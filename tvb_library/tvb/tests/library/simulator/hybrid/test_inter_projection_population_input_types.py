# -*- coding: utf-8 -*-
#
#
# TheVirtualBrain-Scientific Package. This package holds all simulators, and
# analysers necessary to run brain-simulations. You can use it stand alone or
# in conjunction with TheVirtualBrain-Framework Package. See content of the
# documentation-folder for more details. See also http://www.thevirtualbrain.org
#
# (c) 2012-2025, Baycrest Centre for Geriatric Care ("Baycrest") and others
#
# This program is free software: you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation, either version 3 of the License, or (at your option) any later
# version. This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details. You should have received a copy of the GNU General Public
# License along with this program.  If not, see
# <http://www.gnu.org/licenses/>.
#
#
#   CITATION:
# When using The Virtual Brain for scientific publications, please cite it as
# explained here:
# https://www.thevirtualbrain.org/tvb/zwei/neuroscience-publications
#
#

"""
Pedagogical tests: how to indicate in an ``InterProjection`` BOTH

  (a) the **target population** (e.g. E vs I cells of the target region), and
  (b) the **type of input** (excitatory vs inhibitory),

which is what is needed when integrating multi-population models (e.g. basal
ganglia) into the hybrid simulator.

The question
------------
In the classic simulator ``cv_target``/``cvar`` has one entry per target
population (e.g. 2 for E and I), so a projection can say *which* population it
targets but not *what kind of input* it delivers (we would need an array of
dimension 4 = 2 populations x 2 input types).  Redefining ``cvar`` in the model
with all local variables x input types works for the target side, but seems to
break the source side (``cvar_source`` should only span the state variables,
e.g. shape 2 for E/I).

The answer implemented here
---------------------------
``source_cvar`` and ``target_cvar`` live in **two different index spaces**
(see ``tvb/simulator/hybrid/cvar_utils.py``):

* ``source_cvar`` indexes **state variables** of the *source* model.  It is
  resolved by ``resolve_source_cvar`` to ``model.cvar[slot]`` (a state-variable
  index) and validated against ``model.nvar`` by ``validate_cvar_indices``.
  It reads from the projection history buffer of shape
  ``(nvar, nnodes, modes, horizon)`` (``base_projection.py:configure_buffer``).

* ``target_cvar`` indexes **coupling slots** of the *target* model.  It is
  resolved by ``resolve_target_cvar`` to the slot position in ``model.cvar``
  and validated against ``len(model.cvar)`` by ``validate_target_cvar_indices``.
  It writes into the target coupling array of shape
  ``(len(model.cvar), nnodes, modes)`` (``subnetwork.py:Subnetwork.zero_cvars``),
  which the target model's ``dfun`` receives as ``coupling[slot]``.

Hence a target model may declare an *extended* ``cvar`` of length
``n_populations x n_input_types`` (here 4: E-exc, E-inh, I-exc, I-inh) and each
inter-projection picks the slot(s) it wants via ``target_cvar`` -- while the
source side keeps its own small ``cvar`` (here a single output ``x``) and
``source_cvar`` never needs the 4-dim shape.  No separate "input cvar" /
"output cvar" model attribute is required: ``model.cvar`` plays the input-slot
role on the target side, and the full state history plays the output role on
the source side.

Two equivalent recipes are demonstrated below:

* **Recipe A (extended target ``cvar``, dim = populations x input types):**
  the input *type* is encoded in the target slot; the model's ``dfun`` applies
  the sign (``+coupling[0] - coupling[1]`` for the E population, etc.).
  Use this when the same target population can receive both excitatory and
  inhibitory afferents that must be distinguished in the dynamics.

* **Recipe B (plain ``cvar`` of dim = populations, type carried by the
  projection):** one projection with ``target_cvar=[E_slot, I_slot]`` and
  ``target_scales=[+w, -w]`` (per-slot gains, ``base_projection.py``) or a
  negative ``scale``/coupling gain.  Use this when the input type is a
  property of the *source* projection, not of the target.
"""

import numpy as np
import scipy.sparse as sp
import pytest

from tvb.basic.neotraits.api import Final, List
from tvb.simulator.models.base import Model
from tvb.simulator.models import Linear  # 1 state variable 'x', cvar=[0]: our "source region"
from tvb.simulator.integrators import HeunDeterministic
from tvb.simulator.hybrid import Subnetwork, NetworkSet, InterProjection
from tvb.simulator.hybrid.cvar_utils import (
    resolve_source_cvar,
    resolve_target_cvar,
    validate_cvar_indices,
    validate_target_cvar_indices,
)


class ToyEIPopulation(Model):
    """Toy target region with two populations (E, I) and FOUR input slots.

    ``cvar`` has one entry per (population, input type) pair -- the "dim-4
    cvar_target" discussed in the email.  Entries may repeat state-variable
    indices (here both E slots point at state variable ``E`` = index 0);
    repeated entries are explicitly supported by ``resolve_cvar_names``
    ("for more cvars than svars").

    Slot convention (decided by this model, consumed by ``dfun``):

    * slot 0: excitatory input onto the E population
    * slot 1: inhibitory input onto the E population
    * slot 2: excitatory input onto the I population
    * slot 3: inhibitory input onto the I population

    Note: because ``cvar`` repeats the state-variable indices, string names
    resolve to the *first* matching slot (``resolve_target_cvar('E') == 0``);
    with such an extended cvar, address slots by integer index, as done below.
    """

    state_variables = ('E', 'I')
    _nvar = 2
    # 4 coupling slots: (E-exc, E-inh, I-exc, I-inh), pointing at state vars (E, E, I, I)
    cvar = np.array([0, 0, 1, 1], dtype=np.int32)

    variables_of_interest = List(of=str, choices=("E", "I"), default=("E", "I"))
    state_variable_range = Final(
        default={"E": np.array([0.0, 1.0]), "I": np.array([0.0, 1.0])},
    )
    # Names of the coupling array entries, one per cvar slot (used by the numba
    # codegen to unpack ``coupling[k]``; kept in sync with ``cvar``).
    coupling_terms = Final(default=["cE_exc", "cE_inh", "cI_exc", "cI_inh"])

    def dfun(self, state_variables, coupling, local_coupling=0.0):
        """dE = -E + (exc input) - (inh input);  dI = -I + (exc) - (inh).

        The sign of each input channel is applied HERE, in the model, according
        to which cvar slot the projection wrote into.
        """
        E, I = state_variables
        dE = -E + coupling[0] - coupling[1]
        dI = -I + coupling[2] - coupling[3]
        return np.array([dE, dI])


class ToyEIPopulationPlain(Model):
    """Same two populations, but ``cvar`` of dim 2 (one slot per population).

    Used for Recipe B: the coupling array has shape (2, nnodes, modes) with
    slot 0 = input onto E, slot 1 = input onto I, exactly like WilsonCowan's
    ``cvar=[0, 1]``.  The input *type* (exc/inh) is then carried by the
    projection's ``target_scales``/``scale`` sign instead of by a dedicated
    slot.
    """

    state_variables = ('E', 'I')
    _nvar = 2
    cvar = np.array([0, 1], dtype=np.int32)

    variables_of_interest = List(of=str, choices=("E", "I"), default=("E", "I"))
    state_variable_range = Final(
        default={"E": np.array([0.0, 1.0]), "I": np.array([0.0, 1.0])},
    )
    coupling_terms = Final(default=["cE", "cI"])

    def dfun(self, state_variables, coupling, local_coupling=0.0):
        E, I = state_variables
        dE = -E + coupling[0]
        dI = -I + coupling[1]
        return np.array([dE, dI])


def _make_subnets(target_model, n_src=2, n_tgt=3):
    """Build a configured (source, target) subnetwork pair.

    The source is a ``Linear`` model (single state variable ``x``, ``cvar=[0]``)
    playing the role of an afferent region with ONE output; the target uses
    *target_model* (the toy E/I region).
    """
    scheme = HeunDeterministic(dt=0.1)
    src = Subnetwork(
        name="src", model=Linear(), scheme=scheme, nnodes=n_src
    ).configure()
    tgt = Subnetwork(
        name="tgt", model=target_model, scheme=scheme, nnodes=n_tgt
    ).configure()
    return src, tgt


def _ones_weights(n_tgt, n_src):
    """All-to-all weights of 1.0 (every source node excites every target node)."""
    return sp.csr_matrix(np.ones((n_tgt, n_src)))


class TestExtendedTargetCvar:
    """Recipe A: target model declares one cvar slot per (population, input type)."""

    def test_target_model_declares_four_input_slots(self):
        """The coupling array of the target has shape (4, nnodes, modes).

        ``Subnetwork.zero_cvars`` allocates ``(model.cvar.size, ...)`` slots, so
        with ``cvar = [0, 0, 1, 1]`` the target coupling array has 4 slots:
        0=E-exc, 1=E-inh, 2=I-exc, 3=I-inh.  This is the "dim-4 cv_target".
        """
        _, tgt = _make_subnets(ToyEIPopulation())
        assert tgt.model.cvar.size == 4
        c = tgt.zero_cvars()
        assert c.shape == (4, tgt.nnodes, tgt.model.number_of_modes)
        # All four slots are valid target_cvar indices ...
        validate_target_cvar_indices(tgt.model, np.array([0, 1, 2, 3]))
        # ... but slot 4 does not exist (only 2 populations x 2 input types).
        with pytest.raises(ValueError, match="Invalid target cvar indices"):
            validate_target_cvar_indices(tgt.model, np.array([4]))

    def test_source_cvar_stays_in_state_variable_space(self):
        """The source side never needs the 4-dim shape -- this is the key point.

        ``resolve_source_cvar`` returns STATE-VARIABLE indices (bounded by
        ``model.nvar``), while ``resolve_target_cvar`` returns COUPLING-SLOT
        indices (bounded by ``len(model.cvar)``).  On the 4-slot target model
        used as a source, 'E' resolves to state variable 0 (not to a slot):
        """
        _, tgt = _make_subnets(ToyEIPopulation())
        # source-side resolution on the target model: state-var index, < nvar = 2
        np.testing.assert_array_equal(resolve_source_cvar(tgt.model, "E"), [0])
        np.testing.assert_array_equal(resolve_source_cvar(tgt.model, "I"), [1])
        validate_cvar_indices(tgt.model, resolve_source_cvar(tgt.model, ["E", "I"]))
        # target-side resolution: slot indices, < len(cvar) = 4
        assert resolve_target_cvar(tgt.model, np.array([0, 1, 2, 3])).max() == 3
        # and on the plain source model (Linear, nvar=1) source_cvar='x' -> [0]
        src, _ = _make_subnets(ToyEIPopulation())
        np.testing.assert_array_equal(resolve_source_cvar(src.model, "x"), [0])
        validate_cvar_indices(src.model, np.array([0]))
        with pytest.raises(ValueError, match="Invalid cvar indices"):
            validate_cvar_indices(src.model, np.array([1]))  # nvar=1: no index 1

    def test_projection_to_inhibitory_input_of_excitatory_population(self):
        """The email's example: target E cells with an INHIBITORY input.

        ``target_cvar=[1]`` selects the "inhibitory channel of E" slot; the
        projection writes there and nowhere else.  ``source_cvar=[0]`` reads
        the source's single state variable.  The two arrays have unrelated
        lengths (1 vs 1 here, but could be e.g. 1 vs 4) -- they index different
        arrays (history buffer vs coupling array).
        """
        src, tgt = _make_subnets(ToyEIPopulation())
        W = _ones_weights(tgt.nnodes, src.nnodes)
        proj = InterProjection(
            source=src, target=tgt,
            source_cvar=[0],        # source state variable 'x' (index 0)
            target_cvar=[1],        # target slot 1 = inhibitory input onto E
            weights=W, lengths=sp.csr_matrix(W.shape), cv=3.0, dt=0.1, scale=2.0,
        )
        proj.configure()
        # Put a known constant source state into the history buffer.
        state = np.zeros((src.model.nvar, src.nnodes, src.model.number_of_modes))
        state[0] = 3.0
        for t in range(proj._horizon + 2):
            proj.update_buffer(state, t)
        # Apply at a step where the delayed read sees our state.
        tgt_c = tgt.zero_cvars()
        proj.apply(tgt_c, proj._horizon + 1)
        # Each target node receives scale * sum_j W_ij * x_j = 2.0 * (3+3) = 12
        # on slot 1 ONLY; slots 0, 2, 3 (E-exc, I-exc, I-inh) stay zero.
        np.testing.assert_allclose(tgt_c[1], 12.0)
        assert np.all(tgt_c[0] == 0) and np.all(tgt_c[2] == 0) and np.all(tgt_c[3] == 0)

    def test_one_projection_can_feed_several_slots_with_per_slot_scales(self):
        """One source, one projection, several (population, type) targets.

        ``target_cvar=[0, 3]`` with ``target_scales=[1.0, 1.0]`` delivers the
        same afferent signal to the E-exc slot and to the I-inh slot; the
        model's ``dfun`` then applies +slot0 to E and -slot3 to I.  This is
        the basal-ganglia pattern "one source excites E and inhibits I".
        """
        src, tgt = _make_subnets(ToyEIPopulation())
        W = _ones_weights(tgt.nnodes, src.nnodes)
        proj = InterProjection(
            source=src, target=tgt,
            source_cvar=[0],
            target_cvar=[0, 3],            # E-exc and I-inh slots
            target_scales=np.array([1.0, 1.0]),
            weights=W, lengths=sp.csr_matrix(W.shape), cv=3.0, dt=0.1, scale=0.5,
        )
        proj.configure()
        state = np.zeros((src.model.nvar, src.nnodes, src.model.number_of_modes))
        state[0] = 2.0
        for t in range(proj._horizon + 2):
            proj.update_buffer(state, t)
        tgt_c = tgt.zero_cvars()
        proj.apply(tgt_c, proj._horizon + 1)
        # per-node signal = scale * sum_j W x_j = 0.5 * (2+2) = 2.0 on slots 0 and 3
        np.testing.assert_allclose(tgt_c[0], 2.0)
        np.testing.assert_allclose(tgt_c[3], 2.0)
        assert np.all(tgt_c[1] == 0) and np.all(tgt_c[2] == 0)

    def test_end_to_end_step_applies_input_type_sign(self):
        """Full loop through ``NetworkSet``: projection -> slot -> dfun sign.

        With a constant positive source activity:
        * projecting to slot 0 (E-exc) makes E INCREASE,
        * projecting to slot 1 (E-inh) makes E DECREASE,
        while the I population stays at zero because slots 2 and 3 are untouched.
        """
        def run(target_slot):
            src, tgt = _make_subnets(ToyEIPopulation())
            W = _ones_weights(tgt.nnodes, src.nnodes)
            proj = InterProjection(
                source=src, target=tgt,
                source_cvar=[0], target_cvar=[target_slot],
                weights=W, lengths=sp.csr_matrix(W.shape), cv=3.0, dt=0.1, scale=1.0,
            )
            nets = NetworkSet(subnets=[src, tgt], projections=[proj]).configure()
            xs = nets.zero_states()
            xs.src[0, :, :] = 1.0  # constant positive source activity
            nets.init_projection_buffers(xs)
            for step in range(1, 6):
                xs = nets.step(step, xs)
            return xs

        xs_exc = run(target_slot=0)   # excitatory input onto E
        xs_inh = run(target_slot=1)   # inhibitory input onto E
        assert np.all(xs_exc.tgt[0] > 0), "E must be excited via slot 0"
        assert np.all(xs_inh.tgt[0] < 0), "E must be inhibited via slot 1"
        # I population received nothing (slots 2, 3 untouched): stays at 0
        assert np.all(xs_exc.tgt[1] == 0) and np.all(xs_inh.tgt[1] == 0)


class TestProjectionSignRecipe:
    """Recipe B: plain dim-2 ``cvar`` (one slot per population) + projection sign.

    Equivalent to Recipe A when the input type is a property of the source:
    one projection with ``target_cvar=[E_slot, I_slot]`` and
    ``target_scales=[+w, -w]`` excites E and inhibits I.
    """

    def test_target_scales_carry_the_input_type_sign(self):
        """target_cvar=[0, 1], target_scales=[+w, -w] on a 2-slot target model."""
        src, tgt = _make_subnets(ToyEIPopulationPlain())
        assert tgt.model.cvar.size == 2  # one slot per population, like WilsonCowan
        W = _ones_weights(tgt.nnodes, src.nnodes)
        w = 0.25
        proj = InterProjection(
            source=src, target=tgt,
            source_cvar=[0],
            target_cvar=[0, 1],                    # E slot and I slot
            target_scales=np.array([w, -w]),       # +w excites E, -w inhibits I
            weights=W, lengths=sp.csr_matrix(W.shape), cv=3.0, dt=0.1, scale=1.0,
        )
        proj.configure()
        state = np.zeros((src.model.nvar, src.nnodes, src.model.number_of_modes))
        state[0] = 2.0
        for t in range(proj._horizon + 2):
            proj.update_buffer(state, t)
        tgt_c = tgt.zero_cvars()
        proj.apply(tgt_c, proj._horizon + 1)
        # raw signal per node = sum_j W x_j = 4.0; slot 0 gets +w*4, slot 1 gets -w*4
        np.testing.assert_allclose(tgt_c[0], w * 4.0)
        np.testing.assert_allclose(tgt_c[1], -w * 4.0)

    def test_out_of_range_target_slot_is_rejected(self):
        """``target_cvar`` is bounded by ``len(model.cvar)``, not by ``nvar``."""
        src, tgt = _make_subnets(ToyEIPopulationPlain())  # nvar=2, len(cvar)=2
        W = _ones_weights(tgt.nnodes, src.nnodes)
        # slot 2 would be valid for the 4-slot model but NOT here:
        proj = InterProjection(
            source=src, target=tgt,
            source_cvar=[0], target_cvar=[2],
            weights=W, lengths=sp.csr_matrix(W.shape), cv=3.0, dt=0.1,
        )
        proj.configure()
        state = np.zeros((src.model.nvar, src.nnodes, src.model.number_of_modes))
        proj.update_buffer(state, 0)
        with pytest.raises(ValueError, match="Invalid target cvar indices"):
            proj.apply(tgt.zero_cvars(), 1)
