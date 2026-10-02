# Proofs for the Bend MontbrioPazoRoxin hybrid prototype.
#
#   bend PROOF.bend            checks the proofs
#   bend PROOF.bend --verdict  re-checks them with the BendTT kernel, which
#                              accepts a def only when it is a valid proof and
#                              relies on no `@unsafe` or foreign code
#
# Each claim in LAWS.bend is closed over concrete values and is either an
# integer equality (which normalises) or a structural identity, so the proof
# term is reflexivity: both sides of the claim reduce to the same term.  The
# def fills the law of the same name -- the type comes from the law, so the
# body is just the proof.
import ./LAWS.bend as Laws

# the drift is the model's expression, term for term
def Laws.drift_is_model_expression_r():
  {==}

def Laws.drift_is_model_expression_v():
  {==}

def Laws.zero_coupling_is_uncoupled():
  {==}

# the fixed point, in structural form
def Laws.drift_fixed_point_r():
  {==}

def Laws.drift_fixed_point_v():
  {==}

# the packed edge word round-trips
def Laws.packed_edge_roundtrip():
  {==}

def Laws.packed_edge_idx():
  {==}

def Laws.packed_edge_delay():
  {==}

# the delayed read
def Laws.ring_zero_delay_first_tick():
  {==}

def Laws.ring_wraps_before_the_start():
  {==}

def Laws.ring_delays_are_offset():
  {==}

def Laws.ring_advances_one_slot_per_tick():
  {==}

def Laws.ring_wraps_around():
  {==}
