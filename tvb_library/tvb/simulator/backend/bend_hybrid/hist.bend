# hist.bend -- the tape: the history's SPEC object for the provenance laws.
#
# DESIGN (see HISTORY_DESIGN.md): Design A is the semantics, Design B (the
# engine's flat ring) a compression tied back by one theorem.  This file is
# the law-layer tape, and it is deliberately the SIMPLEST absolute-index
# structure: a cons list of samples where ELEMENT i IS THE SAMPLE AT
# ABSOLUTE TICK i.  The IC value is supplied at read time and answered for
# reads past the end (the not-yet-written region) -- the same
# default-past-end convention as nats_nth / nth_lane, so the IC law is a
# statement, not an accident.
#
# Representation independence: the runtime object (FTree, flat ring) is
# NOT this list.  Any structure satisfying the four laws below (read-after-
# write, stability, IC region, prune-shift) is the tape for the law layer's
# purposes; the ring correspondence theorem (to come) discharges B against
# these laws directly.
import Base

# the tape's length: the number of samples written so far.  Tick numbers run
# 0 .. len-1; the first write lands at tick 0 (the initial condition
# occupies nothing -- it is the default, not a cell)
def hist_len(xs: List<&2, F32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(1n, hist_len(t))

# read the tape at absolute tick i; ic (the IC fill) is the answer for any
# tick at or past the tape's length -- the not-yet-written region
def hist_read(xs: List<&2, F32>, i: Nat, +ic: F32) -> F32:
  match xs i:
    case Nil{} _:
      ic
    case h <> t 0n:
      h
    case h <> t 1n+p:
      hist_read(t, p, ic)

# append v as the NEXT tick's sample: the tape grows at the far end
def hist_snoc(xs: List<&2, F32>, +v: F32) -> List<&2, F32>:
  match xs:
    case Nil{}:
      v <> Nil{}
    case h <> t:
      h <> hist_snoc(t, v)

# prune: drop the k OLDEST samples (the sliding-window operation).  The
# surviving sample at position i is the original at absolute tick i+k --
# the reindexing is the prune-shift law, and the dropped region is exactly
# what no in-horizon read can name (the pruning corollary)
def hist_drop(xs: List<&2, F32>, k: Nat) -> List<&2, F32>:
  match xs k:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      xs
    case h <> t 1n+q:
      hist_drop(t, q)

# ring_read: Design B's flat slot addressing -- the engine's ring reads
# slot i mod cap of a cap-slot buffer.  The tape is the semantics; the
# ring is a compression of it, and the bridge is the mod fence law
# (mod_lt: i < cap makes the slot address EXACTLY i -- the first lap is
# the tape) plus the prune laws (the live window is the pruned tape).
# The fence is where the deferred div/mod debt gets paid, once, here.
def ring_read(xs: List<&2, F32>, i: Nat, +cap: Nat, +ic: F32) -> F32:
  hist_read(xs, Nat.mod(i, cap), ic)
