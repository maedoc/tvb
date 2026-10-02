# kernel.bend -- the LEAF layer. F32 appears only here, as opaque terms
# whose OPERATOR ORDER is pinned by laws.
#
# The checker never computes a float VALUE (not even 0.0 + 0.0); what the
# laws pin is STRUCTURE: which operation, in which order, on which
# operands. In IEEE-754 that IS the rounding behaviour, so these are
# numerical-fidelity contracts wearing structural costumes.
#
# Reference expressions:
#   * parity_audit.md decision 1 pins the interpolation:
#       tmp = x1 - x0;  val = x0 + alpha * tmp
#     evaluated left-to-right, no FMA, no re-association;
#   * the template's Linear coupling post:
#       wsum = a * wsum + b
#   * the per-target coupling gather is a fold over CSR edges in config
#     order -- float addition is not associative, so EDGE ORDER is part of
#     the observable behaviour.
#
# Composition with the router: routing (router.bend) selects WHICH samples
# a read touches (Line{i0, i1, num, den, win}); this layer turns a
# selected pair into a value:
#     val = blend(hist[i0], hist[i1], float32(num) / float32(den))
# The history itself would be an F32 tree (the bendygrad FTree pattern);
# this file keeps only the pure arithmetic so the laws stay self-contained.
import Base

# the interpolation leaf -- decision 1's pinned expression, term for term
def blend(+x0: F32, +x1: F32, +alpha: F32) -> F32:
  F32.add(x0, F32.mul(alpha, F32.sub(x1, x0)))

# Linear coupling post -- the template's exact term order
def cfun_linear(+a: F32, +b: F32, +wsum: F32) -> F32:
  F32.add(F32.mul(a, wsum), b)

# one weighted edge: w * val, in that order
type Edge is Data:
  Edge{w: F32, val: F32}

def edge_w(+e: Edge) -> F32:
  match e:
    case Edge{w, val}:
      w

def edge_val(+e: Edge) -> F32:
  match e:
    case Edge{w, val}:
      val

# the per-target gather: folds edges in CSR (config) order. The fold's
# shape IS the fidelity contract: reordering edges changes the result in
# the last ulp, and the gather_cons law refuses any silent reordering.
def gather(edges: List<&2, Edge>, +acc: F32) -> F32:
  match edges:
    case Nil{}:
      acc
    case +h <> t:
      gather(t, F32.add(acc, F32.mul(edge_w(h), edge_val(h))))
