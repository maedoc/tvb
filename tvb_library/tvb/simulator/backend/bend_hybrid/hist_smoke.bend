import Base
import ./hist.bend as H

# the tape: ticks 0,1,2 carry 1.5, 2.5, 3.5
def build_tape() -> List<&2, F32>:
  H.hist_snoc(H.hist_snoc(H.hist_snoc(Nil{}, 1.5), 2.5), 3.5)

def probe0(t: List<&2, F32>) -> Bool:
  F32.is_eq(H.hist_read(t, 0n, 0.0), 1.5)

def probe2(t: List<&2, F32>) -> Bool:
  F32.is_eq(H.hist_read(t, 2n, 0.0), 3.5)

# past the end: IC
def probe_ic(t: List<&2, F32>) -> Bool:
  F32.is_eq(H.hist_read(t, 5n, 9.0), 9.0)

# stability: appending 4.5 leaves tick 1 alone
def probe_stable(t: List<&2, F32>) -> Bool:
  F32.is_eq(H.hist_read(H.hist_snoc(t, 4.5), 1n, 0.0), 2.5)

# prune: dropping the 2 oldest reindexes tick 2 -> position 0
def probe_prune(t: List<&2, F32>) -> Bool:
  F32.is_eq(H.hist_read(H.hist_drop(t, 2n), 0n, 0.0), 3.5)

def verdict(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool) -> String:
  match a b c d e:
    case True{} True{} True{} True{} True{}:
      "tape smoke ok"
    case _ _ _ _ _:
      "tape smoke FAIL"

def main() -> String:
  verdict(probe0(build_tape()),
          probe2(build_tape()),
          probe_ic(build_tape()),
          probe_stable(build_tape()),
          probe_prune(build_tape()))
