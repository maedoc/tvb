# Functional smoke test for sweep.bend: a literal 3-sim parameter table, a
# literal 8-run table, and the fixed 8-wide fan over it.  Pins the fan's
# coverage (n = 3 gathers exactly runs 0..2, n = 8 gathers all 8, n = 0
# gathers nothing), the gate (lane 2 of a 3-sweep runs, lane 5 does not),
# and the row routing (sim 2's parameter IS word 2, through the
# witness-carrying swept_param; the reference read agrees on word 1).
# Expected lines are pinned below (#|); run via tests/run_sweep.sh.
import Base
import ../sweep.bend as S
import ../router.bend as R

def main() -> IO(Unit):
  +runs = {"r0" <> "r1" <> "r2" <> "r3" <> "r4" <> "r5" <> "r6" <> "r7" <> Nil{} : List<&2, String>}
  +tbl = {0.5 <> 1.5 <> 2.5 <> Nil{} : List<&2, F32>}
  +r2 : String = S.fan_lane(3n, 2n, k => S.str_nth(runs, k))
  +r5 : String = S.fan_lane(3n, 5n, k => S.str_nth(runs, k))
  +p2 : Bool = F32.is_eq(S.swept_param(tbl, 2n, R.le_refl(3n)), 2.5)
  +p1 : Bool = F32.is_eq(S.sweep_word(tbl, 1n), 1.5)
  # the connectome sweep (P2): a literal 2-sim payload sweep over a
  # shared 2-edge shape, validated against the good 2-lane config; sim
  # 1's payload routes (its weight head is 0.3, its delay head is 2); a
  # short payload (1 weight on the 2-edge shape) is REJECTED.
  +csok : Bool = S.sweep_csr_ok(0n <> 1n <> 2n <> Nil{}, 0n <> 1n <> Nil{},
                                S.CsrPay{0.1 <> 0.2 <> Nil{}, 0n <> 1n <> Nil{}}
                                  <> S.CsrPay{0.3 <> 0.4 <> Nil{}, 2n <> 0n <> Nil{}}
                                  <> Nil{},
                                R.Config{1n <> 2n <> Nil{},
                                         R.Proj{0n, 1n, 1n, 0n, 0n} <> Nil{}, 4n})
  +w1 : Bool = F32.is_eq(S.sweep_head_or(S.pay_weights(S.pay_nth(
                            S.CsrPay{0.1 <> 0.2 <> Nil{}, 0n <> 1n <> Nil{}}
                              <> S.CsrPay{0.3 <> 0.4 <> Nil{}, 2n <> 0n <> Nil{}}
                              <> Nil{}, 1n)), 0.0), 0.3)
  +d1 : Bool = Nat.is_eq(R.nats_nth(S.pay_delays(S.pay_nth(
                           S.CsrPay{0.1 <> 0.2 <> Nil{}, 0n <> 1n <> Nil{}}
                             <> S.CsrPay{0.3 <> 0.4 <> Nil{}, 2n <> 0n <> Nil{}}
                             <> Nil{}, 1n)), 0n), 2n)
  +csbad : Bool = S.sweep_csr_ok(0n <> 1n <> 2n <> Nil{}, 0n <> 1n <> Nil{},
                                 S.CsrPay{0.1 <> Nil{}, 0n <> 1n <> Nil{}}
                                   <> S.CsrPay{0.3 <> 0.4 <> Nil{}, 2n <> 0n <> Nil{}}
                                   <> Nil{},
                                 R.Config{1n <> 2n <> Nil{},
                                          R.Proj{0n, 1n, 1n, 0n, 0n} <> Nil{}, 4n})
  +out : String = " " ++ S.gather(S.fan8(3n, runs)) ++ "\n"
    ++ " " ++ S.gather(S.fan8(8n, runs)) ++ "\n"
    ++ " " ++ S.gather(S.fan8(0n, runs)) ++ "\n"
    ++ " " ++ r2 ++ "\n"
    ++ " " ++ r5 ++ "\n"
    ++ " " ++ Bool.show(p2) ++ "\n"
    ++ " " ++ Bool.show(p1) ++ "\n"
    ++ " " ++ Bool.show(csok) ++ "\n"
    ++ " " ++ Bool.show(w1) ++ "\n"
    ++ " " ++ Bool.show(d1) ++ "\n"
    ++ " " ++ Bool.show(csbad) ++ "\n"
  do IO<Unit>:
    IO.print(out)

#| r0r1r2
#| r0r1r2r3r4r5r6r7
#| 
#| r2
#| 
#| True
#| True
#| True
#| True
#| True
#| False
