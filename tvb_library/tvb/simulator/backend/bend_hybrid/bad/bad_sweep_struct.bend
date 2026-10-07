# NEGATIVE CONTROL -- this file MUST NOT typecheck.
# The connectome-sweep layer's negative for the SHARED-SHAPE / ROUTING
# pins (LAWS_sweep.bend's P2 family), TWO modes of the claim a missing
# law would let through:
#   (1) bad_sweep_struct_indptr -- two rows with DIFFERENT indptr shapes
#       accepted: "the row CSR built from the DIFFERENT indptr [0,2] IS
#       the row CSR built from the shared indptr [0,1]".  The
#       fixed-node-count constraint is ONE shared indptr for all sims
#       (sweep_csr_shared_indptr pins the routed CSR's indptr to the
#       shared one); this claim asserts the opposite -- the indptr may
#       differ per row and the sweep is still the same connectome.
#   (2) bad_sweep_struct_route -- the per-sim CSR mis-routed to the
#       WRONG sim: "sim 1's payload IS sim 0's payload" on a 2-row table
#       whose rows carry different weights AND delays.  sweep_csr_route
#       pins sim i's payload to ROW i; this claim would let sim 1 run
#       sim 0's connectome silently.
# Expected failure for BOTH: the two sides reduce to DIFFERENT record
# values (different indptr lists in (1), different weights/delays in
# (2)), so {==} cannot close -- the checker reports the mismatch at
# THIS claim, not at an import or a syntax error.
import Base
import ../sweep.bend as S
import ../router.bend as R

def bad_sweep_struct_indptr()
  -> {S.pay_csr(0n <> 2n <> Nil{}, 0n <> 1n <> Nil{},
                S.CsrPay{0.1 <> 0.2 <> Nil{}, 0n <> 1n <> Nil{}})
        == S.pay_csr(0n <> 1n <> 2n <> Nil{}, 0n <> 1n <> Nil{},
                     S.CsrPay{0.1 <> 0.2 <> Nil{}, 0n <> 1n <> Nil{}})
      : R.Csr}:
  {==}

def bad_sweep_struct_route()
  -> {S.pay_nth(S.CsrPay{0.1 <> 0.2 <> Nil{}, 0n <> 1n <> Nil{}}
                  <> S.CsrPay{0.3 <> 0.4 <> Nil{}, 2n <> 0n <> Nil{}}
                  <> Nil{},
                1n)
        == S.CsrPay{0.1 <> 0.2 <> Nil{}, 0n <> 1n <> Nil{}} : S.CsrPay}:
  {==}
