# MontbrioPazoRoxin sweep CLI.
#
# Usage:
#   JOB_SWEEP=... JOB_ICR=... ... montbrio_sweep <hdr0> <hdr1> ... <idx0> <del0>
#
# argv carries the job header as raw u32 words (floats are pre-scaled by 1e6,
# because Bend has no float bit-reinterpretation -- `F32.to_u32` is a numeric
# truncation, not a bit cast -- and `U32.read` is the cheapest exact parser).
# The eight section files are named by environment variable rather than argv:
# a `List<String>` is a single-owner `Type` and cannot be copied for repeated
# indexing, while `IO.get_env` hands back a `String`, which is `Data`.
#
# Each section lives in its own file because `File.read_bytes` returns a byte
# list, and an `Array` decoded from it is single-owner: exactly one consumer
# per file.
import ./mcore.bend as Core
import ./mengine.bend as Eng

type Job is Data:
  Jb{n_nodes: U32, n_step: U32, n_sweep: U32,
     sdepth: Nat, hdepth: Nat, tdepth: Nat, hslots: U32,
     nnz: U32, wdepth: Nat, scale: F32,
     dt: F32, tau: F32, delta: F32, eta: F32, jj: F32, ii: F32,
     ccr: F32, ccv: F32, cfa: F32, cfb: F32}

type Paths is Data:
  Ps{sweep: String, icr: String, icv: String, histr: String, histv: String,
      edge: String, tgt: String, w: String}

type Out is Data:
  O{r: String, v: String}



# --------------------------------------------------------------------------
# job file -> words
# --------------------------------------------------------------------------

def bytes_of(pb: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  match pb:
    case (f, r):
      IO.pass(List<&2, U32>, r)
def load_bytes(path: String) -> IO(List<&2, U32>):
  IO.bind(File, List<&2, U32>,
          IO.try(File, File.open(path, "r")),
          f => IO.bind(File & Result<&1, &1, U32 & String, List<&2, U32>>,
                       List<&2, U32>, File.read_bytes(f, 67108864), bytes_of))

# Pack the byte stream into little-endian u32 words.  A flat multi-cons
# pattern consumes four cells in one step, which keeps this a SINGLE def
# (a shift-counter accumulator would have needed a helper that calls back into
# the loop, i.e. the mutual recursion Bend forbids).
def words_loop(+fuel: Nat, bs: List<&2, U32>, +widx: U32,
               w: Array<U32>) -> Array<U32>:
  match fuel bs:
    case 1n+p b0 <> b1 <> b2 <> b3 <> t:
      +wrd : U32 = U32.or(U32.or(b0, U32.shln(b1, 8n)),
                          U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))
      words_loop(p, t, U32.add(widx, 1), Array.set(U32, w, widx, wrd))
    case _ Nil{}:
      w
    case _ _:
      w
def to_words(bs: List<&2, U32>, +nbytes: Nat, +depth: Nat) -> Array<U32>:
  words_loop(nbytes, bs, 0, Array.new(U32, depth, 0))

# --------------------------------------------------------------------------
# job header
# --------------------------------------------------------------------------

def nth(xs: List<&2, U32>, k: Nat) -> U32:
  # several values are matched together with `match a b:`, in binder order;
  # a def may not `match` twice
  match xs k:
    case h <> t 0n:
      h
    case h <> t 1n+p:
      nth(t, p)
    case Nil{} 0n:
      0
    case Nil{} 1n+p:
      0
def parse_one(xs: List<String>, acc: List<&2, U32>) -> List<&2, U32>:
  # Maybe.default unwraps without a `match`, which keeps this a single def: a
  # helper that read the value and recursed would be mutual recursion.
  match xs:
    case Nil{}:
      acc
    case h <> t:
      parse_one(t, Maybe.default(&2, U32, U32.read(h), 0) <> acc)
def j_nnodes(+j: Job) -> U32:
  match j:
    case Jb{n_nodes, n_step, n_sweep, sdepth, hdepth, tdepth, hslots, nnz,
            wdepth, scale, dt, tau, delta, eta, jj, ii, ccr, ccv, cfa, cfb}: n_nodes
def j_nstep(+j: Job) -> U32:
  match j:
    case Jb{n_nodes, n_step, n_sweep, sdepth, hdepth, tdepth, hslots, nnz,
            wdepth, scale, dt, tau, delta, eta, jj, ii, ccr, ccv, cfa, cfb}: n_step
def j_nsweep(+j: Job) -> U32:
  match j:
    case Jb{n_nodes, n_step, n_sweep, sdepth, hdepth, tdepth, hslots, nnz,
            wdepth, scale, dt, tau, delta, eta, jj, ii, ccr, ccv, cfa, cfb}: n_sweep
def j_sdepth(+j: Job) -> Nat:
  match j:
    case Jb{n_nodes, n_step, n_sweep, sdepth, hdepth, tdepth, hslots, nnz,
            wdepth, scale, dt, tau, delta, eta, jj, ii, ccr, ccv, cfa, cfb}: sdepth
def j_hdepth(+j: Job) -> Nat:
  match j:
    case Jb{n_nodes, n_step, n_sweep, sdepth, hdepth, tdepth, hslots, nnz,
            wdepth, scale, dt, tau, delta, eta, jj, ii, ccr, ccv, cfa, cfb}: hdepth
def j_tdepth(+j: Job) -> Nat:
  match j:
    case Jb{n_nodes, n_step, n_sweep, sdepth, hdepth, tdepth, hslots, nnz,
            wdepth, scale, dt, tau, delta, eta, jj, ii, ccr, ccv, cfa, cfb}: tdepth
def j_hslots(+j: Job) -> U32:
  match j:
    case Jb{n_nodes, n_step, n_sweep, sdepth, hdepth, tdepth, hslots, nnz,
            wdepth, scale, dt, tau, delta, eta, jj, ii, ccr, ccv, cfa, cfb}: hslots
def j_nnz(+j: Job) -> U32:
  match j:
    case Jb{n_nodes, n_step, n_sweep, sdepth, hdepth, tdepth, hslots, nnz,
            wdepth, scale, dt, tau, delta, eta, jj, ii, ccr, ccv, cfa, cfb}: nnz
def j_wdepth(+j: Job) -> Nat:
  match j:
    case Jb{n_nodes, n_step, n_sweep, sdepth, hdepth, tdepth, hslots, nnz,
            wdepth, scale, dt, tau, delta, eta, jj, ii, ccr, ccv, cfa, cfb}: wdepth
def j_scale(+j: Job) -> F32:
  # the fixed-point DIVISOR every scaled float is decoded against; argv word 9
  # carries it so Python owns the choice, but it must not itself be decoded
  1000000.0
def j_cfa(+j: Job) -> F32:
  match j:
    case Jb{n_nodes, n_step, n_sweep, sdepth, hdepth, tdepth, hslots, nnz,
            wdepth, scale, dt, tau, delta, eta, jj, ii, ccr, ccv, cfa, cfb}: cfa
def j_cfb(+j: Job) -> F32:
  match j:
    case Jb{n_nodes, n_step, n_sweep, sdepth, hdepth, tdepth, hslots, nnz,
            wdepth, scale, dt, tau, delta, eta, jj, ii, ccr, ccv, cfa, cfb}: cfb
def j_cfg(+j: Job) -> Core.Cfg:
  match j:
    case Jb{n_nodes, n_step, n_sweep, sdepth, hdepth, tdepth, hslots, nnz,
            wdepth, scale, dt, tau, delta, eta, jj, ii, ccr, ccv, cfa, cfb}: Core.C{dt, tau, delta, eta, jj, ii, ccr, ccv}

# offsets of the bulk sections inside the words file (floats are scaled by
# `scale`, which the caller already applied when writing them)
def o_icr(+j: Job) -> U32:
  U32.add(j_nsweep(j), 0)
def o_icv(+j: Job) -> U32:
  U32.add(o_icr(j), j_nnodes(j))
def o_histr(+j: Job) -> U32:
  U32.add(o_icv(j), j_nnodes(j))
def o_histv(+j: Job) -> U32:
  U32.add(o_histr(j), U32.mul(j_nnodes(j), j_hslots(j)))
def o_edge(+j: Job) -> U32:
  U32.add(o_histv(j), U32.mul(j_nnodes(j), j_hslots(j)))
def o_tgt(+j: Job) -> U32:
  U32.add(o_edge(j), U32.add(j_nnz(j), 1))
def o_w(+j: Job) -> U32:
  U32.add(o_tgt(j), U32.add(j_nnz(j), 1))
def dec_scaled(+hdr: List<&2, U32>, +k: Nat) -> F32:
  Core.dec_f32(nth(hdr, k), 1000000.0)

def make_job(+hdr: List<&2, U32>) -> Job:
  +sc : F32 = Core.dec_f32(nth(hdr, 9n), 1000000.0)
  Jb{nth(hdr, 0n), nth(hdr, 1n), nth(hdr, 2n),
     U32.to_nat(nth(hdr, 3n)), U32.to_nat(nth(hdr, 4n)), U32.to_nat(nth(hdr, 5n)),
     nth(hdr, 6n), nth(hdr, 7n), U32.to_nat(nth(hdr, 8n)), sc,
     dec_scaled(hdr, 10n), dec_scaled(hdr, 11n), dec_scaled(hdr, 12n),
     dec_scaled(hdr, 13n), dec_scaled(hdr, 14n), dec_scaled(hdr, 15n),
     dec_scaled(hdr, 16n), dec_scaled(hdr, 17n),
     dec_scaled(hdr, 18n), dec_scaled(hdr, 19n)}
# parse_one conses onto an accumulator, so its result is reversed; one pass
# puts the header words back in argv order
def rev(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      rev(t, h <> acc)

def drop1(xs: List<String>) -> List<String>:
  match xs:
    case h <> t:
      t
    case Nil{}:
      Nil{}

# Each sweep point is a forked task that prints its own block, prefixed with
# the point index so the (order-independent) output can be reassembled.  The
# program ends only when every computation is done, so no join list is needed
# -- which also avoids `List<Chan<String>>`, whose `>>` the parser reads as a
# shift operator (and `Chan` cannot appear in a user datatype anyway).

# --------------------------------------------------------------------------
# bulk sections and trace output
# --------------------------------------------------------------------------

def fill_u32(+fuel: Nat, +i: U32, src: (Array<U32> & U32), +base: U32,
             dst: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      dst
    case 1n+f:
      match src:
        case (s1, v):
          fill_u32(f, U32.add(i, 1), Array.get(U32, s1, U32.add(base, U32.add(i, 1))),
                   base, Array.set(U32, dst, i, v))
def fill_f32(+fuel: Nat, +i: U32, src: (Array<U32> & U32), +base: U32,
             dst: Array<F32>, +scale: F32) -> Array<F32>:
  match fuel:
    case 0n:
      dst
    case 1n+f:
      match src:
        case (s1, v):
          fill_f32(f, U32.add(i, 1), Array.get(U32, s1, U32.add(base, U32.add(i, 1))),
                   base, Array.set(F32, dst, i, Core.dec_f32(v, scale)),
                   scale)
def word_of(p: (Array<U32> & U32)) -> U32:
  match p:
    case (a, v):
      v

# The trace holds r and V interleaved (2*(t-1) and 2*(t-1)+1).  ONE def walks
# it and accumulates both series into a record built in the base case: the list
# is affine (`Array.to_list` yields List<&1, F32>) so it cannot be traversed
# twice, and a value returned by a call cannot be destructured -- hence the
# `Out` record, which `fmt` matches as a parameter.
def fmt(o: Out) -> String:
  match o:
    case O{r, v}:
      "R " ++ r ++ "\nV " ++ v ++ " \n"
def scaled_abs(+s: F32, +neg: Bool) -> F32:
  Bool.pick(F32, neg, F32.neg(s), s)

def fscaled(+x: F32) -> String:
  # round(x * 1e6) as a decimal integer, sign handled explicitly because
  # F32.to_nat truncates toward zero
  +scaled : F32 = F32.mul(x, 1000000.0)
  +neg : Bool = F32.is_lt(x, 0.0)
  +mag : Nat = F32.to_nat(F32.add(scaled_abs(scaled, neg), 0.5))
  Bool.pick(String, neg, "-" ++ Nat.show(mag), Nat.show(mag))

def emit_both(lim: Nat, xs: List<F32>, +i: U32, +ar: String, +av: String) -> Out:
  # `lim` bounds the walk to 2*nstep entries: the trace array is a power of two
  # and its tail is never written
  match lim xs:
    case 0n Nil{}:
      O{ar, av}
    case 0n _:
      O{ar, av}
    case 1n+p Nil{}:
      O{ar, av}
    case 1n+p +h <> t:
      +even : Bool = U32.is_eq(U32.mod(i, 2), 0)
      emit_both(p, t, U32.add(i, 1),
                Bool.pick(String, even, ar ++ fscaled(h) ++ " ", ar),
                Bool.pick(String, even, av, av ++ fscaled(h) ++ " "))
# the trace array, printed as the two space-separated series

def p_sweep(p: Paths) -> String:
  match p:
    case Ps{sweep, icr, icv, histr, histv, edge, tgt, w}: sweep
def p_icr(p: Paths) -> String:
  match p:
    case Ps{sweep, icr, icv, histr, histv, edge, tgt, w}: icr
def p_icv(p: Paths) -> String:
  match p:
    case Ps{sweep, icr, icv, histr, histv, edge, tgt, w}: icv
def p_histr(p: Paths) -> String:
  match p:
    case Ps{sweep, icr, icv, histr, histv, edge, tgt, w}: histr
def p_histv(p: Paths) -> String:
  match p:
    case Ps{sweep, icr, icv, histr, histv, edge, tgt, w}: histv
def p_edge(p: Paths) -> String:
  match p:
    case Ps{sweep, icr, icv, histr, histv, edge, tgt, w}: edge
def p_tgt(p: Paths) -> String:
  match p:
    case Ps{sweep, icr, icv, histr, histv, edge, tgt, w}: tgt
def p_w(p: Paths) -> String:
  match p:
    case Ps{sweep, icr, icv, histr, histv, edge, tgt, w}: w

# --------------------------------------------------------------------------
# The sweep, as data-parallel work.
#
# IO.spawn does NOT fan pure work out across cores -- measured: 1 point 206 ms,
# 2 points 432 ms, 8 points 1412 ms, i.e. exactly serial.  Bend's real
# parallelism is the parallel LET (`a b = f(x) g(x)`), which forks two calls at
# once.  So the bulk is loaded ONCE (every section is a reusable byte List),
# and the sweep points are run with nested parallel lets, two levels deep, for
# 8 points on 8 cores.
#
# Each point builds its own Arrays from the shared byte lists, which it must:
# an Array is a single-owner Type and cannot be shared across concurrent
# branches, but a List is Data and copies for free.
# --------------------------------------------------------------------------

type In is Data:
  Inn{j: Job, i0: U32, d0: U32,
      be: List<&2, U32>, bt: List<&2, U32>, bw: List<&2, U32>,
      bir: List<&2, U32>, biv: List<&2, U32>,
      bhr: List<&2, U32>, bhv: List<&2, U32>, bsw: List<&2, U32>}








def trace_of(tr: Array<F32>, +nstep: U32) -> String:
  fmt(emit_both(U32.to_nat(U32.mul(nstep, 2)),
                Array.to_list(F32, tr), 0, "", ""))

def point_body(k: U32, sim: Eng.Sim, +nstep: U32) -> String:
  match sim:
    case Eng.Sim{edge, tgt, w, hr, hv, r, v, cr, cv, tr, t, nnz, n_nodes,
                 hslots, tmask, cfa, cfb, scale, c}:
      "POINT " ++ U32.show(k) ++ " scale " ++ fscaled(scale) ++ "\n"
        ++ trace_of(tr, nstep)

def build_and_run(+k: U32, +idx0: U32, +del0: U32, +j: Job,
                  be: List<&2, U32>, bt: List<&2, U32>, bw: List<&2, U32>,
                  bir: List<&2, U32>, biv: List<&2, U32>,
                  bhr: List<&2, U32>, bhv: List<&2, U32>,
                  bsw: List<&2, U32>) -> String:
  +sc : F32 = j_scale(j)
  +nn : U32 = j_nnodes(j)
  +ne : U32 = U32.add(j_nnz(j), 1)
  +nhist : U32 = U32.mul(nn, j_hslots(j))
  +tmask : U32 = U32.sub(j_hslots(j), 1)
  ew : Array<U32> = to_words(be, U32.to_nat(U32.mul(ne, 4)), j_wdepth(j))
  tw : Array<U32> = to_words(bt, U32.to_nat(U32.mul(ne, 4)), j_wdepth(j))
  ww : Array<U32> = to_words(bw, U32.to_nat(U32.mul(ne, 4)), j_wdepth(j))
  irw : Array<U32> = to_words(bir, U32.to_nat(U32.mul(nn, 4)), j_wdepth(j))
  ivw : Array<U32> = to_words(biv, U32.to_nat(U32.mul(nn, 4)), j_wdepth(j))
  hrw : Array<U32> = to_words(bhr, U32.to_nat(U32.mul(nhist, 4)), j_hdepth(j))
  hvw : Array<U32> = to_words(bhv, U32.to_nat(U32.mul(nhist, 4)), j_hdepth(j))
  sww : Array<U32> = to_words(bsw, U32.to_nat(U32.mul(j_nsweep(j), 4)), 9n)
  w_arr : Array<F32> = fill_f32(U32.to_nat(ne), 0, Array.get(U32, ww, 0), 0,
                                 Array.new(F32, j_wdepth(j), 0.0), sc)
  r_arr : Array<F32> = fill_f32(U32.to_nat(nn), 0, Array.get(U32, irw, 0), 0,
                                 Array.new(F32, j_sdepth(j), 0.0), sc)
  v_arr : Array<F32> = fill_f32(U32.to_nat(nn), 0, Array.get(U32, ivw, 0), 0,
                                 Array.new(F32, j_sdepth(j), 0.0), sc)
  hr : Array<F32> = fill_f32(U32.to_nat(nhist), 0, Array.get(U32, hrw, 0), 0,
                              Array.new(F32, j_hdepth(j), 0.0), sc)
  hv : Array<F32> = fill_f32(U32.to_nat(nhist), 0, Array.get(U32, hvw, 0), 0,
                              Array.new(F32, j_hdepth(j), 0.0), sc)
  +swp : F32 = Core.dec_f32(word_of(Array.get(U32, sww, k)), sc)
  sim : Eng.Sim = Eng.Sim{ew, tw, w_arr, hr, hv, r_arr, v_arr,
                Array.new(F32, j_sdepth(j), 0.0), Array.new(F32, j_sdepth(j), 0.0),
                Array.new(F32, j_tdepth(j), 0.0),
                1, j_nnz(j), nn, j_hslots(j), tmask,
                j_cfa(j), j_cfb(j), swp, j_cfg(j)}
  point_body(k, Eng.step_loop(U32.to_nat(j_nstep(j)), sim, U32.to_nat(ne),
                              idx0, del0, j_hslots(j), tmask),
             j_nstep(j))


# the Sim is a single-owner Type, so it is consumed once: the header's scale and
# the trace both come out of one match

def sweep_scale(sim: Eng.Sim) -> F32:
  match sim:
    case Eng.Sim{edge, tgt, w, hr, hv, r, v, cr, cv, tr, t, nnz, n_nodes,
                 hslots, tmask, cfa, cfb, scale, c}:
      scale

# 2-way and 4-way fans; the results are Strings, so they concatenate and no
# record destructuring is needed

def run_one(k: U32, +in: In) -> String:
  match in:
    case Inn{j, i0, d0, be, bt, bw, bir, biv, bhr, bhv, bsw}:
      build_and_run(k, i0, d0, j, be, bt, bw, bir, biv, bhr, bhv, bsw)

# the per-point string, including its POINT header

def point(k: U32, +in: In, +active: Bool) -> String:
  # `active` is False for lanes past n_sweep, so the fan-out is always 8 wide
  # and the unused lanes cost a match, not a simulation
  match active:
    case True{}:
      run_one(k, in)
    case False{}:
      ""

def two_str(k0: U32, k1: U32, +a0: Bool, +a1: Bool, +in: In) -> String:
  x y = point(k0, in, a0) point(k1, in, a1)
  x ++ y

def four_str(k0: U32, k1: U32, k2: U32, k3: U32,
             a0: Bool, a1: Bool, a2: Bool, a3: Bool, +in: In) -> String:
  x y = two_str(k0, k1, a0, a1, in) two_str(k2, k3, a2, a3, in)
  x ++ y

def sweep8(+j: Job, +in: In) -> String:
  +n : U32 = j_nsweep(j)
  x y = four_str(0, 1, 2, 3,
                 U32.is_lt(0, n), U32.is_lt(1, n), U32.is_lt(2, n),
                 U32.is_lt(3, n), in)
           four_str(4, 5, 6, 7,
                    U32.is_lt(4, n), U32.is_lt(5, n), U32.is_lt(6, n),
                    U32.is_lt(7, n), in)
  x ++ y

def go(args: List<String>) -> IO(Unit):
  do IO<Unit>:
    +hdr : List<&2, U32> = rev(parse_one(drop1(args), Nil{}), Nil{})
    +jb : Job = make_job(hdr)
    +psw : String <- IO.try(String, IO.get_env("JOB_SWEEP"))
    +picr : String <- IO.try(String, IO.get_env("JOB_ICR"))
    +picv : String <- IO.try(String, IO.get_env("JOB_ICV"))
    +phr : String <- IO.try(String, IO.get_env("JOB_HISTR"))
    +phv : String <- IO.try(String, IO.get_env("JOB_HISTV"))
    +ped : String <- IO.try(String, IO.get_env("JOB_EDGE"))
    +ptg : String <- IO.try(String, IO.get_env("JOB_TGT"))
    +pwf : String <- IO.try(String, IO.get_env("JOB_W"))
    # every section is read once and shared: a byte List is `Data`, so each
    # sweep point can copy it, while the Arrays it builds are single-owner
    +be : List<&2, U32> <- load_bytes(ped)
    +bt : List<&2, U32> <- load_bytes(ptg)
    +bw : List<&2, U32> <- load_bytes(pwf)
    +bir : List<&2, U32> <- load_bytes(picr)
    +biv : List<&2, U32> <- load_bytes(picv)
    +bhr : List<&2, U32> <- load_bytes(phr)
    +bhv : List<&2, U32> <- load_bytes(phv)
    +bsw : List<&2, U32> <- load_bytes(psw)
    +i0 : U32 = nth(hdr, 21n)
    +d0 : U32 = nth(hdr, 22n)
    out : String <- IO.pure(String, sweep8(jb, Inn{jb, i0, d0, be, bt, bw,
                                               bir, biv, bhr, bhv, bsw}))
    IO.print(out)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
