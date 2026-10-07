# json_demo.bend -- the compiled binary that ingests ARBITRARY JSON at
# runtime.  Usage:
#
#   bend json_demo.bend -o json_demo && ./json_demo '<json-config>'
#
# The schema (see json_ingest.bend):
#   {"lanes":[k0,k1,...],"projs":[[src,tgt,d,win,tc],...],"horizon":h}
#
# The binary parses the string, gates on json_good (parse-valid AND
# R.ok == True -- it refuses to run anything else), runs 4 master ticks,
# then prints the runtime INSTANCES of the proven properties on this very
# config:
#
#   sweep: names=N cols=M ns=K -- the total SWEEP ingress's decode of the
#       same argv string (see json_ingest.bend's sweep schema): printed
#       before the gate, so a rejected input's decode is still visible.
#       garbage decodes to 0/0/0; proved total by json_sweep_garbage.
#   plateau (d = 1+n+0 vs 1+n+9)  -- Laws.json_delay_plateau: both delays
#       are past the whole history, so both reads are THE IC read.  True
#       for every input string; proved, so a False here is impossible.
#   fresh (i1 <= newest)          -- Laws.read_fresh: no routed read ever
#       names a sample beyond the newest published one (causality).
#
# Together: for any config that enters as JSON text, reads never see the
# future, and out-of-history delays saturate onto the IC instead of
# wrapping around a ring.

import Base
import ./router.bend as R
import ./sweep.bend as S
import ./json_ingest.bend as J

def show_line(+l: R.Line) -> String:
  "i0=" ++ Nat.show(R.l_i0(l)) ++ " i1=" ++ Nat.show(R.l_i1(l)) ++ " num=" ++ Nat.show(R.l_num(l)) ++ "/" ++ Nat.show(R.l_den(l)) ++ " win=" ++ Nat.show(R.l_win(l))

def show_lines(ls: List<&2, R.Line>, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case h <> t:
      show_lines(t, acc ++ " | " ++ show_line(h))

def show_nats_go(xs: List<&2, Nat>, +acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      show_nats_go(t, acc ++ "," ++ Nat.show(h))

def show_nats(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case h <> t:
      show_nats_go(t, Nat.show(h))

def count_projs(ps: List<&2, R.Proj>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case h <> t:
      1n+count_projs(t)

def line_eq(+a: R.Line, +b: R.Line) -> Bool:
  Bool.and(Nat.is_eq(R.l_i0(a), R.l_i0(b)),
  Bool.and(Nat.is_eq(R.l_i1(a), R.l_i1(b)),
  Bool.and(Nat.is_eq(R.l_num(a), R.l_num(b)),
  Bool.and(Nat.is_eq(R.l_den(a), R.l_den(b)),
           Nat.is_eq(R.l_win(a), R.l_win(b))))))

def plateau_str(+ls: List<&2, R.Lane>, ps: List<&2, R.Proj>, +acc: String) -> String:
  match ps:
    case Nil{}:
      acc
    case +h <> t:
      plateau_str(ls, t, acc ++ " " ++ Bool.show(line_eq(J.route_bump(ls, h, 0n), J.route_bump(ls, h, 9n))))

def proj_fresh(+ls: List<&2, R.Lane>, +p: R.Proj) -> Bool:
  Nat.is_le(R.l_i1(R.route_proj(ls, p)), R.lane_newest(R.nth_lane(ls, R.proj_src(p))))

def fresh_all(+ls: List<&2, R.Lane>, ps: List<&2, R.Proj>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(proj_fresh(ls, h), fresh_all(ls, t))

def final_report(+ls: List<&2, R.Lane>, +ps: List<&2, R.Proj>) -> IO(Unit):
  do IO<Unit>:
    IO.print("plateau (d=1+n+0 vs 1+n+9): " ++ plateau_str(ls, ps, ""))
    IO.print("fresh   (i1<=newest):       " ++ Bool.show(fresh_all(ls, ps)))

def tick_loop(m: Nat, tk: R.Tick, +ps: List<&2, R.Proj>) -> IO(Unit):
  match m tk:
    case 0n R.Tick{lanes, lines}:
      final_report(lanes, ps)
    case 1n+p R.Tick{lanes, lines}:
      do IO<Unit>:
        IO.print("tick: " ++ show_lines(lines, ""))
        tick_loop(p, R.tick(lanes, ps), ps)

# the SWEEP decode line: what the total sweep ingress makes of this same
# argv string -- names/cols counts and the decoded sim count (garbage
# decodes to the empty sweep: 0/0/0).  Printed BEFORE the config gate so
# a rejected input's decode is still visible.
def sweep_line(+json: String) -> String:
  +sw = J.json_sweep_decode(json)
  "sweep: names=" ++ Nat.show(J.names_len(J.sw_names(sw)))
    ++ " cols=" ++ Nat.show(S.rows_len(J.sw_cols(sw)))
    ++ " ns=" ++ Nat.show(S.cols_ns(J.sw_cols(sw)))

# the NAMED-CONFIG decode line: what the total named-config ingress makes
# of the same argv string -- lanes / per-lane name lists / projections /
# per-projection cvar-name counts, and the heterogeneous validator's
# verdict (garbage decodes to the empty named config: all zeros, ok=false;
# proved total by json_named_garbage).  Printed BEFORE the gate, next to
# the sweep line, so a rejected input's decode is still visible.
def count_nats(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      1n+count_nats(t)

def count_slists(xs: List<&2, List<&2, String>>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      1n+count_slists(t)

def named_line(+json: String) -> String:
  +jn = J.json_named_decode(json)
  "named: lanes=" ++ Nat.show(count_nats(J.jn_lanes(jn)))
    ++ " models=" ++ Nat.show(count_slists(J.jn_snames(jn)))
    ++ " projs=" ++ Nat.show(count_projs(J.jn_projs(jn)))
    ++ " svars=" ++ Nat.show(J.names_len(J.jn_svars(jn)))
    ++ " tcvars=" ++ Nat.show(J.names_len(J.jn_tcvars(jn)))
    ++ " ok=" ++ Bool.show(J.jn_good(jn))

def report(+cfg: R.Config, +json: String) -> IO(Unit):
  do IO<Unit>:
    IO.print(sweep_line(json))
    IO.print(named_line(json))
    IO.print("ok=PASS lanes=" ++ show_nats(R.cfg_lanes(cfg)) ++ " projs=" ++ Nat.show(count_projs(R.cfg_projs(cfg))) ++ " horizon=" ++ Nat.show(R.cfg_horizon(cfg)))
    tick_loop(4n, R.tick(R.init_lanes(R.cfg_lanes(cfg)), R.cfg_projs(cfg)), R.cfg_projs(cfg))

# the NAMED gate: the named-config validator's own verdict -- the named
# decode is parse-valid AND jn_good (the name-per-projection lengths and
# the heterogeneous layer's mc_ok at the decoded shapes/view/config), so
# the binary runs the DECODED config (jn_cfg) under the proved contract
# (json_named_contract, LAWS_mconfig.bend).
def named_gate(g: Bool, +jn: J.JN, +json: String) -> IO(Unit):
  match g:
    case True{}:
      report(J.jn_cfg(jn), json)
    case _:
      do IO<Unit>:
        IO.print(sweep_line(json))
        IO.print(named_line(json))
        IO.print("REJECTED: bad JSON or the named validator == False")

# the ingress order: the PLAIN gate first, the named gate only on refusal.
# The named keys junk the plain parse and the plain keys are a subset of
# the named schema, so the two gates accept disjoint documents -- the
# plain path keeps every pinned output, the named path adds the
# heterogeneous ones.
def show_gate(g: Bool, +jn: J.JN, +json: String) -> IO(Unit):
  match g:
    case True{}:
      report(J.json_decode(json), json)
    case _:
      named_gate(J.jn_good(jn), jn, json)

def run_json(+json: String) -> IO(Unit):
  show_gate(J.json_good(json), J.json_named_decode(json), json)

def arg_or_usage(args: List<String>) -> IO(Unit):
  match args:
    case json <> rest:
      run_json(json)
    case _:
      do IO<Unit>:
        IO.print("usage: json_demo '<json-config>'")

def main_go(args: List<String>) -> IO(Unit):
  match args:
    case prog <> rest:
      arg_or_usage(rest)
    case _:
      arg_or_usage(Nil{})

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args
    main_go(args)
