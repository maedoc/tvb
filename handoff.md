# Handoff — tvb-bend: the Bend router worktree (feat/bend-router)

## Where I am
- cwd `/home/duke/src/tvb-bend` — a **git worktree** of `/home/duke/src/tvb-kh`,
  branch `feat/bend-router`, based on **origin/master @ d37a429b6** ("feat(models):
  two-population GastSollaKennedy E/I (RS+FS) model" — up to date, includes the
  merged PR #799 work). Created 2026-10-01, night.
- ALL the bend work is copied to
  `tvb_library/tvb/simulator/backend/bend_hybrid/` and shows as **untracked** —
  **the user commits it themselves** (explicitly requested; do NOT commit).
- The original copy still lives (untracked) in `/home/duke/src/tvb-kh` — same
  files; tvb-kh remains the reference. Edits should happen HERE now.
- **Both gates verified green in this worktree**: the router gate
  (`tests/run_router.sh`: 36 laws kernel-verified, 5 negative controls rejected,
  3 pinned functional tests) and the older Montbrio gate
  (`bend PROOF.bend --verdict` → ALL PROOFS CHECK).

## What exists (two generations, both complete)
1. **Montbrio prototype** (first session): `mcore.bend`/`mengine.bend`/
   `montbrio_sweep.bend` + `LAWS.bend`/`PROOF.bend` + Python drivers
   (`run_montbrio.py`, `compare_montbrio.py`, `bench_montbrio.py`).
   Measured: 5.09× sweep speedup (8 pts, nested parallel lets), one-step drift
   bit-exact, coupled+delayed vs NbHybridBackend ~1e-5. `sketch.bend`/`SKETCH.md`
   = earlier design sketch. Doctrinal docs: `README.md`, `BEND_TVB_GUIDE.md`
   (START HERE for Bend judgement), `NOTES.md` (ALL syntax/proof gotchas —
   read before writing any Bend).
2. **The router** (this session, the real thing): `router.bend` (Nat routing
   core: Lane{k,left,newest} carried counters, route_read + the ZOH clamp,
   route_window/Q2, tick, ok/csr_ok validators, le_ok deciders),
   `kernel.bend` (F32 leaf layer: blend, cfun_linear, gather — op-order laws),
   `LAWS_router.bend` (36 claims: arithmetic bricks, schedule, control flow
   (chunking/read-then-push gating as lemmas), read (freshness, clamp
   necessity, degenerate golden rule), config/CSR validators, leaf op-order),
   `PROOF_router.bend` (discharges; --verdict clean), `bad/` (5 negative
   controls), `tests/` (3 functional, `#|`-pinned) + `tests/run_router.sh`
   (THE gate), `ROUTER_EXPLAINER.md` (the published doc).
- Docs published on the lab HedgeDoc under `marmaduke`:
  v2 explainer **https://md.ins-amu.fr/MP2SQRNHSVCOr6zISn4UBw** (v1
  `z5kjuhFjSteaZNXT0Y4CVQ` deletable). Posting skill:
  `~/.pi/agent/skills/hedgedoc-amu/`. AGENTS.md now has a `# writing` rule
  (post explainers with diagrams freely).

## Design decisions that are LOAD-BEARING
- **Carried counters, not closed forms**: no div/mod anywhere in the schedule;
  every schedule law is structural induction over the tick stream. Designing
  for the prover paid the proof debt in the data representation.
- **Laws = Bool checks + hypothesis binders** (`for +h: {ok == True{}}`),
  bendygrad pattern. le_ok-as-Type only for witness constructors + negatives.
- **Routing policies are schedules**: staggered (current tvb-kh) and macro-first
  co-simulation are both expressible with the SAME primitives — macro-first
  slow→fast interpolated read = `route_read(d=1, phase)` (fresh, no clamp);
  fast→slow = `route_window(w=k)`. `clamp_necessary` is the causality theorem
  that adjudicates between them. Duality: zero-lag interp ⟺ windowed input.
- **Floats**: op-order contracts on symbolic F32 terms (blend_order,
  cfun_linear_order, gather_cons) — value-equal regroupings are REJECTED
  (bad/bad_blend.bend). Values stay in differential testing. 3-tier division:
  laws pin structure/order, literal laws pin transcription, Python pins values.

## THE BACKLOG — in mind, not done (grouped, with prereqs)

### A. Laws queued, machinery exists (days)
1. **`count_shared` + monitor model**: the run has ONE tavg_count incremented
   once per master tick for ALL subnets (template L1195/L1102; decision 6 pins
   it for ctavg). Needs a small monitor/count extension to `tick`. Stops
   someone "fixing" the shared counter to per-subnet due-ticks (would silently
   change slow subnets' averages from master-time to per-own-step meaning).
2. **`monitor_zoh_average`**: tavg = master-time average of the ZOH-held
   trajectory. Routing half is ALREADY the combination lane_hold +
   due_iff_publishes + period_from_init; needs the count model (A1) for the
   statement, float half (Σ/k) needs trees (D).
3. **`window_span`** (Q2 quantified): hi−lo == w given d+w ≤ n. Prereq:
   subtraction library — **sub_add_cancel is proved**; needs ~2 more bricks
   (sub_sub_add, add_cancel_right-ish). Also state `route_window` window
   placement law.
4. **`staleness_bound` / age law** (Q1's "up to k−1 ticks stale"): age =
   k−1−left; statement needs lt→le-sub lemma + sub bricks. `left_det` (proved)
   already gives decision 10's "identical step grids" via purity.
5. **`delay_injective` / `ring_liveness`**: distinct delays < H read distinct
   live slots; reads land in [m−H+1, m]. PREREQ REFACTOR: **horizon is
   per-SOURCE-lane in the template** (one shared srcbuf, H = max over outgoing
   projections, nb_hybrid source_horizons) but global in our Config — move it
   into Lane/Config-per-lane first.
6. **cvar/mode_map image laws**: target_state_cvar == cvar[target_cvar]; the 4
   `_cvar_mapping_mode` cases total; bounds. Same shape as csr_ok validators +
   instances.
7. **`merge_equal_k`**: decision 9's decider (mirrors _can_merge_subnets).
8. **`convention_reconciliation`**: route(t) ≡ template read phase at t+1
   (0- vs 1-based tick, step-then-read vs read-then-push). One identity; makes
   the router a spec OF the engine. Read the mako `_slot_setup`/`_read`
   (L29–72) carefully first; run cgg on nb_hybrid before touching anything.

### B. Semantics discovered in the template, not yet law-stated
9. **`consumption_law`**: coupling+stimulus are computed EVERY master tick but
   consumed ONLY at due ticks (c zeroed each tick; integrate if t%k==0);
   odd-tick values feed only ctavg. For slow targets this is the Q2 discussion
   in disguise. Needs a c-lifecycle model in the router (due exists; extend
   tick with consumed/monitor channels).
10. **`stimulus_grid` + `noise_subsample`** (decision 7 + template noise
    indexing): bounds (t−offset−1 ∈ [0, nstep)) + the same consumption
    characterization — documents that slow subnets SUBSAMPLE master-grid
    stimulus/noise.

### C. Routing policy work (the interesting design space)
11. **`macro_tick` implementation**: macro-first co-sim as a real scheduler
    (slow steps first, fast micro-ticks route with d=1+phase, slow input =
    route_window). Demo exists (tests/cosim_window.bend) but no scheduler def.
12. **`macro_degenerate` law**: k=1 ⟹ macro_tick ≡ tick (the policy's own
    golden rule).
13. **`slow_lag_necessary`**: the dual of clamp_necessary — in macro-first the
    slow's input is one window stale, necessarily (formalizes the duality).
14. Then: ZOH-policy, average-policy, mixed per-projection policies — the
    router treats policy as config; laws per policy.

### D. Floats-as-leaves (bendygrad FTree pattern) — the next architecture step
15. **History as F32 trees**: Data-kinded balanced 2^d trees = shareable/
    forkable (the GPU §6 representation — same rep serves proofs and GPU).
16. **IC const-fold law**: a read saturating below 0 returns the IC leaf, for
    any depth/config — induction on tree depth (bendygrad's Buf.view_const
    pattern). Composes with read_fresh (routing says which slot, fold says
    what's in it).
17. **Drift as symbolic tree identity** (generalize LAWS.bend's literal
    version), monitor fold identities, full degenerate-gate bit-parity.
18. After trees: the Python differential harness against this Bend kernel
    (instead of only numba-vs-numba).

### E. Python-side verification (the adversary)
19. **Property harness**: random configs (N, density, delay vectors with
    ties/gaps, cvar maps, sweep descriptors) attacking `ok`/`csr_ok`,
    cross-checked against nb_hybrid's `_analyse`/`_cvar_mapping_mode`/horizon
    ValueError behavior. Hypothesis. This was the user's stated #1 interest.
20. **CSR into route**: Csr type + validators exist standalone; wire per-edge
    delays into route_proj (Proj.d is currently the scalar max; template has
    per-edge idelays) — the routing tree then matches the CSR fold 1:1.

### F. Housekeeping
21. `/tmp/proofdemo` (demo.bend/bad.bend) never migrated — superseded by
    router's deciders; delete or fold the two multi-dt facts into LAWS_router.
22. `~/Downloads/Multi-Rate Hybrid Simulator.pdf` → `/tmp/multirate.txt` +
    `/tmp/tvb-root-ref` (sipv clone, feature/heterogeneous-timesteps) —
    reference material for Q2/averaging semantics; /tmp may be gone.
23. bendygrad reference `/tmp/bendygrad` (KapioKai) — PORTING_RULES.md is
    required reading; /tmp may be gone (it's cloned from
    https://github.com/KapioKai/bendygrad).
24. Old session HTML exports at tvb-kh repo root (pi-session-*.html) — user
    was asked whether to delete; unanswered.

## Next 3 actions (my order, ties broken by user's stated interests)
1. **E19 property harness** — the user's #1 interest; also the cheapest real
   validation of ok/csr_ok (and it would have caught nats_last).
2. **A1+A2 count_shared/monitor model** — closes the tavg story (the question
   the user actually asked); small router extension.
3. **A5 per-lane horizon refactor + delay_injective/ring_liveness** — the
   template's own aliasing argument as theorems; unlocks Tier-2 generally.
   (Then C11 macro_tick — the design space the user is most excited about.)

## Do-not-forget (operational)
- **bend binary**: `/home/duke/.bend/bin/bend` (which bend fails). Lean 4.34
  via elan, symlinked into ~/.local/bin (non-interactive shells miss profile)
  — needed for `--verdict`.
- **THE gate**: `cd tvb_library/tvb/simulator/backend/bend_hybrid &&
  tests/run_router.sh` — proofs --verdict + bad/ rejected + pinned tests.
  Run before ANY commit. Montbrio gate: `bend PROOF.bend --verdict` (separate
  LAWS/PROOF pair, older).
- **No .venv in this worktree** — Python drivers need one: `uv` per AGENTS.md
  (`cd tvb_library && uv venv && uv pip install -e .` or mirror tvb-kh's
  setup; compare_montbrio.py needs numpy+numba+tvb). Until then, drivers can
  run from tvb-kh's venv against this tree via PYTHONPATH.
- **Bend idioms** (all in NOTES.md "Router" sections): law binders `+` in the
  LAW not the proof def; `1n++q` for reusable succ binders; Equal.sym(A,a,b,e)
  takes e:{a==b} → {b==a} (order errors name the flipped equation); symbolic
  Nat arithmetic only reduces when the FIRST arg is the scrutinee (`1n+n`,
  never Nat.add(n,1n)); `List<&2, T>` is Data-kinded; no mutual recursion;
  one match per def; declare before use; termination = shrinking arg FIRST;
  cons literals in let need type annotations; do-IO binds via `<- IO.pure`;
  strings `++`; nested constructor patterns in cons forbidden (helper defs).
- **Positive instance laws are load-bearing** (nats_last bug passed all
  negatives, caught by csr_ok_good). Every validator needs a GOOD instance.
- **bad/ files must never be imported** by PROOF_router.bend.
- F32 has no value laws (not even 0.0+0.0==0.0); op-order laws only; job data
  as u32 words with floats as scaled ints (no bit-cast exists).
- Sweep parallelism: nested parallel lets over points (5×); NEVER IO.spawn
  (exactly serial) or per-node forking (5.7× slower). GPU needs tree history.
- Multi-dt spec: parity_audit.md §6 decisions 1–12 (in
  tvb_library/tvb/simulator/backend/cpp_hybrid/parity_audit.md on master).
- dapper-moss handoff (read-only multi-dt review, Q1–Q4):
  ~/.pi/agent/handoffs/done/2026-10-01-home-duke-.localterm-worktrees-tvb-kh-dapper-moss.md
- Posting pads: skill hedgedoc-amu; mermaid renders in preview (user
  confirmed), maybe not on published pages; no edit API — "update" = new note.
- GitHub writes on tvb repos need EXPLICIT owner approval (never push
  unprompted).

## Pointers
- Router core: `router.bend`; leaf layer: `kernel.bend`; claims:
  `LAWS_router.bend`; proofs: `PROOF_router.bend`; negatives: `bad/`;
  functional: `tests/`; gate: `tests/run_router.sh`; explainer:
  `ROUTER_EXPLAINER.md`; judgement: `BEND_TVB_GUIDE.md`; gotchas: `NOTES.md`;
  Montbrio prototype: `mcore/mengine/montbrio_sweep/LAWS/PROOF*.bend` +
  `*_montbrio.py`.
- Key template refs (on master): `templates/nb-hybrid-sim.py.mako` L29–72
  (_slot_setup/_read — the read semantics), L955–1132 (main loop),
  `nb_hybrid.py` L691 (_validate_multi_dt), L714 (_stim_master_grid),
  L1642–1667 (horizon ValueError + chunking comment), L1012+ (ProjectionInfo).
- Sessions: ~/.pi/agent/sessions/--home-duke-src-tvb-kh--/ (this session's
  jsonl is the newest; future tvb-bend sessions will be under
  --home-duke-src-tvb-bend--).
