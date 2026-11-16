# nanoimage Lean verification: resumption prompt

Repository: `~/work/nanoimage`. Last commit: C1 (Phase 2 decode composition
groundwork). `git log` for history.

Plan of record: `/home/syoyo/.opencode/plan/nanoimage-lean-verification.md`.
Remaining-work plan: `~/.commandcode/plans/nanoimage-formal-remaining-phases.md`.
Status doc: `formal/VERIFICATION.md`. Method doc: `formal/README.md`.

## Where things stand

Phase 0 (infrastructure) done. Phase 1 (shared leaves) done. Phase 2 (BMP):

- `ni_bmp_header_exs` proven end-to-end (axioms
  `[propext, Classical.choice, Quot.sound]`), now with a **guarded memory
  export**: on success the info object holds `bmpHeaderFinalBlock d gout`
  (`NiBmpHeaderCompose.lean`: `bmpHeadBlock`, `bmpHeaderFinalBlock`,
  `header_stores_exs` + memory export, `ni_bmp_header_rem_stores_exs`,
  `ni_bmp_header_rem_exs`, `ni_bmp_header_exs` — all with the export).
- **`ni_bmp_decode_into_ok_exs` is PROVEN** (`NiBmpDecodeInto.lean`) —
  all-pixels-OK case, axioms clean. Key moves vs the old notes: the `e`
  rewrite closes with `ac_rfl`; `hch8` was replaced by
  `hc32 : h.channels = (if h.bitCount = 32 then 4 else 3)` plus `hrsd` and
  `hobl64` hypotheses; the 8-bit branch calls `loop1_iter` DIRECTLY (it takes
  an arbitrary state with pointwise locals hypotheses — no bridge lemma
  needed, despite what the old notes say about the row-entry frame); the
  direct branch evaluates `.set 19` via `EvE.cond` + `hc32` and calls
  `loop3_iter` directly; the tail is `ExS.seq … (ExS.ret (EvE.const _))`
  through an `hFin` assembler; the memory conclusion rewrites `bmpRowSize h`.
- New `formal/NANO/C/Proofs/NiBmpLoad.lean` (imported by `NANO.lean`):
  - 19 field-slice lemmas, layered per store stage
    (`arithBlock_*`, `palBlock_*`, `headBlock_*`, then the ten
    `bmpHeaderFinalBlock_*` slices + length). Layering matters: a one-shot
    flat-rewrite of the 3-constructor block hits kernel deep recursion.
  - `bmpHeaderInfoOf d` (spec witness) and `bmpHeader_ok_of_stages`
    (five stage verdicts ⇒ `bmpHeader size d = .ok (bmpHeaderInfoOf d)`),
    modeled on `bmpHeaderCode_zero_of_ok` and using the existing
    `bmpOutputCompose_ok_8` / `bmpOutputCompose_ok_ne8`.
- `ExS.call_ret` in `Logic.lean`: statement-level call of a value-returning
  function (result discarded, caller continues with `.normal`).
- Gates all green: `make test`, `make lean-check` (lake build + c2lean
  --check), `make lean-diff` (4200 cases, 0 mismatches).

## Current work in progress: `ni_bmp_load_exs` (NiBmpLoad.lean)

The composite: `.seq (.call (some 17) 15 [v0,v1,v2]) (.seq (.ite (.ne (var 17)
0) (.ret (var 17)) .skip) (.seq (.call none 16 [v0..v4]) (.ret 0)))` over
frameLocals [0,1,2,3,4,17] — returns `bmpHeaderCode size d`; on success runs
the decode and the out block holds `bmpRowsBytes d H H.height ++ out.drop (H.height *
bmpRowSize H)` with `H := bmpHeaderInfoOf d`, plus `bmpHeader size d = .ok H`.

**Blocker found**: `ni_bmp_decode_into_ok_exs` is stated over the 26-local
frame (`frameLocals [0..25] …`), but a call creates the 5-param frame
(`frameLocals [0,1,2,3,4] …`, locals ≥ 5 unbound). `loop2_iter` and
`loop3_iter` carry an over-strong `s.locals 25 = some (.int ⟨32,true⟩ 0)`
hypothesis (threaded as an invariant); local 25 is *written before it is ever
read* (loop2's `call_dst (some 25) 20 …`), so the hypothesis can simply be
dropped.

## Next steps, in order

1. **Weaken the loop iter invariants**:
   a. `NiBmpLoop2.lean` `loop2_iter`: drop `s.locals 25 = some (.int 32t 0)`
      from the hypotheses (line ~91), from the conclusion (line ~103), the
      intros (lines ~107/145), the zero-case `exact hl25` (line ~142) and its
      `refine` slot, and the succ-case threading (`h25b` stays — it is
      re-derived from the per-pixel call's return by `rfl`; drop `hl25_3`,
      the IH arg at line ~431, and the `hLoc25'` export/arg). Keep the
      general preservation `∀ j, j ≠ 6 → j ≠ 23 → j ≠ 24 → j ≠ 25 → …`
      unchanged. Update the wrapper `ni_bmp_decode_into_loop2_ok_exs`
      accordingly (it may keep its own frame; just pass fewer args).
   b. `NiBmpLoop5.lean` `loop3_iter`: same treatment (hypothesis line ~63,
      intros ~73/101, the `s1.locals 25` extract at ~307, `hl25_5` at ~396,
      the recursive-call arg list at ~406, and the export). **Keep the
      `locals 19` hypotheses** — local 19 (src_channels) is genuinely read
      by loop2's dst_base computation.
2. **Restate the decode theorem over the call frame**: in
   `NiBmpDecodeInto.lean`, change the theorem's frame to
   `frameLocals [0,1,2,3,4] [.ptr bd 0, .int u64 d.length, .ptr 2 0, .ptr ob 0,
   .int u64 obl.length]` (info block = 2, the harness convention), delete the
   `hl25` have, and rebuild the pointwise facts (locals 0-4 by rfl; 7..13 via
   the existing extract chains; 5/19 after their sets). Everything else in
   the proof is frame-agnostic.
3. **Assemble `ni_bmp_load_exs`** (NiBmpLoad.lean):
   - `ExS.call_dst` for the header call (args `[v0,v1,v2]`, dst 17) using
     `ni_bmp_header_exs`'s ExS + its guarded export (hypotheses: the five
     stage verdicts) → code in local 17, info block = block 2 filled.
   - Reject path: `ExS.ite` true-branch `.ret (var 17)`; the composite's
     outcome `.ret (bmpHeaderCode size d)` matches directly.
   - Success path: `ExS.ite` false-branch skip → `ExS.call_ret` for the
     decode call (body ExS = the restated decode theorem; baton-pass
     `bmpHeaderFinalBlock d gout` as `info`, all ten field slices, bounds
     from `arithCode_unfold` + the prelude-style derivations, `hidx8` from
     `hok` via `bmpPixel_idx_lt_entries_of_ok`, `hpx8`/`hpos8` from `hpx` +
     `hpalok` + 8-bit `bmpRowStride w 8 ≥ w` by omega, `hrsd` for the direct
     path by case analysis on bitCount, `hcap`/`hcap64` as hypotheses) →
     `.ret 0` = `.ret (bmpHeaderCode size d)` (code = 0).
   - Close with `bmpHeader_ok_of_stages` for the spec link. Finish with
     `#print axioms ni_bmp_load_exs` — expect `[propext, Classical.choice,
     Quot.sound]`.
4. Update `formal/VERIFICATION.md` (mark the composition row proven) and
   commit C2.
5. Phase 3: TGA (see the remaining-work plan, Milestone 2).

## Key implementation notes (Phase 2 + composition work)

- **Kernel deep recursion**: factor every proof into separately declared
  theorems. For list slices over multi-constructor blocks, prove slices
  LAYERED (one constructor per lemma: `arithBlock_*` → `palBlock_*` →
  `headBlock_*` → final); a one-shot flat rewrite of the 3-constructor
  `bmpHeaderFinalBlock` hits "(kernel) deep recursion detected".
- **omega treats `a * b` and `b * a` as DIFFERENT atoms** — normalize
  multiplication order to match the goal before the final omega
  (see `hrow`/`e1` in `NiBmpDecodeInto.lean`'s `hsrcD`).
- **AC goals close with `ac_rfl`** (core Lean); omega fails on var*var atoms.
- `frameLocals` reduction: plain `rfl` works for small indices on literal
  frames; `simp only [frameLocals_apply]` fails on let-bound states (use
  plain rfl — the let zeta-reduces). For large indices use
  `by simp only [frameLocals_apply]; rfl` on literal frames only.
- Track state-succession with pointwise `s.locals i = some …` hypotheses;
  rewrite with `Locals.upd_same`/`Locals.upd_ne` (`locals_upd_extract`).
- `bin_u64_mul`/`bin_u64_add` need explicit `< 2^64` bounds; `bin_u64_gt/lt/eq`
  are rfl-style; `bin_u64_sub` takes `k ≤ n`.
- `simp only [frameLocals_apply]` / `split` on `let`-bearing defs: use full
  `simp [def, …]` (zeta-reduces) rather than `simp only [def]` + `split`.
- Loop wrappers take only locals the body reads — but audit for
  write-before-read locals that were included "for free" (the locals-25
  case above); they block call-frame composition later.
- `EvE.cond (hc) (hbc : truthy vc = .ok bc) (hv : EvE p s (if bc then a else b) v)`;
  `ExS.ret (EvE.const _)` builds `.ret` steps; `ExS.seq_ret` is only for a
  returning FIRST component (the normal-path tail is plain `ExS.seq`).
- `if_pos`/`if_neg` are deprecated → `ite_eq_left`/`ite_eq_right`.
- `.index` yields `Val.ptr b (0 + i * 1)` — rewrite via `load_byte_at`/
  `store_byte_at` + omega.

## Build and check quickly

```sh
cd ~/work/nanoimage
make test
make lean-check
make lean-diff
python3 formal/tools/c2lean.py --check
```

After editing a core C function:

1. `python3 formal/tools/c2lean.py` (regenerates `formal/NANO/C/Gen.lean`)
2. `cd formal && lake build`
3. `make lean-diff`

Fast iteration on one module: `cd formal && lake build NANO.C.Proofs.NiBmpLoad`
(only rebuilds that module + its deps). A full-tree rebuild after touching
`Logic.lean` takes ~25 min.
