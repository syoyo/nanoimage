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

## Phase 2 is COMPLETE (commit C3)

`ni_bmp_load_exs` (`NiBmpLoad.lean`) is proven: under the five stage verdicts,
header (fid 15) then decode (fid 16) returns 0 and the output block holds the
flattened `bmpPixels` bytes for `h = bmpHeaderInfoOf d`; axioms
`[propext, Classical.choice, Quot.sound]`. All gates green (`make test`,
`make lean-check`, cdiff).

Key pieces added to get there:
- Framing exports `∀ b ≠ 3, s'.mem b = s.mem b` on every header stage
  (`mem_upd_other_blk` peel; threaded through geometry/arith/palette/stores/
  prelude/rem/header).
- Decode chain: locals-25 invariant dropped from `loop2_iter`/`loop3_iter`;
  info block unified to 3; `ni_bmp_decode_into_ok_exs` over the 5-param call
  frame; palette-read bounds (`hpos8`/`hidx8`) conditional on `bitCount = 8`.
- `ExS.call_ret` (Logic.lean); `bmpHeaderInfoOf` + `bmpHeader_ok_of_stages`;
  the ten `bmpHeaderFinalBlock` field slices; the bound bundles
  `bmpHeaderInfoOf_stage_facts` (17-way conjunction), `_px8`, `_pos8`,
  `_idx8` (factor monolithic derivations — the kernel chokes otherwise).

## Next: Phase 3 — TGA

See `~/.commandcode/plans/nanoimage-formal-remaining-phases.md`, Milestone 2:
C refactor (core/shell split, error codes), translator + Gen regen, spec
`NANO/Tga.lean` (sequential packet-stream `tgaPixels`), cdiff generator, then
refinement proofs (header → write_pixel → RLE loops with the
`pixel_index + count ≤ width*height` invariant). Commits C4/C5.

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
