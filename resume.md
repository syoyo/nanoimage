# nanoimage Lean verification: resumption prompt

Repository: `~/work/nanoimage`. Current git head: `cb7f5e3` (Phase 3 groundwork).
Active continuation plan: `~/.commandcode/plans/nanoimage-formalization-status-and-plan.md`.
Status: `formal/VERIFICATION.md`. Method: `formal/README.md`.

## Current state

- **Phase 0/1 complete**: MiniC infra, translator/cdiff, shared core helper proofs in `formal/NANO/C/Proofs/Core.lean`.
- **Phase 2 BMP complete**: `ni_bmp_header_exs`, `ni_bmp_decode_into_ok_exs` (all-pixels-OK), `ni_bmp_load_exs` proven, axioms `[propext, Classical.choice, Quot.sound]`.
- **Phase 3 TGA groundwork complete, proofs pending**:
  - C: `src/nanoimage_tga_core.c`, shell `src/nanoimage_tga.c`, `ni_tga_info`/`NI_TGA_ERR_*` in `src/nanoimage_core.h`.
  - Spec: `formal/NANO/Tga.lean` (`tgaHeader`, `tgaWritesAux` fuel=pixel count, `tgaMaterialize` by `List.set`, `tgaPixels/tgaDecode`).
  - Translation: Gen fids 21-23; write_pixel is statement-call in decode (avoid expr-call `ro=true` UB).
  - Diff: cdiff arms in `formal/CDiff.lean`, `formal/tools/{cdiff_c.c,cdiff.py}`; 4800 cases / 0 mismatches total (600 TGA).
  - Lean proofs: **not started**. No `formal/NANO/C/Proofs/*Tga*`; `NANO.lean` has no TGA proof imports.

## Baseline gates (revalidated 2026-11-23)

- `make test` — pass
- `make lean-check` — pass (`lake build` + `c2lean.py --check`)
- `make lean-diff` — pass, 4800 cases, 0 mismatches

## Phase 3 TGA proof progress (as of head 986cd52)

Everything below is committed, `make lean-check` green, axiom-clean
(`[propext, Classical.choice, Quot.sound]` or smaller).

Header / write-pixel / preamble / geometry (earlier sessions):
`ni_tga_header_exs`, `ni_tga_write_pixel_exs`, `ni_tga_write_pixel_stmt_exs`,
`ni_tga_decode_preamble` (+ `_frame` continuation form), `ni_tga_dst_compute`,
`ni_tga_decode_wr_check`, `ni_tga_raw_read`, `ni_tga_pixel_step_rle/raw`,
`ni_tga_pixel_suffix`, `tgaPixelOut_raw`, `tgaFoldI(_length/_raw_eq)`,
`tgaFoldRaw(_length)`, `load_ptr_congr`.

Loop0 (inner packet loop) - complete:
`ni_tga_loop0_step_rle`, `ni_tga_loop0_rle`, `ni_tga_loop0_step_raw`,
`ni_tga_loop0_raw`.

**Uncompressed path (rle = 0) — PROVEN END TO END through loop1 and top level:**
- loop1 prologue/step/fuel induction: `ni_tga_l1pre_rle0`, `ni_tga_l1step_rle0`,
  `ni_tga_loop1_rle` (chains the step over npx-p0 via `tgaFoldI_raw_eq`).
- spec side: `tgaWritesAux_rle0_pkt`, `tgaWritesAux_rle0_walk`,
  `tgaFoldRaw_eq_materialize` (machine buffer = materialised spec writes).
- composition: `ni_tga_loop1_rle_ok`, and top level
  `ni_tga_decode_into_ok_rle0` (preamble + loop1 + ret 0 -> tgaPixels).
- **Bug fixed**: `tgaDecodePre`/preamble used `.int i32 0` (signed) where Gen
  uses `.int ⟨32,false⟩ 0`; corrected, frame body now `rfl`-equal to Gen's body.

**Compressed path (rle != 0) — components done, joint loop1 induction pending:**
- post-header state: `ni_tga_l1posthdr`.
- packet prologues: `ni_tga_l1pre_rle_bytes`, `ni_tga_l1pre_rle_raw`.
- packet steps: `ni_tga_l1step_rle_pkt`, `ni_tga_l1step_raw_pkt`.
- spec per-packet steps: `tgaWritesAux_rle_pkt`, `tgaWritesAux_raw_pkt`
  (plus `tgaHawStep`, `foldlM_*`, `tgaMaterialize_rle/raw`).
- spec bounds inversions: `tgaWritesAux_ok_off`, `tgaWritesAux_ok_cnt`.
- spec well-formedness: `TgaOkW` (fuel-indexed) and
  `tgaWritesAux_ok_of_TgaOkW` (TgaOkW => tgaWritesAux succeeds).
- `tgaPixelOut_ext` (channels-only dependence).

**Compressed path (rle != 0) — NOW PROVEN END TO END:**
- `ni_tga_loop1_rne`: fuel induction over the packet loop (rle != 0), carrying
  the joint machine+spec invariant; dispatches per packet on the header high bit,
  using `ni_tga_l1step_rle_pkt`/`_raw_pkt`, `tgaWritesAux_rle_pkt`/`_raw_pkt`,
  `TgaOkW`, and `tgaMaterialize_rle`/`_raw` for the buffer reconciliation.
- `ni_tga_decode_into_ok_rne`: top-level for compressed images (preamble +
  loop1 + ret 0 -> tgaPixels), precondition `TgaOkW` over the initial walk.
- helper lemmas in `TgaLoop1Rle`: `tgaPixelOut_congr`, `tgaPixelOut_byteAt_eq`,
  `tgaPixelOut_raw_byteAt_eq`.

**Both decode top-level theorems now exist**: `ni_tga_decode_into_ok_rle0`
(uncompressed) and `ni_tga_decode_into_ok_rne` (compressed). A single
mode-dispatching `ni_tga_decode_into_ok_exs` combining them is the next small
step (each branch takes its own data-bound hypotheses; rle0 needs per-offset
`hdbnd`/`hdob` which `TgaOkW` does not directly yield for the single byte read).

**Remaining for the full TGA goal:** unified top-level `ni_tga_decode_into_ok_exs`,
then **M4** `ni_load_tga` -> `tgaDecode` (compose header fid21 + decode fid23 and
handle the error/tag path).

## Immediate next work (M1-M4)

1. **M1 `ni_tga_header_exs`**: staged refinement like BMP header but simpler (no geometry sign/INT_MIN split). Export info-block predicate/constructor for composition.
2. **M2 `ni_tga_write_pixel_exs`**: per-channel store proof (1/3/4), statement-call-friendly wrapper; bad channels return 0, no writes.
3. **M3 decode loops + `ni_tga_decode_into_ok_exs`**: bridge `tgaMaterialize` write-list/List.set spec to in-place buffer early. Inner loop over packet pixels; outer loop induction over remaining pixels (`n_pixels - pixel_index`).
4. **M4 `ni_tga_load_exs`**: compose header fid21 then decode fid23; update VERIFICATION/resume; close Phase 3.

## Key constraints

- No `sorry`/`admit`; axioms only `[propext, Classical.choice, Quot.sound]`; no `native_decide`.
- `Gen.lean` generated only via `python3 formal/tools/c2lean.py`.
- Factor proofs aggressively (separate lemmas/files) to avoid kernel deep recursion.
- Preserve TGA statement-call pattern for `ni_tga_write_pixel`.
- Run `#print axioms` on new top theorems; keep `make test`, `make lean-check`, `make lean-diff` green before each commit.

## Useful commands

```sh
cd ~/work/nanoimage
make test
make lean-check
make lean-diff
python3 formal/tools/c2lean.py --check
cd formal && lake build NANO.C.Proofs.<Module>
```

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
