# nanoimage Lean verification: resumption prompt

Repository: `~/work/nanoimage`. Nothing is committed. `git status` shows
modified decoders, `Makefile`, `xmake.lua`, `.gitignore`, `README.md`,
`src/nanoimage_core.{c,h}`, `src/nanoimage_bmp_core.c`, and the new `formal/`
tree. Commit or stage only with explicit authorization.

Plan of record: `/home/syoyo/.opencode/plan/nanoimage-lean-verification.md`.
Status doc: `formal/VERIFICATION.md`. Method doc: `formal/README.md`.

## Where things stand

Phase 0 (infrastructure) is done. Phase 1 (shared leaves) is done. Phase 2
(BMP) is partly done: geometry is fully proven end-to-end
(`ni_bmp_geometry_exs_pos`, `ni_bmp_geometry_exs_neg_intmin`,
`ni_bmp_geometry_exs_neg_normal`); the header signature reject spec lemma and
the layout reject spec lemma are proven; spec-side helpers
(`bmpHeaderCode_*`, `bmpGeometryStage_*`, `bmpGeometryCode_bound`,
`rd16le28_in_set_of_geomOk`, `rowStride_height_le_sizeMax`,
`height_bound_of_geomOk`, `rd32le18_ge1_of_geomOk`) are proven.

Gates, all green at last run:

- `make lean-check` (lake build of `formal/`, then `c2lean.py --check`)
- `make lean-diff` (`formal/tools/cdiff.py --n 300`, 4200 cases)
- `make test`

**`ni_bmp_header_exs` is proven end-to-end and no `sorry` remains anywhere**
(axioms `[propext, Classical.choice, Quot.sound]`). The composition lives in
`NANO/C/Proofs/NiBmpHeaderCompose.lean` (everything after the readers, split into
`ni_bmp_header_geom_call_exs`, `ni_bmp_header_prelude_ok_exs`,
`ni_bmp_header_rem_geom_fail_exs`, `ni_bmp_header_rem_arith_fail_exs`,
`ni_bmp_header_rem_stores_exs`, `ni_bmp_header_rem_palette_bad_exs`,
`ni_bmp_header_palette_call_exs`, `ni_bmp_header_rem_exs`, with
`Gen.ni_bmp_header_rem_stmt`-shaped named defs (`ni_bmp_header_{prelude,arith,palette,stores,rest}_stmt`)).
`NANO/C/Proofs/NiBmpHeader.lean` is a thin dispatcher with the sig/layout gates and
the three readers; the POS-overflow sub-lemma file `NiBmpHeaderPosOvfl.lean` was
deleted (its subject was proven inline in `ni_bmp_header_prelude_ok_exs`).

The kernel deep-recursion wall was broken by **factoring every proof into
separately declared theorems** and citing them opaquely. Any single monolithic
`by` block deep-recurses the kernel regardless of `maxRecDepth`/`maxHeartbeats`.
The same recipe must be applied to `ni_bmp_decode_into`.

## Next steps, in order

1. Prove `ni_bmp_decode_into`. It has nested loops (rows, then pixels) that
   write `out`. Use a row invariant: after row `y`, `out` holds the first `y`
   rows of `bmpPixels`. Factor the per-pixel write into its own function
   first, then prove that function, then the loops.
2. Compose: `ni_load_bmp_from_memory`'s verified part is header then decode.
   State the composed theorem only after 1 is done.

## Lessons from the Phase 1 and 2 work

- Translator constraints (`formal/tools/c2lean.py`): no `goto`, no `&local`,
  no pointer arithmetic (`bytes + k`; use `&bytes[k]` or indices), no
  expression-level calls that write memory (use statement-level assignment
  `x = f(...)` into a pointer field), no varargs or function pointers. Only
  functions listed in `FUNCTIONS` can be called.
- clang's JSON encodes absent `for` children as `{}`. `c2lean.py` now turns
  them into `None` (`_null_empty`) before tagging nodes with `_tu`.
- Proof style that worked: `EvE.var rfl` for locals; `EvE.bin`/`EvE.cast` with
  a small `simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq]`
  or a `rfl`-style rewrite for the arithmetic obligation; `ExS.set (i := n)`
  (the index is not inferable from the hypothesis); `ExS.ite (c := ...)
  (a := ...) (b := ...) (bc := ...)` with explicit branches; `ExS.seq_ret`
  for a returning first statement; `show` to fix the return value before
  `exact`.
- Pitfalls hit: `simp` loops on `Int`/`Nat` cast lemmas (use `rw` or a
  dedicated lemma such as `int_div_two_pow`, `int_mod_two_pow`, `bin_shr_i32`);
  `norm_num` is not available (no Mathlib, use `omega`); `omega` treats
  `2^k` as an atom (add `2^k ≤ 256` facts first); a theorem whose final state
  is claimed unchanged is false once locals are set, so use `∃ s'`.
- Stating the theorem: the header shape is
  `∃ s', ExS Gen.prog ⟨frameLocals ... , m, ro⟩ Gen.<f>.body (.ret (some (.int i32 v))) s'`.

## Known boundaries and open items

- BMP header proof is done; `ni_bmp_decode_into` and the composition
  (`ni_load_bmp_from_memory`'s verified part) are the open Phase 2 work.
  TGA, GIF, PNG, verified inflate, and JPEG are not started.
- `make lean-diff` now also exercises each BMP helper separately
  (`bmp_sig`, `bmp_layout`, `bmp_geometry`, `bmp_mulfits`) in addition to the
  whole-header and decode gates.
- Phase 1 caveat: packed-bit and scale theorems assume PNG-valid depths.
- Possible refinement: the `ni_bmp_decode_into` bounds checks duplicate what
  the header proves. Keep them only if the decode proof needs them.
- xmake target not verified (only Make was run). `xmake.lua` has the new file
  added.
- No CI yet (Phase 9).

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
