# nanoimage formal verification — status

Scope: loading path only (`ni_load_{png,jpeg,bmp,tga,gif}_from_memory`).
Writers, the row-callback APIs, the allocator shell, and SIMD dispatch are out
of scope. See `formal/README.md` for the method.

## Gates

| Gate | Command | Status |
|---|---|---|
| Lean build | `make lean-check` (`cd formal && lake build`) | green; **no `sorry` anywhere** — `ni_bmp_header_exs` is fully proven (`NANO/C/Proofs/NiBmpHeaderCompose.lean` for everything after the readers, `NANO/C/Proofs/NiBmpHeader.lean` for the top-level sig/layout gates) |
| Translator up to date | `python3 formal/tools/c2lean.py --check` | green |
| Three-way differential (C under ASan/UBSan == MiniC == Lean spec) | `make lean-diff` (`formal/tools/cdiff.py --n 300`) | green, 4200 cases, 0 mismatches |
| Unit tests | `make test` | green |

Axioms (`#print axioms`): every proven theorem depends only on the standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).
No `native_decide`, no `bv_decide`.

## Phase status

| Phase | Item | State |
|---|---|---|
| 0 | MiniC semantics, logic, Hoare rules, lemmas ported (`NANO.C.*`) | done |
| 0 | `c2lean.py` retargeted to `src/nanoimage_core.c` (per-TU layout probes) | done |
| 0 | `cdiff` harness (`CDiff.lean`, `tools/cdiff_c.c`, `tools/cdiff.py`) | done |
| 1 | Core helpers in `src/nanoimage_core.{c,h}` (readers, size math, clamp, scale, packed bits, paeth) | done |
| 1 | Differential checks for all helpers | done |
| 1 | Proofs: `ni_read_u16le/u32le/i32le/u16be/u32be` | done |
| 1 | Proofs: `ni_size_mul`, `ni_size_add` (success and overflow branches) | done |
| 1 | Proofs: `ni_clamp_u8`, `ni_scale_to_8bit` (both branches), `ni_read_packed_bits`, `ni_paeth` | done |
| 2 | BMP core/shell split (`src/nanoimage_bmp_core.c`, `ni_bmp_header` + `ni_bmp_decode_into`) | done |
| 2 | BMP spec (`NANO/Bmp.lean`, `bmpHeader`, `bmpPixels`) | done |
| 2 | BMP differential check (C == MiniC == spec, incl. mutation control) | done, green |
| 2 | BMP signature check `ni_bmp_sig_ok` (split out of the header) | proven (`NANO/C/Proofs/Bmp.lean`) |
| 2 | BMP layout check `ni_bmp_layout_ok` (pixel offset and DIB size guards) | proven (`NANO/C/Proofs/Bmp.lean`) |
| 2 | `bmpHeaderCode_one_of_not_sigOk` and `sigOk_guard_false_of_sigOk` (spec helpers behind the header rejects) | proven (`NANO/C/Proofs/NiBmpHeaderSpec.lean`, `NANO/C/Proofs/NiBmpHeaderSpecSig1.lean`) |
| 2 | BMP refinement proof for `ni_bmp_header` (`ni_bmp_header_exs`): mem survives all stores, returns `bmpHeaderCode size d`; sig/layout/geometry/arith/palette stages all split into standalone lemmas (`NiBmpHeaderCompose.lean`) | proven — axioms `propext`/`Classical.choice`/`Quot.sound` |
| 2 | BMP refinement proof for `ni_bmp_decode_raw_pixel` (`ni_bmp_decode_raw_pixel_exs`, `NiBmpDecode.lean`): BGR(A) splice of 3–4 palette-expansion bytes, channels branch for 4-byte alpha; byte-level bridge lemmas (`splice_enc_*`, `byteAt_toUInt8`, `encodeLE_one_byteAt`) | proven — axioms `propext`/`Classical.choice`/`Quot.sound` |
| 2 | BMP refinement proof for `ni_bmp_decode_indexed_pixel` (`ni_bmp_decode_indexed_pixel_ok_exs` returns 0 and writes BGR from palette in-range; `ni_bmp_decode_indexed_pixel_err_exs` returns 11 and writes nothing out-of-range; both export `s'.mem bd = some d` and `s'.mem 2 = m 2` for loop composition) | proven — axioms `propext`/`Classical.choice`/`Quot.sound` |
| 2 | BMP refinement proof for the inner 8-bit/row decode loop (`loop0_iter` induction over `h.width - x` in `NiBmpLoop.lean`; terminates at `.brk` at `width` with `y+1` rows stored; `ni_bmp_decode_into_loop0_ok_exs` wrapper) | proven — axioms `propext`/`Classical.choice`/`Quot.sound` |
| 2 | Spec bridge lemmas for the decode proof (`flatMap_range_prefix`, `flatten_map'`, `flatten_flatMap'`, `rowOut`/`rowOut_width`/`rowOut_length`/`rowOut_prefix`, `bmpPixel_palette`, `bmpPixel_direct`, `bmpPixel_8bit_length`, `bmpPixel_8bit_ok`, `bmpPixel_idx_lt_entries_of_ok`, `bmpPixels_eq_rowsBytes`, `mapM_row_ok`, `mapM_rows_ok`, `bmpRowsBytes_succ_flat`; in `Bmp.lean`) | proven |
| 2 | BMP refinement proofs for `ni_bmp_decode_into` (outer y-loop, 24/32-bit direct loops, and the `bit_count == 8` vs else split) | **proven** (`ni_bmp_decode_into_ok_exs`, `NiBmpDecodeInto.lean` — all-pixels-OK case, axioms `propext`/`Classical.choice`/`Quot.sound`; the composition consumes `loop1_iter`/`loop3_iter` directly with pointwise state hypotheses) |
| 2 | `ExS.call_ret` (statement-level call of a value-returning function: result discarded, caller continues; in `Logic.lean`) | proven |
| 2 | Header info-block exports: `bmpHeadBlock`/`bmpHeaderFinalBlock` constructors, `header_stores_exs` memory export, guarded exports through `ni_bmp_header_rem_stores_exs` / `ni_bmp_header_rem_exs` / `ni_bmp_header_exs` (success ⇒ info object holds `bmpHeaderFinalBlock d gout`) | proven (`NiBmpHeaderCompose.lean`, `NiBmpHeader.lean`) |
| 2 | Final-info-block field slices (10 fields + length), layered per store stage (`arithBlock_*`, `palBlock_*`, `headBlock_*`) | proven (`NiBmpLoad.lean`) |
| 2 | Spec witness + reconstruction: `bmpHeaderInfoOf d`, `bmpHeader_ok_of_stages` (five stage verdicts ⇒ `bmpHeader size d = .ok (bmpHeaderInfoOf d)`, via `bmpOutputCompose_ok_8`/`_ne8`) | proven (`NiBmpLoad.lean`) |
| 2 | Composition `ni_bmp_load_exs` (header fid 15 then decode fid 16, as the shell runs them) | **in progress** — remaining: restate `ni_bmp_decode_into_ok_exs` over the 5-param call frame (drop the over-strong `locals 25 = some 0` invariant from `loop2_iter`/`loop3_iter`; local 25 is write-before-read), then assemble with `ExS.call_dst`/`ExS.call_ret` |
| 2 | `ni_bmp_geometry_readers` proven (closed-form state with locals 3..7 set) | done |
| 2 | `ni_bmp_mul_fits_exs` proven | done |
| 2 | `ni_bmp_geometry_exs` reject-3 by_cases (widthI<=0, hI=0, planes!=1 → ret3) | done |
| 2 | `ni_bmp_geometry_exs` POS branch (`height_i ≥ 0`) — storage chain + `.set 11/9` cast breakthrough via `cast_u32_i32`; success path stores 5 fixed-offset u32/u16/u8 into ni_bmp_info; returns 0 | proven (`ni_bmp_geometry_exs_pos`) |
| 2 | `ni_bmp_geometry_exs` NEG branch with INTMIN (`height_i == INT32_MIN` → ret4) | proven (`ni_bmp_geometry_exs_neg_intmin`) |
| 2 | `ni_bmp_geometry_exs` NEG branch (`height_i < 0`, `height_i != INT32_MIN`) — deep `.ite` body, kernel deterministic timeout | proven (`NANO/C/Proofs/NiGeometryNegNormal.lean`, `ni_bmp_geometry_exs_neg_normal`) |
| 2 | `tail_exs` (in `NANO/C/Proofs/NiGeometryTail.lean`) — post-LT unverified-store-chain; by_cases on compression=0 vs≠0 and bit_count in {8,24,32} vs invalid; final `.set 10` (channels) then 5 stores at offsets 24/28/40/42/43; returns 0 | proven |
| 2 | `bmp_stores_exs` (in `NANO/C/Proofs/NiGeometryTail.lean`) — the 5 stores against an arbitrary `obl` of length 48, with signatures for by-field-`encodeLE` splices | proven components |
| 2 | `ni_bmp_header` composition: the kernel-deep-recursion problem was solved by factoring the entire post-reader pipeline into standalone lemmas — `ni_bmp_header_geom_call_exs`, `ni_bmp_header_prelude_ok_exs` (geometry OK through the six field loads), and the four outcome decls (`ni_bmp_header_rem_geom_fail_exs`, `ni_bmp_header_rem_arith_fail_exs`, `ni_bmp_header_rem_stores_exs`, `ni_bmp_header_rem_palette_bad_exs`) plus the `ni_bmp_header_palette_call_exs` helper; `ni_bmp_header_rem_exs` dispatches; `NiBmpHeader.lean` composes it with the sig/layout gates and the `.call 1` readers | proven (`NiBmpHeaderCompose.lean`, `NiBmpHeader.lean`) — `propext`/`Classical.choice`/`Quot.sound` |
| 2 | Spec-side header helpers `bmpHeaderCode_one_of_not_sigOk`, `bmpHeaderCode_two_of_not_layoutOk`, `bmpHeaderCode_seven_of_geomOk`, `bmpHeaderCode_nine_of_trunc`, `bmpHeaderCode_ten_of_palette`, `bmpHeaderCode_zero_of_ok` (in `NiBmpHeaderSpec.lean`) | proven |
| 2 | Spec-side geometry helpers `bmpGeometryStage_eq_of_ne_zero`, `bmpGeometryStage_ok_of_zero`, `bmpGeometryCode_bound`, `rd16le28_in_set_of_geomOk`, `rd32le18_ge1_of_geomOk`, `height_bound_of_geomOk`, `rowStride_height_le_sizeMax`, `sizeMulOK_true_of_mulLE`, `sizeMulOK_false_of_notFit`, `bmpOutputCompose_seven`, `bmpOutputCompose_nine` (in `NiBmpHeaderSpecGeo.lean`) | proven |
| 2 | Spec-side palette helpers `paletteEntriesUsed`, `paletteEntriesUsed_eq_of_ne_zero`, `bmpOutputCompose_ten`, `bmpOutputCompose_zero_ne8`, `bmpOutputCompose_ok_8` (in `NiBmpHeaderSpecPalette.lean`) | proven |
| 2 | Header-load helpers `readBytes_drop_ok`, `load_u32_field_of_geom`, `load_u16_field_of_geom`, `load_u8_field_of_geom`, `decodeLE_of_lt` (in `NiBmpHeaderLoads.lean`) | proven |
| 2 | Header tail-arith helpers `trunc_check_skip`, `trunc_check_fire_condA/B`, `set_twelve_mul`, `set_twelve_mul2`, `set_eleven_rowstride`, `mulfits2_ite_skip`, `mulfits3_ite_skip`, `mulfits4_ite_skip`, `hMulFits2/3/4`, `fits{2,3,4}_proof`, `set_twelve_mul`, `set_eleven_rowstride`, `bin_u64_add_wrap`, `u16_u64_cast`, `bin_u64_sub`, `eval_row_stride` (in `NiBmpHeaderTail.lean`) | proven |

| 3 | TGA | not started |
| 4 | GIF | not started |
| 5 | PNG container (inflate is an oracle until phase 6) | not started |
| 6 | Verified DEFLATE / zlib, default switch | not started |
| 7 | JPEG (integer IDCT, verified pipeline) | not started |
| 8 | Composition theorems | not started |
| 9 | Assurance docs / CI | partially (gates in Makefile; CI not yet) |

Phase 2 also fixed a C defect found while writing the spec: the BMP header
compared `pixel_offset < 14u + dib_size` in `uint32_t`, which wraps for
`dib_size` near `UINT32_MAX` on inputs larger than 4 GiB. The core now compares
in `size_t`.

## Proven theorems

In `formal/NANO/C/Proofs/Core.lean`:

* `ni_read_u16le_exs`, `ni_read_u32le_exs`, `ni_read_i32le_exs`,
  `ni_read_u16be_exs`, `ni_read_u32be_exs`: for every block `d` and in-bounds
  offset, the translated function terminates without UB, returns the
  little/big-endian value of `d` at the offset, and writes nothing.
* `ni_size_mul_exs_ok` / `ni_size_mul_exs_fail`: `ni_size_mul` returns 1 and
  stores `a*b` exactly when no `uint64_t` overflow occurs, otherwise returns 0
  and leaves the output untouched.
* `ni_size_add_exs_ok` / `ni_size_add_exs_fail`: the same for `ni_size_add`.
* `ni_clamp_u8_exs`: returns `clampU8 v` (clamp to `[0, 255]`) for every
  `int` argument.
* `ni_read_packed_bits_exs`: for PNG depths `bd ∈ {1, 2, 4, 8}` and an
  in-row pixel index, returns `packedBits row p bd`; the caller must supply
  the in-bounds byte index as a hypothesis (out-of-row loads are UB).
* `ni_scale_to_8bit_exs_ok`: for `1 ≤ bd ≤ 8`, returns 1, writes the scaled
  byte at `out[0]`, and leaves the rest of the buffer intact.
  `ni_scale_to_8bit_exs_fail`: for `bd = 0` or `8 < bd < 256`, returns 0 and
  writes nothing.
* `ni_paeth_exs`: returns `paeth a b c` (PNG Paeth predictor) for all byte
  inputs.

Every theorem above depends only on `propext`, `Quot.sound`, and (for some)
`Classical.choice`.

## BMP (Phase 2) differential evidence

`make lean-diff` (seed 1, n = 300) runs 3900 cases, of which 600 are BMP
(`bmp_header` and `bmp_decode` for 300 generated files). `--n 400 --seed 2`
runs 5200 cases. Both report 0 mismatches. Generator: `formal/tools/cdiff.py`
(valid and malformed headers; 8/24/32 bpp plus invalid depths; top-down and
bottom-up; palettes with out-of-range indices; truncation; byte flips). A
mutation control (`dib < 41` in the spec) produces 94 mismatches, so the gate
is sensitive to spec drift. Outcome distribution on 300 files: 215 success,
the rest spread over codes 1 to 11.

## Module organization (Phase 2 BMP core)

The BMP core proofs are split so that each file elaborates within the
local kernel's depth/heartbeat budget:

* `NANO.C.Proofs.Bmp` — signature/layout checks, `ni_bmp_mul_fits_exs`, and the
  composite `ni_bmp_geometry_exs` (reject-3 dispatch + the three sign cases).
* `NANO.C.Proofs.NiGeometryTail` — `store_field_u{8,16,32}`, `ptrAddN_ok`,
  `bmp_stores_exs`, `tail_exs` (the post-`height`-branch store chain),
  `wrap_i32_lt`, `ev_ptr_const`, `ev_byte_const`.
* `NANO.C.Proofs.NiGeometryPos` — `ni_bmp_geometry_readers`,
  `ni_bmp_geometry_exs_pos`, `ni_bmp_geometry_exs_neg_intmin`.
* `NANO.C.Proofs.NiGeometryNegNormal` — `ni_bmp_geometry_exs_neg_normal`.
* `NANO.C.Proofs.NiBmpDecode` — the per-pixel decode proofs
  (`ni_bmp_decode_raw_pixel_exs`, `ni_bmp_decode_indexed_pixel_{ok,err}_exs`),
  plus `mem_upd_other`, `mem_upd_eq`, `mem_upd_neq` and the
  `splice_enc_*` splice normalizations.
* `NANO.C.Proofs.NiBmpLoop` — parameterized field-load lemmas
  (`load_u{8,16,32,64}_field` on arbitrary blocks), the `loop0_iter`
  induction over the 8-bit inner row loop and the
  `ni_bmp_decode_into_loop0_ok_exs` wrapper; `ExS.loop_next`'s local-state
  invariant is threaded through `locals_upd_extract` chains.

Kernel notes (no `unsafe`, no `native_decide`):

* An inline proof of the `.un .neg` arithmetic (a proof-term with two dozen
  `IntTy` wrap/unwrap nodes) exceeded the kernel's elaboration budget even at
  `maxRecDepth = 10^9`. The fix was to hoist the fact into the shared library
  as `NANO.C.evalUnNegI32` (with `NANO.C.inRange_i32_split`), so the
  executional equation is a single constant application at the use site.
* `ni_bmp_geometry_exs_neg_normal` additionally needed `hRangeNeg` proved
  without `simp` recursion; it uses `decide (..)` witnesses and
  `Bool.and_eq_true` + `decide_eq_true_eq` rewrites only.
* `wsimp` (the MiniC `simp` wrapper) is defined once in
  `NANO.C.Proofs.NiGeometryTail`; all modules import it via that path.

## Known gaps and boundaries

* Phase 1 is complete: all helpers listed above are proven.
* Phase 2 has the BMP core, spec, differential gate, geometry check, header,
  per-pixel helpers, all four decode loops, and the top-level decode
  composition proven end-to-end: `ni_bmp_decode_into_ok_exs`
  (`NiBmpDecodeInto.lean`) covers the all-pixels-OK case of
  `ni_bmp_decode_into` — no UB, returns 0, and the output block holds the
  flattened `bmpRowsBytes` bytes — with axioms
  `[propext, Classical.choice, Quot.sound]`. The proof consumes
  `loop1_iter`/`loop3_iter` directly (pointwise state hypotheses), so no
  frame-bridging was needed.
* Header/decode composition (`ni_bmp_load_exs`, `NiBmpLoad.lean`): the
  header-side exports are proven (the info object holds `bmpHeaderFinalBlock`
  after a successful `ni_bmp_header`, with all ten field encodings derived,
  and `bmpHeader_ok_of_stages` reconstructs the spec verdict), and
  `ExS.call_ret` composes value-returning statement calls. The remaining
  step is restating `ni_bmp_decode_into_ok_exs` over the 5-parameter call
  frame: the loop iter theorems carry an over-strong
  `locals 25 = some 0` invariant (local 25 is written before it is ever
  read), which a fresh call frame — where locals ≥ 5 are unbound — cannot
  supply. Dropping that invariant from `loop2_iter`/`loop3_iter` and
  restating the decode theorem is mechanical; the composite assembly
  (`ExS.call_dst` for the header call, the verdict `ite`, `ExS.call_ret`
  for the decode call) is already specified.
* `ni_bmp_header_exs` composition note: the final theorem was assembled only
  after factoring the whole post-reader pipeline into standalone lemmas,
  because the monolithic term deep-recursed the Lean kernel even at
  `maxRecDepth = 2×10⁹`. The same technique now applies to
  `ni_bmp_decode_into`.
* `ni_read_packed_bits` and `ni_scale_to_8bit` are proven under PNG-valid
  bit depths (1, 2, 4, 8 for packed bits; 1..8 for scaling). Other depths are
  not a valid PNG input, so the theorems do not state a result for them.
* The `ni_read_*` theorems take a `d.length < 2^64` hypothesis and in-bounds
  offsets; out-of-bounds reads are UB in C and excluded by the precondition.
* The trusted base is the Lean kernel, the MiniC semantics
  (`formal/NANO/C/Semantics.lean`), the translator `formal/tools/c2lean.py`,
  clang's AST, and the LP64 little-endian layout.
