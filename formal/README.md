# nanoimage — formal verification of the loading path

Lean 4 (v4.35.0, no mathlib) formalization of the nanoimage image loaders.
The method follows `tinygltf/formal`: the C is translated mechanically into a
MiniC deep embedding, the translated code is proven to refine a Lean
specification, and a three-way differential test checks the translator and
the semantics against the real compiled C.

Status and the list of proven theorems: [VERIFICATION.md](VERIFICATION.md).

## Layout

| Path | Contents |
|---|---|
| `NANO/Basic.lean` | byte-string readers (LE/BE 16/32/64) |
| `NANO/Spec.lean` | specifications of the Phase 1 helpers |
| `NANO/C/Semantics.lean` | MiniC: values, byte-addressed memory, executable big-step semantics with explicit UB |
| `NANO/C/Logic.lean`, `Hoare.lean`, `Lemmas.lean` | proof rules (`EvE`, `ExS`, triples) and arithmetic/byte lemmas |
| `NANO/C/Gen.lean` | **generated** from `src/nanoimage_core.c` by `tools/c2lean.py` — do not edit |
| `NANO/C/Proofs/Core.lean` | refinement proofs for the Phase 1 helpers |
| `CDiff.lean`, `tools/cdiff_c.c`, `tools/cdiff.py` | three-way differential driver |
| `tools/c2lean.py` | clang-AST → MiniC translator (rejects anything outside the subset) |

## Workflow

```sh
make lean-check   # lake build + c2lean --check
make lean-diff    # C (ASan/UBSan) == MiniC == Lean spec on random inputs
```

After changing a function in `src/nanoimage_core.c`:

1. `python3 formal/tools/c2lean.py` (regenerates `NANO/C/Gen.lean`);
2. `cd formal && lake build` — proofs fail where the generated code changed;
3. `make lean-diff`.

## Rules

* The verified core is `src/nanoimage_core.c` (and per-format core files as
  they are split out). It must not use allocation, varargs, function
  pointers, or floating point. The translator rejects these.
* Specs live in `NANO/`, MiniC in `NANO/C/`, and generated code is never
  edited by hand.
* No `sorry`, no `native_decide`, and no axioms beyond the standard three.
  (For the current BMP header state, see VERIFICATION.md: the POS/NEG
  branches in `NANO/C/Proofs/NiBmpHeader.lean` are sorried while the
  kernel deep-recursion wall is worked through.)
