# Catalan Bijections

Full binary trees, balanced parentheses, and Catalan counting in Lean 4.
Includes an executable parser with proved inverse laws and a size-preserving
bijection: trees with `n` internal nodes correspond to balanced words with `n`
pairs, giving the count `C_n = choose(2n, n) / (n + 1)`.

The encoding is:

```text
encode(leaf)       = ""
encode(node(l,r))  = "(" ++ encode(l) ++ ")" ++ encode(r)
```

Left and right children are ordered. For example, `[[. .] .]` encodes `(())`,
while `[. [. .]]` encodes `()()`; `.` denotes a leaf.

## Build and run

Install [Lean through elan](https://lean-lang.org/install/) and Git, then run:

```sh
lake update
lake exe cache get
lake build --wfail
lake env lean Audit.lean
lake exe catalan-demo
lake exe catalan-demo list 3
lake exe catalan-demo parse '(()())()'
```

Lean and mathlib are pinned to **4.24.0**; `lake-manifest.json` locks every
dependency. Open the folder in VS Code with the recommended Lean 4 extension.

The parser accepts only `(` and `)`. Unbalanced input and other characters are
rejected. The empty string encodes a leaf. Listing is capped at nine pairs.

## Main results

All declarations are in namespace `Catalan`.

| Declaration | Result |
|---|---|
| `balanced_iff_prefix` | The grammar agrees with equal counts and nonnegative prefix balance. |
| `decode_encode`, `encode_of_decode` | Encoding and successful parsing are inverses. |
| `decode_iff_prefix` | The parser accepts exactly the balanced words. |
| `Balanced.unique_split` | Inside/outside decomposition is unique. |
| `sizedEquiv n` | An explicit bijection preserving the number of pairs. |
| `mem_words`, `card_wordAt_closedForm` | Complete enumeration and the Catalan cardinality formula. |

The proofs hold for every `n`. Enumeration is intended for small examples;
no time-complexity bound is formalized.

## Implementation

The repository implements its own list encoder, fuel-based parser, inverse
proofs, and string interface. It reuses mathlib's tree type, Dyck steps,
first-return decomposition, tree enumeration, and Catalan counting results.
Mathlib also has an existing abstract Dyck-word/tree equivalence; the parser
proofs here do not invoke it. See the pinned upstream
[Catalan](https://github.com/leanprover-community/mathlib4/blob/f897ebcf72cd16f89ab4577d0c826cd14afaafc7/Mathlib/Combinatorics/Enumerative/Catalan.lean)
and [DyckWord](https://github.com/leanprover-community/mathlib4/blob/f897ebcf72cd16f89ab4577d0c826cd14afaafc7/Mathlib/Combinatorics/Enumerative/DyckWord.lean)
modules.

The build checks the library, executable, and concrete proof examples. The
axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
GitHub Actions runs the build, audit, and executable examples.

[Proof guide](docs/proof-guide.md) · [Local checks](docs/verification.md) · [Apache 2.0](LICENSE)
