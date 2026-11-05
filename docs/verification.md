# Local verification

Verified on Windows with Lean 4.24.0 and the mathlib revision pinned in
`lake-manifest.json`.

| Check | Result |
|---|---|
| `lake build --wfail` | Passed: library, proof examples, and native executable built successfully. |
| `lake env lean Audit.lean` | Passed: 150 declarations checked against the standard axiom allowlist. |
| `lake exe catalan-demo` | Passed: enumeration counts, word listing, accepted inputs, and rejected inputs ran successfully. |
| `lake exe catalan-demo parse '(())'` | Returned `[[. .] .]`, two internal nodes, exit code 0. |
| `lake exe catalan-demo parse '())('` | Rejected input, exit code 1. |
| `lake exe catalan-demo list 3` | Listed exactly the five three-pair words in lexical order. |

The executable reported these enumeration counts alongside the corresponding
Catalan numbers:

```text
n  enumerated  Catalan
0  1           1
1  1           1
2  2           2
3  5           5
4  14          14
5  42          42
6  132         132
7  429         429
8  1430        1430
```

The audit checks `propext`, `Classical.choice`, and `Quot.sound` as the only
allowed axioms. The printed dependencies of the round-trip, prefix acceptance,
size equivalence, and cardinality results all lie within that allowlist.

These results describe the local check. GitHub Actions verifies each pushed commit separately.
