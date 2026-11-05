# How the proof works

## 1. Fix the objects

`FullBinaryTree` abbreviates mathlib's `Tree Unit`. The `nil` constructor is a
leaf, while `node () l r` is an internal node with two children. The unit label
carries no information. The left/right order remains significant.

A `Word` is a list over `DyckStep.U` and `DyckStep.D`, rendered as opening and
closing parentheses. `Balanced` is an inductive proposition with two rules:

```text
Balanced []
Balanced a → Balanced b → Balanced (U :: (a ++ D :: b))
```

This definition records a derivation of grammatical balance. It does not merely
assert that some tree encodes the word. `balanced_iff_prefix` independently
connects it to the familiar condition on counts in every prefix. The reverse
direction uses mathlib's first-return decomposition and induction on semilength.

## 2. Encode a tree

The encoding follows the grammar. A leaf contributes no tokens. A node contributes
one matching pair surrounding its left child's encoding, followed by its right
child's encoding. Structural induction proves balance, the number of opening
tokens, and the length formula `length (encode t) = 2 * numNodes t`.

## 3. Parse with a delimiter

The internal parser returns a tree and an unconsumed suffix. On empty input or
an initial closing parenthesis, it returns a leaf without consuming the delimiter.
On an opening parenthesis, it parses the inside, consumes the required closing
parenthesis, then parses the outside. A missing closing parenthesis is an error.

Explicit fuel makes recursion structural. The key completeness lemma is stronger
than a top-level round trip: `parse_encode` handles an encoded tree followed by
either an end delimiter or a closing delimiter. It works whenever the fuel is
strictly greater than the number of internal nodes. Both child trees satisfy the
smaller recursive fuel bound.

`decode` supplies `word.length + 1` units of fuel and requires the entire input to
be consumed. The encoding length theorem shows this fuel is sufficient.

## 4. Prove both directions

`parse_sound` proves that a successful parse has consumed exactly the encoding of
its returned tree. Requiring an empty suffix gives `encode_of_decode`.

The delimiter lemma gives `decode_encode`. Applying `decode` to an equality of
encodings then proves the encoder injective. Induction on a `Balanced` derivation
shows that every grammatical word is an encoding, which gives parser completeness.
Together these results show that malformed words are rejected and that accepted
words have a unique tree.

The same injectivity argument proves `Balanced.unique_split`: two grammatical
inside/outside decompositions of one nonempty word must have identical parts.

## 5. Restrict by size and count

`treeWordEquiv` packages the inverse laws as a Lean equivalence. Its inverse
extracts the parser result using a balance proof; no arbitrary tree is chosen.
`sizedEquiv n` restricts it to `n` internal nodes and `n` opening tokens. Balance
ensures there are also `n` closing tokens, so these are words of length `2 * n`.

The executable enumerator images mathlib's finite tree enumeration under `encode`.
`mem_words` proves both completeness and the size condition. Injectivity prevents
different trees from collapsing to one word, so `card_words` transports mathlib's
tree count. The subtype cardinality theorem expresses the same result independently
of the particular enumeration. Finally, mathlib's Catalan closed form supplies
the binomial expression.

## Reading the Lean files

Start with the definitions and size lemmas in `Basic.lean`, then read
`parse_encode` and `parse_sound` in `Parser.lean`. `Bijection.lean` packages those
results rather than introducing another algorithm. `Counting.lean` shows precisely
where imported enumeration and Catalan results enter the argument.

`Examples.lean` demonstrates the public API on concrete trees and malformed
strings. `Audit.lean` checks axiom dependencies of the project declarations;
the ordinary build checks that all proof terms elaborate and type-check.
