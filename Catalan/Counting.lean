import Catalan.Bijection

/-!
# Enumeration and Catalan cardinalities

Mathlib supplies the finite enumeration of trees and its Catalan count.
Injectivity and surjectivity of our encoding transport that count to words.
-/

namespace Catalan

open DyckStep

/-- All full binary trees with `n` internal nodes, from mathlib. -/
def trees (n : Nat) : Finset FullBinaryTree := Tree.treesOfNumNodesEq n

/-- Enumerate balanced words without repetitions by encoding the tree enumeration. -/
def words (n : Nat) : Finset Word := (trees n).image encode

@[simp] theorem mem_trees {t : FullBinaryTree} {n : Nat} :
    t ∈ trees n ↔ t.numNodes = n := Tree.mem_treesOfNumNodesEq

/-- The enumerator includes exactly the balanced words with `n` pairs. -/
@[simp] theorem mem_words {w : Word} {n : Nat} :
    w ∈ words n ↔ Balanced w ∧ w.count U = n := by
  constructor
  · intro h
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
    exact ⟨balanced_encode t, by simpa using (mem_trees.mp ht)⟩
  · rintro ⟨hb, hn⟩
    obtain ⟨t, rfl⟩ := hb.exists_encoding
    apply Finset.mem_image.mpr
    exact ⟨t, mem_trees.mpr (by simpa using hn), rfl⟩

theorem card_words (n : Nat) : (words n).card = catalan n := by
  rw [words, Finset.card_image_of_injective _ encode_injective]
  exact Tree.treesOfNumNodesEq_card_eq_catalan n

theorem card_words_closedForm (n : Nat) :
    (words n).card = Nat.centralBinom n / (n + 1) := by
  rw [card_words, catalan_eq_centralBinom_div]

/-- Identify the size-constrained tree subtype with mathlib's finite set. -/
def treeAtFinsetEquiv (n : Nat) : TreeAt n ≃ ↥(trees n) where
  toFun t := ⟨t.val, mem_trees.mpr t.property⟩
  invFun t := ⟨t.val, mem_trees.mp t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (n : Nat) : Fintype (TreeAt n) :=
  Fintype.ofEquiv ↥(trees n) (treeAtFinsetEquiv n).symm

instance (n : Nat) : Fintype (WordAt n) :=
  Fintype.ofEquiv (TreeAt n) (sizedEquiv n)

theorem card_treeAt (n : Nat) : Fintype.card (TreeAt n) = catalan n := by
  rw [Fintype.card_congr (treeAtFinsetEquiv n), Fintype.card_coe]
  exact Tree.treesOfNumNodesEq_card_eq_catalan n

/-- There are exactly `Cₙ` balanced parenthesis words with `n` pairs. -/
theorem card_wordAt (n : Nat) : Fintype.card (WordAt n) = catalan n := by
  rw [← Fintype.card_congr (sizedEquiv n), card_treeAt]

theorem card_wordAt_closedForm (n : Nat) :
    Fintype.card (WordAt n) = Nat.choose (2 * n) n / (n + 1) := by
  rw [card_wordAt, catalan_eq_centralBinom_div]
  rfl

end Catalan
