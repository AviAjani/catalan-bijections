import Catalan.Parser

/-! # The bijection, with and without a size constraint -/

namespace Catalan

open DyckStep

/-- Extract the certified parser result for a balanced word. -/
def ofBalanced (w : Word) (hw : Balanced w) : FullBinaryTree :=
  match h : decode w with
  | some t => t
  | none => False.elim ((decode_eq_none_iff w).mp h hw)

@[simp] theorem encode_ofBalanced (w : Word) (hw : Balanced w) :
    encode (ofBalanced w hw) = w := by
  unfold ofBalanced
  split
  · rename_i t h
    exact encode_of_decode h
  · rename_i h
    exact False.elim ((decode_eq_none_iff w).mp h hw)

@[simp] theorem ofBalanced_encode (t : FullBinaryTree) :
    ofBalanced (encode t) (balanced_encode t) = t := by
  apply encode_injective
  exact encode_ofBalanced _ _

/-- Full binary trees correspond to balanced parenthesis words. -/
def treeWordEquiv : FullBinaryTree ≃ {w : Word // Balanced w} where
  toFun t := ⟨encode t, balanced_encode t⟩
  invFun w := ofBalanced w.val w.property
  left_inv := ofBalanced_encode
  right_inv w := Subtype.ext (encode_ofBalanced w.val w.property)

abbrev TreeAt (n : Nat) := {t : FullBinaryTree // t.numNodes = n}
abbrev WordAt (n : Nat) := {w : Word // Balanced w ∧ w.count U = n}

theorem numNodes_ofBalanced (w : Word) (hw : Balanced w) :
    (ofBalanced w hw).numNodes = w.count U := by
  rw [← count_open_encode, encode_ofBalanced]

/-- The equivalence restricts to `n` internal nodes and `n` pairs. -/
def sizedEquiv (n : Nat) : TreeAt n ≃ WordAt n where
  toFun t := ⟨encode t.val, balanced_encode t.val, by simp [t.property]⟩
  invFun w := ⟨ofBalanced w.val w.property.1, by
    rw [numNodes_ofBalanced, w.property.2]⟩
  left_inv t := Subtype.ext (ofBalanced_encode t.val)
  right_inv w := Subtype.ext (encode_ofBalanced w.val w.property.1)

theorem length_wordAt {n : Nat} (w : WordAt n) : w.val.length = 2 * n := by
  rw [w.property.1.length_eq_two_mul_count, w.property.2]

end Catalan
