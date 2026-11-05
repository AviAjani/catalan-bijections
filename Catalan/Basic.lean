import Mathlib.Combinatorics.Enumerative.DyckWord

/-!
# Trees and balanced words

`Balanced` is the grammar `S ::= ε | (S)S`. The prefix characterization
connects this grammar to the usual definition of balanced parentheses.
-/

namespace Catalan

open DyckStep

abbrev Word := List DyckStep
abbrev FullBinaryTree := Tree Unit

/-- A leaf is empty; an internal node encloses its left subtree, then writes its right. -/
def encode : FullBinaryTree → Word
  | .nil => []
  | .node _ l r => U :: (encode l ++ D :: encode r)

/-- Balanced parentheses, presented by their unambiguous first-return grammar. -/
inductive Balanced : Word → Prop
  | empty : Balanced []
  | node {a b : Word} : Balanced a → Balanced b → Balanced (U :: (a ++ D :: b))

@[simp] theorem encode_nil : encode .nil = [] := rfl

@[simp] theorem encode_node (l r : FullBinaryTree) :
    encode (.node () l r) = U :: (encode l ++ D :: encode r) := rfl

theorem balanced_encode (t : FullBinaryTree) : Balanced (encode t) := by
  induction t with
  | nil => exact .empty
  | node _ _ _ hl hr => exact .node hl hr

@[simp] theorem count_open_encode (t : FullBinaryTree) :
    (encode t).count U = t.numNodes := by
  induction t <;> simp [encode, *, Nat.add_comm]

@[simp] theorem length_encode (t : FullBinaryTree) :
    (encode t).length = 2 * t.numNodes := by
  induction t with
  | nil => rfl
  | node _ _ _ hl hr =>
    simp only [encode, List.length_cons, List.length_append, hl, hr, Tree.numNodes]
    omega

/-- The grammar implies the equal-count and nonnegative-prefix conditions. -/
theorem Balanced.prefix {w : Word} (h : Balanced w) :
    w.count U = w.count D ∧ ∀ k, (w.take k).count D ≤ (w.take k).count U := by
  induction h with
  | empty => simp
  | @node a b _ _ ha hb =>
    let p : DyckWord := ⟨a, ha.1, ha.2⟩
    let q : DyckWord := ⟨b, hb.1, hb.2⟩
    have e : (p.nest + q).toList = U :: (a ++ D :: b) := by
      simp [DyckWord.nest, p, q, HAdd.hAdd, Add.add, List.append_assoc]
    rw [← e]
    exact ⟨(p.nest + q).count_U_eq_count_D, (p.nest + q).count_D_le_count_U⟩

/-- First-return decomposition proves that the prefix conditions generate the grammar.
Only mathlib's decomposition lemmas are used here, not its tree bijection. -/
theorem balanced_dyckWord (p : DyckWord) : Balanced p.toList := by
  by_cases h : p = 0
  · subst p
    exact .empty
  · have hi := DyckWord.semilength_insidePart_lt h
    have ho := DyckWord.semilength_outsidePart_lt h
    have b := Balanced.node (balanced_dyckWord p.insidePart) (balanced_dyckWord p.outsidePart)
    have e : (p.insidePart.nest + p.outsidePart).toList =
        U :: (p.insidePart.toList ++ D :: p.outsidePart.toList) := by
      simp [DyckWord.nest, HAdd.hAdd, Add.add, List.append_assoc]
    rw [← e, DyckWord.nest_insidePart_add_outsidePart h] at b
    exact b
termination_by p.semilength

theorem balanced_iff_prefix (w : Word) :
    Balanced w ↔ w.count U = w.count D ∧
      ∀ k, (w.take k).count D ≤ (w.take k).count U := by
  constructor
  · exact Balanced.prefix
  · rintro ⟨he, hp⟩
    exact balanced_dyckWord ⟨w, he, hp⟩

theorem Balanced.length_eq_two_mul_count {w : Word} (h : Balanced w) :
    w.length = 2 * w.count U := by
  let p : DyckWord := ⟨w, h.prefix.1, h.prefix.2⟩
  exact (DyckWord.two_mul_semilength_eq_length (p := p)).symm

end Catalan
