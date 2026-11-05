import Catalan.Counting
import Catalan.Text

/-!
# Small, kernel-checked regression examples

These examples exercise the executable definitions with `decide`, not
external evaluation or unchecked native computation.
-/

namespace Catalan.Examples

open DyckStep

def cherry : FullBinaryTree := .node () .nil .nil
def leftComb : FullBinaryTree := .node () cherry .nil
def rightComb : FullBinaryTree := .node () .nil cherry

example : render (encode cherry) = "()" := by decide
example : render (encode leftComb) = "(())" := by decide
example : render (encode rightComb) = "()()" := by decide

example : readTree "" = some .nil := by decide
example : readTree "(())" = some leftComb := by decide
example : readTree "()()" = some rightComb := by decide
example : readTree "(()())()" = some (.node () (.node () .nil cherry) cherry) := by decide

example : readTree "(" = none := by decide
example : readTree ")" = none := by decide
example : readTree ")(" = none := by decide
example : readTree "(()" = none := by decide
example : readTree "())(" = none := by decide
example : readTree "(x)" = none := by decide
example : readTree "( )" = none := by decide

example : (words 0).card = 1 := by rw [card_words_closedForm]; decide
example : (words 1).card = 1 := by rw [card_words_closedForm]; decide
example : (words 2).card = 2 := by rw [card_words_closedForm]; decide
example : (words 3).card = 5 := by rw [card_words_closedForm]; decide
example : (words 4).card = 14 := by rw [card_words_closedForm]; decide

example : readTree "((()))" = some (.node () leftComb .nil) := by decide
example : readTree "(()())" = some (.node () rightComb .nil) := by decide
example : readTree "(())()" = some (.node () cherry cherry) := by decide
example : readTree "()(())" = some (.node () .nil leftComb) := by decide
example : readTree "()()()" = some (.node () .nil rightComb) := by decide

/-- A word with equal total counts can still fail the prefix test. -/
example : ¬ Balanced [D, U] := by
  intro h
  have := h.prefix.2 1
  simp at this

end Catalan.Examples
