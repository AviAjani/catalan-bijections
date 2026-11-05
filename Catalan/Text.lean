import Catalan.Parser

/-! # Parenthesis strings -/

namespace Catalan

open DyckStep

/-- Render a word using the conventional parenthesis alphabet. -/
def render (w : Word) : String :=
  String.mk (w.map fun b => match b with | U => '(' | D => ')')

/-- Tokenize strictly: any character other than `(` or `)` is rejected. -/
def tokenize : List Char → Option Word
  | [] => some []
  | '(' :: cs => (U :: ·) <$> tokenize cs
  | ')' :: cs => (D :: ·) <$> tokenize cs
  | _ => none

/-- Parse a string, rejecting invalid characters as well as unbalanced parentheses. -/
def readTree (s : String) : Option FullBinaryTree := do
  let w ← tokenize s.toList
  decode w

@[simp] theorem tokenize_render (w : Word) : tokenize (render w).toList = some w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | U => simpa [render, tokenize] using congrArg (Option.map (U :: ·)) ih
    | D => simpa [render, tokenize] using congrArg (Option.map (D :: ·)) ih

@[simp] theorem readTree_render_encode (t : FullBinaryTree) :
    readTree (render (encode t)) = some t := by
  unfold readTree
  rw [tokenize_render]
  exact decode_encode t

theorem render_injective : Function.Injective render := by
  intro a b h
  have ht := congrArg (fun s : String => tokenize s.toList) h
  simpa only [tokenize_render, Option.some.injEq] using ht

/-- A compact display: `.` is a leaf and `[left right]` is an internal node. -/
def shape : FullBinaryTree → String
  | .nil => "."
  | .node _ l r => "[" ++ shape l ++ " " ++ shape r ++ "]"

end Catalan
