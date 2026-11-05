import Catalan.Basic

/-!
# A certified recursive-descent parser

The parser stops before a closing parenthesis. Fuel is explicit so that the
implementation is structurally recursive; input length plus one suffices.
-/

namespace Catalan

open DyckStep

/-- Parse one balanced segment, leaving a closing delimiter unconsumed. -/
def parse : Nat → Word → Option (FullBinaryTree × Word)
  | 0, _ => none
  | _ + 1, [] => some (.nil, [])
  | _ + 1, D :: w => some (.nil, D :: w)
  | fuel + 1, U :: w =>
    match parse fuel w with
    | some (l, D :: tail) =>
      match parse fuel tail with
      | some (r, rest) => some (.node () l r, rest)
      | none => none
    | _ => none

/-- Parse a complete word; reject a trailing unmatched closing parenthesis. -/
def decode (w : Word) : Option FullBinaryTree :=
  match parse (w.length + 1) w with
  | some (t, []) => some t
  | _ => none

/-- A parser result accounts for every consumed token. -/
theorem parse_sound {fuel : Nat} {w rest : Word} {t : FullBinaryTree}
    (h : parse fuel w = some (t, rest)) : w = encode t ++ rest := by
  induction fuel generalizing w rest t with
  | zero => simp [parse] at h
  | succ fuel ih =>
    cases w with
    | nil =>
      simp only [parse, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | cons b w =>
      cases b with
      | D =>
        simp only [parse, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rfl
      | U =>
        cases hl : parse fuel w with
        | none => simp [parse, hl] at h
        | some result =>
          rcases result with ⟨l, tail⟩
          cases tail with
          | nil => simp [parse, hl] at h
          | cons b tail =>
            cases b with
            | U => simp [parse, hl] at h
            | D =>
              cases hr : parse fuel tail with
              | none => simp [parse, hl, hr] at h
              | some result =>
                rcases result with ⟨r, suffix⟩
                simp only [parse, hl, hr, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                rw [ih hl, ih hr]
                simp [encode, List.append_assoc]

/-- A delimiter is either the end of the input or a closing parenthesis. -/
def Boundary : Word → Prop
  | [] => True
  | D :: _ => True
  | U :: _ => False

/-- Sufficient fuel parses any encoding up to its delimiter. -/
theorem parse_encode (t : FullBinaryTree) (suffix : Word) (hs : Boundary suffix)
    (fuel : Nat) (hf : t.numNodes < fuel) :
    parse fuel (encode t ++ suffix) = some (t, suffix) := by
  induction t generalizing suffix fuel with
  | nil =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      cases suffix with
      | nil => rfl
      | cons b suffix => cases b <;> simp_all [Boundary, encode, parse]
  | node a l r hl hr =>
    cases a
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hlf : l.numNodes < fuel := by simp only [Tree.numNodes] at hf; omega
      have hrf : r.numNodes < fuel := by simp only [Tree.numNodes] at hf; omega
      have hleft := hl (D :: (encode r ++ suffix)) trivial fuel hlf
      have hright := hr suffix hs fuel hrf
      simp [encode, List.append_assoc, parse, hleft, hright]

@[simp] theorem decode_encode (t : FullBinaryTree) : decode (encode t) = some t := by
  have h := parse_encode t [] trivial ((encode t).length + 1) (by rw [length_encode]; omega)
  have hp : parse ((encode t).length + 1) (encode t) = some (t, []) := by
    simpa only [List.append_nil] using h
  simp only [decode, hp]

/-- Every accepted input is exactly the encoding of the returned tree. -/
theorem encode_of_decode {w : Word} {t : FullBinaryTree} (h : decode w = some t) :
    encode t = w := by
  unfold decode at h
  cases hp : parse (w.length + 1) w with
  | none => simp [hp] at h
  | some result =>
    rcases result with ⟨r, rest⟩
    cases rest with
    | nil =>
      simp only [hp, Option.some.injEq] at h
      subst r
      simpa using (parse_sound hp).symm
    | cons _ _ => simp [hp] at h

theorem encode_injective : Function.Injective encode := by
  intro a b h
  have := congrArg decode h
  simpa using this

/-- Every grammatical word has a tree, independently of the parser implementation. -/
theorem Balanced.exists_encoding {w : Word} (h : Balanced w) :
    ∃ t : FullBinaryTree, encode t = w := by
  induction h with
  | empty => exact ⟨.nil, rfl⟩
  | node _ _ hl hr =>
    obtain ⟨l, rfl⟩ := hl
    obtain ⟨r, rfl⟩ := hr
    exact ⟨.node () l r, rfl⟩

/-- Acceptance is equivalent to the grammar, hence also to prefix balance. -/
theorem decode_eq_some_iff (w : Word) :
    (∃ t, decode w = some t) ↔ Balanced w := by
  constructor
  · rintro ⟨t, ht⟩
    rw [← encode_of_decode ht]
    exact balanced_encode t
  · intro h
    obtain ⟨t, rfl⟩ := h.exists_encoding
    exact ⟨t, decode_encode t⟩

theorem decode_eq_none_iff (w : Word) : decode w = none ↔ ¬ Balanced w := by
  rw [← decode_eq_some_iff]
  cases decode w <;> simp

/-- Parser acceptance agrees with the usual definition, not only the grammar. -/
theorem decode_iff_prefix (w : Word) :
    (∃ t, decode w = some t) ↔ w.count U = w.count D ∧
      ∀ k, (w.take k).count D ≤ (w.take k).count U := by
  rw [decode_eq_some_iff, balanced_iff_prefix]

theorem decode_unique {w : Word} {t : FullBinaryTree} :
    decode w = some t ↔ encode t = w := by
  constructor
  · exact encode_of_decode
  · rintro rfl
    exact decode_encode t

/-- The first-return grammar has a unique inside/outside decomposition. -/
theorem Balanced.unique_split {a b c d : Word}
    (ha : Balanced a) (hb : Balanced b) (hc : Balanced c) (hd : Balanced d)
    (h : U :: (a ++ D :: b) = U :: (c ++ D :: d)) : a = c ∧ b = d := by
  obtain ⟨ta, rfl⟩ := ha.exists_encoding
  obtain ⟨tb, rfl⟩ := hb.exists_encoding
  obtain ⟨tc, rfl⟩ := hc.exists_encoding
  obtain ⟨td, rfl⟩ := hd.exists_encoding
  have he : encode (.node () ta tb) = encode (.node () tc td) := h
  have ht := encode_injective he
  cases ht
  exact ⟨rfl, rfl⟩

end Catalan
