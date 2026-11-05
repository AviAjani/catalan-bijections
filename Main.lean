import Catalan
import Mathlib.Data.Finset.Sort
import Mathlib.Data.String.Basic

open Catalan

private def showParse (s : String) : IO Unit :=
  match readTree s with
  | none => IO.println s!"{repr s}: rejected"
  | some t => IO.println s!"{repr s}: {shape t}  ({t.numNodes} internal nodes)"

private def listWords (n : Nat) : IO Unit := do
  let ws := ((words n).image render).sort (· ≤ ·)
  IO.println s!"{ws.length} balanced words with {n} pairs:"
  for w in ws do
    IO.println (if w.isEmpty then "<empty>" else w)

private def demo : IO Unit := do
  IO.println "Trees, parentheses, and Catalan numbers"
  IO.println "n  enumerated  Catalan"
  for n in List.range 9 do
    IO.println s!"{n}  {(words n).card}  {catalan n}"
  IO.println ""
  listWords 3
  IO.println ""
  for s in ["", "(())", "()()", "(()())()", ")(", "(()", "(x)"] do
    showParse s

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => demo; pure 0
  | ["parse", s] => showParse s; pure (if (readTree s).isSome then 0 else 1)
  | ["list", n] =>
    match n.toNat? with
    | some k =>
      if k ≤ 9 then
        listWords k
        pure 0
      else
        IO.eprintln "Listing is limited to 9 pairs (4862 words)."
        pure 2
    | none => IO.eprintln "Expected a nonnegative integer."; pure 2
  | _ =>
    IO.eprintln "Usage: lake exe catalan-demo [parse <parentheses> | list <0..9>]"
    pure 2
