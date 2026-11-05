import Catalan
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Check every declaration in the project namespace, including generated
declarations. The allowlist is Lean's standard classical foundation.
An unfinished proof or additional axiom makes this command fail.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    if (`Catalan).isPrefixOf name || name.toString.startsWith "_private.Catalan." then
      checked := checked + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
  logInfo m!"Axiom audit passed for {checked} declarations in namespace Catalan."

#print axioms Catalan.decode_encode
#print axioms Catalan.encode_of_decode
#print axioms Catalan.decode_iff_prefix
#print axioms Catalan.sizedEquiv
#print axioms Catalan.card_wordAt_closedForm
