import Lean

/-!
# Axiom audit

`#audit_axioms thm` prints the axioms `thm` depends on and fails the build when the set contains anything
beyond `propext`, `Classical.choice` and `Quot.sound`. This rejects `sorry` (`sorryAx`), a declared `axiom`,
and a native-code trust axiom. Every main theorem of the package is audited with it.

`#audit_package` does the same for every declaration of every `Vinc.*` module that is imported at that point;
the root module `Vinc` runs it, so `lake build` fails if anything in the package depends on `sorry` or an
extra axiom, even a helper lemma that no main theorem mentions.
-/

open Lean Elab Command

private def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

elab "#audit_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms n
  let bad := axs.filter (fun a => !allowedAxioms.contains a)
  logInfo m!"'{n}' depends on axioms: {axs.toList}"
  unless bad.isEmpty do
    throwError "'{n}' depends on disallowed axioms: {bad.toList}"

/-- Fail unless every declaration of every imported `Vinc.*` module depends only on the allowed axioms. -/
elab "#audit_package" : command => do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if env.header.moduleNames[idx.toNat]!.getRoot == `Vinc && !n.isInternal then names := names.push n
  let mut seen : Array Name := #[]
  for n in names do
    for a in (← liftCoreM <| collectAxioms n) do
      unless seen.contains a do seen := seen.push a
  let bad := seen.filter (fun a => !allowedAxioms.contains a)
  logInfo m!"{names.size} declarations audited; axioms used: {seen.toList}"
  unless bad.isEmpty do
    throwError "disallowed axioms in the package: {bad.toList}"
