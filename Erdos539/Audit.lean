import Erdos539
import Mathlib.Util.AssertNoSorry

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mut checked := 0
  -- Use Lean's own kernel-environment collector, sharing its visited set
  -- across roots. The union is exactly the union of the per-root axiom
  -- closures; each transitive dependency only needs to be visited once.
  let mut state : Lean.CollectAxioms.State := {}
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Erdos539" then
      let (_, next) := ((Lean.CollectAxioms.collect name).run env).run state
      state := next
      checked := checked + 1
  for ax in state.axioms do
    unless allowed.contains ax do
      throwError "Forbidden axiom {ax} in the audited declaration closure"
  logInfo m!"Axiom audit passed for {checked} declarations. Allowed: propext, Classical.choice, Quot.sound."
