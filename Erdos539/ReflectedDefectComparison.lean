/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CountingReflectedMixture
import Erdos539.StationaryUniformDefect

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def reflectedMeanCountingDefect (S : Finset G) : ℝ :=
  ∑ w ∈ S + S, countingReflectionWeight S w *
    Real.log (((reflectedSupport S w).card : ℝ) ^ 3 / countingEnergy (reflectedSupport S w))

def reflectedMeanStationaryDefect (S : Finset G) : ℝ :=
  ∑ w ∈ S + S, countingReflectionWeight S w *
    stationaryEntropyDefect (reflectedSupport S w) (uniformReference (reflectedSupport S w))

theorem reflectedMeanCountingDefect_le_stationary (S : Finset G) :
    reflectedMeanCountingDefect S ≤ reflectedMeanStationaryDefect S := by
  apply Finset.sum_le_sum
  intro w hw
  exact mul_le_mul_of_nonneg_left
    (stationaryEntropyDefect_uniform_lower (reflectedSupport_nonempty_of_mem_add hw))
    (countingReflectionWeight_nonneg S w)

theorem counting_endpoint_defect_le {S : Finset G} (hS : S.Nonempty) :
    stationaryEntropyDefect S (referenceEndpoint S (uniformReference S)) ≤
      Real.log ((S.card : ℝ) ^ 3 / countingEnergy S) := by
  have he := stationaryReferenceDefect_counting hS
  have hD := finiteRelEntropy_nonneg (referenceEndpoint S (uniformReference S))
    (uniformReference S) (fun x ↦ (referenceEndpoint_pos hS (uniformReference_pos hS) x).le)
    (fun x ↦ (uniformReference_pos hS x).le)
    (referenceEndpoint_sum hS (uniformReference_pos hS)) (uniformReference_sum hS)
    (fun x _ ↦ uniformReference_pos hS x)
  unfold stationaryReferenceDefect at he
  linarith

/-- A strict excess for ordinary reflected counting defects implies the
same strict excess for stationary defects over their canonical mixture. -/
theorem reflected_stationary_excess_of_counting {S : Finset G} (hS : S.Nonempty)
    {c : ℝ} (hc : c < reflectedMeanCountingDefect S -
      Real.log ((S.card : ℝ) ^ 3 / countingEnergy S)) :
    c < reflectedMeanStationaryDefect S -
      stationaryEntropyDefect S (referenceEndpoint S (uniformReference S)) := by
  have h1 := reflectedMeanCountingDefect_le_stationary S
  have h2 := counting_endpoint_defect_le hS
  linarith

end
end Erdos539Geometry
