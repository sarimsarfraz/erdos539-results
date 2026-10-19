/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryLawCorrelation
import Erdos539.StationaryCoordinateEnergy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

namespace StationaryAdditiveLaw
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] {S : Finset G} {ν : S → ℝ}

/-- The same-law entropy lower bound for logarithmic energy. -/
def energyProfile (Q : StationaryAdditiveLaw S ν) : ℝ := Q.entropy - 2 * finiteEntropy ν

theorem energyProfile_eq_entropy_sub_correlation (Q : StationaryAdditiveLaw S ν) :
    Q.energyProfile = finiteEntropy ν - Q.correlation := by
  unfold energyProfile correlation
  ring

theorem map_energyProfile_lower (Q : StationaryAdditiveLaw S ν) (hν : ∀ x, 0 ≤ ν x)
    {T : Finset H} (e : S → T)
    (hrel : ∀ a b c d : S, a.val + b.val = c.val + d.val →
      (e a).val + (e b).val = (e c).val + (e d).val) :
    Q.energyProfile - (finiteEntropy ν - finiteEntropy (finitePush ν e)) ≤ (Q.map e hrel).energyProfile := by
  have h := Q.correlation_map_le hν e hrel
  rw [energyProfile_eq_entropy_sub_correlation, energyProfile_eq_entropy_sub_correlation]
  linarith

end StationaryAdditiveLaw

theorem optimizerStationaryAdditiveLaw_energyProfile {G : Type*} [AddCommGroup G] [DecidableEq G]
    {S : Finset G} (hS : S.Nonempty) {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    (optimizerStationaryAdditiveLaw hS hf hE).energyProfile = Real.log (energyNorm S) := by
  rw [StationaryAdditiveLaw.energyProfile_eq_entropy_sub_correlation,
    optimizerStationaryAdditiveLaw_correlation hS hf hE]
  ring

variable {ι : Type*}
local instance stationaryProjectionProfileDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The complete first chain of the parallel-projection theorem: actual
projected marginal energy retains the root log norm minus entropy loss.
The original optimizer and its canonical law are fixed throughout. -/
theorem optimizer_projection_log_energy_lower {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) (I : Finset ι) :
    Real.log (energyNorm S) -
      (finiteEntropy (fun x ↦ f x ^ 2) - finiteEntropy (finitePush (fun x ↦ f x ^ 2) (projectEndpoint S I))) ≤
      Real.log (actualMarginalEnergy S (extendWeight S f) I) := by
  let Q := optimizerStationaryAdditiveLaw hS hf hE
  have h := Q.map_energyProfile_lower (fun x ↦ sq_nonneg (f x))
    (projectEndpoint S I) (projectEndpoint_preserves_additive S I)
  have hroot : Q.energyProfile = Real.log (energyNorm S) := optimizerStationaryAdditiveLaw_energyProfile hS hf hE
  rw [hroot] at h
  exact h.trans (Q.projected_entropy_le_log_actual hf.2 I)

end
end Erdos539Geometry
