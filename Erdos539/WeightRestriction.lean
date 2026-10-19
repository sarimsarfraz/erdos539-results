/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyMonotonicity
import Erdos539.EnergySupport

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def restrictWeight (A : Finset G) (w : G → ℝ) (x : G) : ℝ := if x ∈ A then w x else 0

theorem weightedEnergy_restrict {A S : Finset G} (hAS : A ⊆ S) (w : G → ℝ) :
    weightedEnergy S (restrictWeight A w) = weightedEnergy A w := by
  rw [← weightedEnergy_support hAS _ (by intro x _ hx; simp [restrictWeight, hx])]
  apply weightedEnergy_congr
  intro x hx
  simp [restrictWeight, hx]

theorem weightedEnergy_restrict_split {A S : Finset G} (_hAS : A ⊆ S) (w : G → ℝ) :
    weightedEnergy S (restrictWeight A w + restrictWeight (S \ A) w) = weightedEnergy S w := by
  apply weightedEnergy_congr
  intro x hx
  by_cases hxa : x ∈ A <;> simp [restrictWeight, hx, hxa]

theorem weightedEnergy_complement_retention {A S : Finset G} (hAS : A ⊆ S) (w : G → ℝ)
    (hbad : weightedEnergy A w ≤ weightedEnergy S w / 16) :
    weightedEnergy S w / 16 ≤ weightedEnergy (S \ A) w := by
  have h := weightedEnergy_split_retention S (restrictWeight A w) (restrictWeight (S \ A) w)
  rw [weightedEnergy_restrict_split hAS, weightedEnergy_restrict hAS,
    weightedEnergy_restrict Finset.sdiff_subset] at h
  exact h hbad

theorem weightedEnergy_nonempty_of_pos {S : Finset G} {w : G → ℝ} (h : 0 < weightedEnergy S w) :
    S.Nonempty := by
  by_contra hS
  rw [Finset.not_nonempty_iff_eq_empty.mp hS] at h
  simp [weightedEnergy] at h

end
end Erdos539Geometry
