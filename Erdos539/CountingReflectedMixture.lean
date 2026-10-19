/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryCountingRoot
import Erdos539.PopularReflectedSupport

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem sum_additive_pair_indicator (S : Finset G) (z : G) :
    (∑ c : S, ∑ d : S, if c.val + d.val = z then (1 : ℝ) else 0) =
      ((reflectedSupport S z).card : ℝ) := by
  rw [← weightedConvolution_one_eq_reflected_card]
  unfold weightedConvolution fiber
  rw [Finset.sum_filter, Finset.sum_product]
  rw [← Finset.sum_attach S]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_attach S]
  simp

theorem reflectedSupport_nonempty_of_mem_add {S : Finset G} {w : G}
    (hw : w ∈ S + S) : (reflectedSupport S w).Nonempty := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hw
  exact ⟨a, Finset.mem_filter.mpr ⟨ha, by simpa using hb⟩⟩

/-- Distribution of the sum of the first two endpoints of a uniformly
sampled additive quadruple. -/
def countingReflectionWeight (S : Finset G) (w : G) : ℝ :=
  ((reflectedSupport S w).card : ℝ) ^ 2 / countingEnergy S

theorem countingReflectionWeight_nonneg (S : Finset G) (w : G) :
    0 ≤ countingReflectionWeight S w :=
  div_nonneg (sq_nonneg _) (weightedEnergy_nonneg S (fun _ ↦ 1))

theorem countingReflectionWeight_sum {S : Finset G} (hS : S.Nonempty) :
    ∑ w ∈ S + S, countingReflectionWeight S w = 1 := by
  simp only [countingReflectionWeight, div_eq_mul_inv, ← Finset.sum_mul,
    ← countingEnergy_eq_reflected_square_sum]
  have hE := weightedGibbsPartition_pos hS (fun (_ : S) ↦ zero_lt_one)
  simp only [weightedGibbsPartition_constant, one_pow, one_mul] at hE
  exact mul_inv_cancel₀ hE.ne'

/-- The uniform law on an actual reflected intersection, extended by zero
to the original support. -/
def reflectedUniformLaw (S : Finset G) (w : G) (a : S) : ℝ :=
  if a.val ∈ reflectedSupport S w then 1 / (reflectedSupport S w).card else 0

theorem reflectedUniformLaw_sum {S : Finset G} {w : G} (hw : w ∈ S + S) :
    ∑ a : S, reflectedUniformLaw S w a = 1 := by
  have hn : (0 : ℝ) < (reflectedSupport S w).card := by
    exact_mod_cast (reflectedSupport_nonempty_of_mem_add hw).card_pos
  change (∑ a ∈ S.attach, if a.val ∈ reflectedSupport S w then
    (1 : ℝ) / (reflectedSupport S w).card else 0) = 1
  rw [Finset.sum_attach S (fun x ↦ if x ∈ reflectedSupport S w then
    (1 : ℝ) / (reflectedSupport S w).card else 0)]
  rw [← Finset.sum_filter]
  have he : S.filter (fun a ↦ a ∈ reflectedSupport S w) = reflectedSupport S w := by
    ext a
    simp [reflectedSupport]
  rw [he]
  simp [hn.ne']

theorem counting_endpoint_sum_representations {S : Finset G} (hS : S.Nonempty) (a : S) :
    referenceEndpoint S (uniformReference S) a =
      ∑ b : S, ((reflectedSupport S (a.val + b.val)).card : ℝ) / countingEnergy S := by
  change (∑ b, ∑ c, ∑ d,
    (referenceGibbsLaw S (uniformReference S) (uniformReference_pos hS)).mass a b c d) = _
  simp only [referenceGibbs_uniform_mass hS]
  apply Finset.sum_congr rfl
  intro b _
  have h := sum_additive_pair_indicator S (a.val + b.val)
  have he := congrArg (fun t : ℝ ↦ t / countingEnergy S) h
  simpa only [div_eq_mul_inv, Finset.sum_mul, ite_mul, one_mul, zero_mul, eq_comm] using he

/-- The canonical endpoint is exactly the mixture of uniform laws on
reflected parents. These are not the original coordinate conditionals. -/
theorem counting_endpoint_reflected_mixture {S : Finset G} (hS : S.Nonempty) (a : S) :
    referenceEndpoint S (uniformReference S) a =
      ∑ w ∈ S + S, countingReflectionWeight S w * reflectedUniformLaw S w a := by
  rw [counting_endpoint_sum_representations hS]
  change (∑ b ∈ S.attach, ((reflectedSupport S (a.val + b.val)).card : ℝ) /
    countingEnergy S) = _
  rw [Finset.sum_attach S (fun b ↦ ((reflectedSupport S (a.val + b)).card : ℝ) /
    countingEnergy S)]
  calc
    _ = ∑ w ∈ S.image (fun b ↦ a.val + b),
        ((reflectedSupport S w).card : ℝ) / countingEnergy S := by
      rw [Finset.sum_image]
      intro b _ c _ he
      exact add_left_cancel he
    _ = ∑ w ∈ S + S, if w - a.val ∈ S then
        ((reflectedSupport S w).card : ℝ) / countingEnergy S else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext w
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨Finset.mem_add.mpr ⟨a.val, a.property, b, hb, rfl⟩, by simpa using hb⟩
      · rintro ⟨_, hb⟩
        exact ⟨w - a.val, hb, by abel⟩
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      have hn : (0 : ℝ) < (reflectedSupport S w).card := by
        exact_mod_cast (reflectedSupport_nonempty_of_mem_add hw).card_pos
      simp only [countingReflectionWeight, reflectedUniformLaw, reflectedSupport,
        Finset.mem_filter, a.property, true_and]
      split_ifs
      · field_simp
      · simp

end
end Erdos539Geometry
