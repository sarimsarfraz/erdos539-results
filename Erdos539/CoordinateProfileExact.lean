/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinateHan

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

namespace StationaryAdditiveLaw
variable {G H K : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]
variable {S : Finset G} {ν : S → ℝ}

theorem energyProfile_map_comp (Q : StationaryAdditiveLaw S ν)
    {T : Finset H} {U : Finset K} (e : S → T) (g : T → U)
    (he : ∀ a b c d : S, a.val + b.val = c.val + d.val →
      (e a).val + (e b).val = (e c).val + (e d).val)
    (hg : ∀ a b c d : T, a.val + b.val = c.val + d.val →
      (g a).val + (g b).val = (g c).val + (g d).val) :
    ((Q.map e he).map g hg).energyProfile =
      (Q.map (g ∘ e) (fun a b c d h ↦ hg _ _ _ _ (he a b c d h))).energyProfile := by
  simp only [energyProfile, entropy_eq_finiteEntropy_flat, flat_map, finitePush_comp]
  rfl

theorem energyProfile_map_eq_of_injective (Q : StationaryAdditiveLaw S ν)
    {T : Finset H} (e : S → T) (hinj : Function.Injective e)
    (he : ∀ a b c d : S, a.val + b.val = c.val + d.val →
      (e a).val + (e b).val = (e c).val + (e d).val) :
    (Q.map e he).energyProfile = Q.energyProfile := by
  have hfour : Function.Injective (mapFour e) := by
    intro a b h
    apply Prod.ext
    · apply Prod.ext
      · exact hinj (congrArg (fun z ↦ z.1.1) h)
      · exact hinj (congrArg (fun z ↦ z.1.2) h)
    · apply Prod.ext
      · exact hinj (congrArg (fun z ↦ z.2.1) h)
      · exact hinj (congrArg (fun z ↦ z.2.2) h)
  simp only [energyProfile, entropy_eq_finiteEntropy_flat, flat_map]
  rw [finiteEntropy_push_eq_of_support_injective _ _ (fun a b _ _ h ↦ hfour h),
    finiteEntropy_push_eq_of_support_injective _ _ (fun a b _ _ h ↦ hinj h)]

end StationaryAdditiveLaw

variable {ι : Type*} [Fintype ι]
local instance coordinateProfileExactDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance coordinateProfileExactProjectionDecidableEq (S : Finset (ι → ℝ)) (I : Finset ι) :
    DecidableEq (projection S I) := Classical.decEq _

namespace StationaryAdditiveLaw
variable {S : Finset (ι → ℝ)} {f : S → ℝ}

theorem projectLaw_univ_energyProfile (Q : StationaryAdditiveLaw S (fun x ↦ f x ^ 2)) :
    (Q.projectLaw Finset.univ).energyProfile = Q.energyProfile := by
  apply Q.energyProfile_map_eq_of_injective
  intro a b he
  apply Subtype.ext
  funext i
  exact congrFun (congrArg Subtype.val he) ⟨i, Finset.mem_univ i⟩

theorem outside_energyProfile_eq (Q : StationaryAdditiveLaw S (fun x ↦ f x ^ 2)) (i : ι) :
    (Q.projectLaw (Finset.univ.erase i)).energyProfile =
      Q.energyProfile - coordinateConditionalEntropy S (fun x ↦ f x ^ 2) i +
        (Q.correlation - (Q.projectLaw (Finset.univ.erase i)).correlation) := by
  rw [energyProfile_eq_entropy_sub_correlation, energyProfile_eq_entropy_sub_correlation]
  unfold coordinateConditionalEntropy outsideEndpoint
  ring

/-- Exact manuscript identity for all coordinate deletions, with the
same endpoint and quadruple laws throughout. -/
theorem parallel_profile_identity (Q : StationaryAdditiveLaw S (fun x ↦ f x ^ 2)) :
    (∑ i, (Q.projectLaw (Finset.univ.erase i)).energyProfile) -
      ((Fintype.card ι : ℝ) - 1) * Q.energyProfile =
    Q.energyProfile - (∑ i, coordinateConditionalEntropy S (fun x ↦ f x ^ 2) i) +
      ∑ i, (Q.correlation - (Q.projectLaw (Finset.univ.erase i)).correlation) := by
  simp_rw [Q.outside_energyProfile_eq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

theorem outside_correlation_loss_nonneg (Q : StationaryAdditiveLaw S (fun x ↦ f x ^ 2)) (i : ι) :
    0 ≤ Q.correlation - (Q.projectLaw (Finset.univ.erase i)).correlation := by
  exact sub_nonneg.mpr (Q.correlation_map_le (fun x ↦ sq_nonneg (f x))
    (projectEndpoint S (Finset.univ.erase i)) (projectEndpoint_preserves_additive S _))

end StationaryAdditiveLaw
end
end Erdos539Geometry
