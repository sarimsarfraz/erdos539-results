/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GluingSeparation

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι κ : Type*}

abbrev GluePositiveIndex (ι κ : Type*) :=
  ((ι → ℤ) × (κ → ℤ)) ⊕ ((ℤ × (ι → ℤ)) ⊕ (ℤ × (κ → ℤ)))

def positiveGlueIndices (F : Finset (ι → ℤ)) (G : Finset (κ → ℤ)) (K : ℕ) :
    Finset (GluePositiveIndex ι κ) :=
  (integerPositiveDifferences F ×ˢ integerPositiveDifferences G).disjSum
    (((Finset.Ico 1 (K : ℤ)) ×ˢ integerDifferences F).disjSum
      ((Finset.Ico 1 (K : ℤ)) ×ˢ integerDifferences G))

def positiveGlueEncode (M : ℤ) : GluePositiveIndex ι κ → (ι ⊕ κ → ℤ) :=
  Sum.elim (fun p ↦ Sum.elim p.1 p.2)
    (Sum.elim (fun p ↦ Sum.elim (glueShift M p.1 p.2) (fun _ ↦ 0))
      (fun p ↦ Sum.elim (fun _ ↦ 0) (glueShift M p.1 p.2)))

/-- The three regimes have exactly the claimed number of formal parameters. -/
theorem positiveGlueIndices_card (F : Finset (ι → ℤ)) (G : Finset (κ → ℤ)) (K : ℕ) :
    (positiveGlueIndices F G K).card =
      (integerPositiveDifferences F).card * (integerPositiveDifferences G).card +
        (K - 1) * ((integerDifferences F).card + (integerDifferences G).card) := by
  have hc : (Finset.Ico 1 (K : ℤ)).card = K - 1 := by rw [Int.card_Ico]; omega
  simp only [positiveGlueIndices, Finset.card_disjSum, Finset.card_product, hc]
  ring

/-- Separation M>2L makes the three positive-difference regimes disjoint,
and recovers every parameter inside each regime. -/
theorem positiveGlueEncode_injOn {F : Finset (ι → ℤ)} {G : Finset (κ → ℤ)}
    (K : ℕ) {L M : ℤ} (hL : 0 ≤ L) (hM : 2 * L < M)
    (hF : ∀ x ∈ F, ∀ y ∈ F, ∀ i, |x i - y i| ≤ L)
    (hG : ∀ x ∈ G, ∀ y ∈ G, ∀ i, |x i - y i| ≤ L) (i : ι) (j : κ) :
    Set.InjOn (positiveGlueEncode M) (positiveGlueIndices F G K : Set (GluePositiveIndex ι κ)) := by
  intro p hp q hq he
  change p ∈ positiveGlueIndices F G K at hp
  change q ∈ positiveGlueIndices F G K at hq
  have hMp : 0 < M := by omega
  have hf := differences_coordinateGap_of_diameter hM hF
  have hg := differences_coordinateGap_of_diameter hM hG
  rcases p with p | (p | p) <;> rcases q with q | (q | q)
  all_goals simp only [positiveGlueIndices, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum,
    Finset.mem_product, Finset.mem_Ico] at hp hq
  · apply congrArg Sum.inl
    apply Prod.ext
    · funext k
      exact congrFun he (Sum.inl k)
    · funext k
      exact congrFun he (Sum.inr k)
  · have hz := (integerPositiveDifference_coordinate_bound hL hF hp.1 i).2
    have hs := glueShift_coordinate_gt hL hM hq.1.1 hF hq.2 i
    have hh := congrFun he (Sum.inl i)
    change p.1 i = glueShift M q.1 q.2 i at hh
    omega
  · have hz := (integerPositiveDifference_coordinate_bound hL hG hp.2 j).2
    have hs := glueShift_coordinate_gt hL hM hq.1.1 hG hq.2 j
    have hh := congrFun he (Sum.inr j)
    change p.2 j = glueShift M q.1 q.2 j at hh
    omega
  · have hz := (integerPositiveDifference_coordinate_bound hL hF hq.1 i).2
    have hs := glueShift_coordinate_gt hL hM hp.1.1 hF hp.2 i
    have hh := congrFun he (Sum.inl i)
    change glueShift M p.1 p.2 i = q.1 i at hh
    omega
  · have hh : glueShift M p.1 p.2 = glueShift M q.1 q.2 := funext (fun k ↦ congrFun he (Sum.inl k))
    obtain ⟨h1, h2⟩ := glueShift_injective_of_gap hMp hf i hp.2 hq.2 hh
    exact congrArg (fun z ↦ Sum.inr (Sum.inl z)) (Prod.ext h1 h2)
  · have hs := glueShift_coordinate_gt hL hM hp.1.1 hF hp.2 i
    have hh := congrFun he (Sum.inl i)
    change glueShift M p.1 p.2 i = 0 at hh
    omega
  · have hz := (integerPositiveDifference_coordinate_bound hL hG hq.2 j).2
    have hs := glueShift_coordinate_gt hL hM hp.1.1 hG hp.2 j
    have hh := congrFun he (Sum.inr j)
    change glueShift M p.1 p.2 j = q.2 j at hh
    omega
  · have hs := glueShift_coordinate_gt hL hM hq.1.1 hF hq.2 i
    have hh := congrFun he (Sum.inl i)
    change 0 = glueShift M q.1 q.2 i at hh
    omega
  · have hh : glueShift M p.1 p.2 = glueShift M q.1 q.2 := funext (fun k ↦ congrFun he (Sum.inr k))
    obtain ⟨h1, h2⟩ := glueShift_injective_of_gap hMp hg j hp.2 hq.2 hh
    exact congrArg (fun z ↦ Sum.inr (Sum.inr z)) (Prod.ext h1 h2)

end
end Erdos539Geometry
