/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignMasks

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*} [Fintype ι]

/-- The mask pairs exceeding the relative projection threshold. Every
projection and maximum fiber here belongs to the fixed original parent `S`. -/
def badPairs (A S : Finset (ι → ℝ)) (I : Finset ι) (H : ℕ) : Finset ((ι → ℝ) × (ι → ℝ)) :=
  (samePairs A (project I)).filter (fun p ↦
    4 * 2 ^ (Finset.univ \ I).card * H * maxRestrictedFan A I * (projection S I).card <
      A.card * (projection S (I ∪ freeMask I p.1 p.2)).card)

theorem four_mul_badPairs_le_samePairs
    {A S : Finset (ι → ℝ)} (hAS : A ⊆ S) (hA : A.Nonempty)
    (I : Finset ι) (H : ℕ)
    (hH : ∀ J, (projection S J).card * maxFiber S (project J) ≤ H) :
    4 * (badPairs A S I H).card ≤ (samePairs A (project I)).card := by
  classical
  let n := A.card
  let P := (projection S I).card
  let M := maxRestrictedFan A I
  let t := 2 ^ (Finset.univ \ I).card
  let C := 4 * t
  let B := badPairs A S I H
  let f : ((ι → ℝ) × (ι → ℝ)) → ((ι → ℝ) × Finset ι) :=
    fun p ↦ (p.2, freeMask I p.1 p.2)
  have hP : 0 < P := Finset.card_pos.mpr ((hA.mono hAS).image _)
  have ht : 0 < t := pow_pos (by decide) _
  have hcell (y : ι → ℝ) (hy : y ∈ A) (J : Finset ι)
      (hb : C * H * M * P < n * (projection S (I ∪ J)).card) :
      (maskCell A I J y).card * (C * P) ≤ n := by
    have hm : (maskCell A I J y).card * (projection S (I ∪ J)).card ≤ M * H := by
      calc
        _ ≤ (M * maxFiber S (project (I ∪ J))) * (projection S (I ∪ J)).card :=
          Nat.mul_le_mul_right _ (card_maskCell_le hAS I J hy)
        _ = M * ((projection S (I ∪ J)).card * maxFiber S (project (I ∪ J))) := by ring
        _ ≤ M * H := Nat.mul_le_mul_left M (hH (I ∪ J))
    apply Nat.le_of_lt
    apply Nat.lt_of_mul_lt_mul_right (a := (projection S (I ∪ J)).card)
    calc
      _ = (C * P) * ((maskCell A I J y).card * (projection S (I ∪ J)).card) := by ring
      _ ≤ (C * P) * (M * H) := Nat.mul_le_mul_left _ hm
      _ = C * H * M * P := by ring
      _ < _ := hb
  have hf : ∀ b ∈ B.image f, (fiber B f b).card * (C * P) ≤ n := by
    intro b hb
    obtain ⟨p, hp, hfp⟩ := Finset.mem_image.mp hb
    obtain ⟨hpE, hpbad⟩ := Finset.mem_filter.mp hp
    have hpdata := mem_samePairs.mp hpE
    have hbfirst : p.2 = b.1 := congrArg Prod.fst hfp
    have hbsecond : freeMask I p.1 p.2 = b.2 := congrArg Prod.snd hfp
    have hsub : (fiber B f b).image Prod.fst ⊆ maskCell A I b.2 b.1 := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hqB, hqf⟩ := mem_fiber.mp hq
      have hqdata := mem_samePairs.mp (Finset.mem_filter.mp hqB).1
      have hqfirst : q.2 = b.1 := congrArg Prod.fst hqf
      have hqsecond : freeMask I q.1 q.2 = b.2 := congrArg Prod.snd hqf
      exact mem_maskCell.mpr ⟨hqdata.1, hqfirst ▸ hqdata.2.2, hqfirst ▸ hqsecond⟩
    have hinj : (fiber B f b : Set ((ι → ℝ) × (ι → ℝ))).InjOn Prod.fst := by
      intro q hq r hr he
      apply Prod.ext he
      exact (congrArg Prod.fst (mem_fiber.mp hq).2).trans
        (congrArg Prod.fst (mem_fiber.mp hr).2).symm
    have hcard : (fiber B f b).card ≤ (maskCell A I b.2 b.1).card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card hsub
    apply (Nat.mul_le_mul_right (C * P) hcard).trans
    apply hcell b.1 (hbfirst ▸ hpdata.2.1) b.2
    change C * H * M * P < n * (projection S (I ∪ freeMask I p.1 p.2)).card at hpbad
    rwa [hbsecond] at hpbad
  have himg : B.image f ⊆ A ×ˢ (Finset.univ \ I).powerset := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_product.mpr ⟨(mem_samePairs.mp (Finset.mem_filter.mp hp).1).2.1,
      Finset.mem_powerset.mpr (freeMask_subset I p.1 p.2)⟩
  have hcount : B.card * (C * P) ≤ (n * t) * n := by
    apply (card_mul_le_image_mul B f (C * P) n hf).trans
    apply Nat.mul_le_mul_right n
    simpa only [Finset.card_product, Finset.card_powerset] using Finset.card_le_card himg
  have hsmall : 4 * B.card * P ≤ n ^ 2 := by
    apply Nat.le_of_mul_le_mul_right (c := t) _ ht
    calc
      _ = B.card * (C * P) := by dsimp [C]; ring
      _ ≤ (n * t) * n := hcount
      _ = _ := by ring
  apply Nat.le_of_mul_le_mul_right (c := P) _ hP
  calc
    _ ≤ n ^ 2 := hsmall
    _ ≤ P * (samePairs A (project I)).card := card_sq_le_parent_image_mul_samePairs hAS _
    _ = _ := Nat.mul_comm _ _

/-- Relative projection balance, in an exact natural-number formulation.
Dividing by `|A| P_I(S)` recovers the manuscript's relative projection ratios. -/
theorem relative_projection_balance
    {A S : Finset (ι → ℝ)} (hAS : A ⊆ S) (hA : A.Nonempty)
    (I : Finset ι) (H : ℕ)
    (hH : ∀ J, (projection S J).card * maxFiber S (project J) ≤ H) :
    ∃ U ⊆ Finset.univ \ I,
      A.card * (projection S (I ∪ U)).card ≤
        4 * 2 ^ (Finset.univ \ I).card * H * maxRestrictedFan A I * (projection S I).card ∧
      A.card * (projection S (I ∪ ((Finset.univ \ I) \ U))).card ≤
        4 * 2 ^ (Finset.univ \ I).card * H * maxRestrictedFan A I * (projection S I).card := by
  classical
  let E := samePairs A (project I)
  let B := badPairs A S I H
  have hsmall : 4 * B.card ≤ E.card := four_mul_badPairs_le_samePairs hAS hA I H hH
  have hE : 0 < E.card := by
    obtain ⟨a, ha⟩ := hA
    exact Finset.card_pos.mpr ⟨(a, a), mem_samePairs.mpr ⟨ha, ha, rfl⟩⟩
  have hcard : (B ∪ B.image Prod.swap).card < E.card := by
    have hc := Finset.card_union_le B (B.image Prod.swap)
    have hi : (B.image Prod.swap).card ≤ B.card := Finset.card_image_le
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hforward : p ∉ B := fun h ↦ hpnot (Finset.mem_union_left _ h)
  have hreverse : p.swap ∉ B := by
    intro h
    apply hpnot
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨p.swap, h, Prod.swap_swap p⟩
  have hswap : p.swap ∈ E := by
    obtain ⟨hx, hy, he⟩ := mem_samePairs.mp hp
    exact mem_samePairs.mpr ⟨hy, hx, he.symm⟩
  refine ⟨freeMask I p.1 p.2, freeMask_subset I p.1 p.2, ?_, ?_⟩
  · exact le_of_not_gt (fun h ↦ hforward (Finset.mem_filter.mpr ⟨hp, h⟩))
  · have hr := le_of_not_gt (fun h ↦ hreverse (Finset.mem_filter.mpr ⟨hswap, h⟩))
    apply (Nat.mul_le_mul_left A.card (projection_card_mono S ?_)).trans hr
    exact Finset.union_subset_union_right (complement_freeMask_subset_reverse I p.1 p.2)

end
end Erdos539Geometry
