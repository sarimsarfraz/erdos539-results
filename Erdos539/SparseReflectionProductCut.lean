/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SparseReflectionProductGeometry
import Erdos539.StationaryCoordinateEnergy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
local instance productCutRealDecidableEq {ι : Type} : DecidableEq (ι → ℝ) := Classical.decEq _
local instance productCutStripDecidableEq : DecidableEq ((Unit ⊕ Unit) → ℤ) := inferInstance
local instance productCutIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _

def reflectionProductLeft : Finset ReflectionProductCoordinates := {Sum.inl (), Sum.inr (Sum.inl ())}
def reflectionProductRight : Finset ReflectionProductCoordinates := {Sum.inr (Sum.inr ())}

local instance productCutLeftDecidableEq : DecidableEq (reflectionProductLeft → ℝ) :=
  fun a b ↦ @Fintype.decidablePiFintype reflectionProductLeft (fun _ ↦ ℝ)
    (fun _ ↦ Classical.decEq ℝ) inferInstance a b
local instance productCutRightDecidableEq : DecidableEq (reflectionProductRight → ℝ) :=
  fun a b ↦ @Fintype.decidablePiFintype reflectionProductRight (fun _ ↦ ℝ)
    (fun _ ↦ Classical.decEq ℝ) inferInstance a b

theorem reflectionProductCut_disjoint : Disjoint reflectionProductLeft reflectionProductRight := by
  simp [reflectionProductLeft, reflectionProductRight]

theorem reflectionProductCut_cover : reflectionProductLeft ∪ reflectionProductRight = Finset.univ := by
  ext i
  rcases i with ⟨⟨⟩⟩ | ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩⟩ <;> simp [reflectionProductLeft, reflectionProductRight]

theorem sparseReflectionProduct_left_card (S : Finset ℤ) (T : ℕ) :
    (projection (sparseReflectionProduct S T) reflectionProductLeft).card ≤ S.card * T ^ 2 := by
  let F : ℤ × (ℤ × ℤ) → (reflectionProductLeft → ℝ) := fun p i ↦
    match i.val with
    | Sum.inl _ => (p.1 : ℝ)
    | Sum.inr _ => ((4 * (T : ℤ) * p.2.1 + p.2.2 : ℤ) : ℝ)
  have hsub : projection (sparseReflectionProduct S T) reflectionProductLeft ⊆
      (S ×ˢ (scalarInterval T ×ˢ scalarInterval T)).image F := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨⟨s, v⟩, hsv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hs, hv⟩ := Finset.mem_product.mp hsv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨(s, a.1), Finset.mem_product.mpr ⟨hs, (Finset.mem_product.mp ha).1⟩, ?_⟩
    funext i
    have hi := i.property
    simp only [reflectionProductLeft, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · simp [F, project, reflectionProductEmbedding, hi]
    · simp [F, project, reflectionProductEmbedding, integerToReal, stripEncode, hi]
  calc
    _ ≤ ((S ×ˢ (scalarInterval T ×ˢ scalarInterval T)).image F).card := Finset.card_le_card hsub
    _ ≤ (S ×ˢ (scalarInterval T ×ˢ scalarInterval T)).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_product, Finset.card_product, scalarInterval_card]; ring

theorem sparseReflectionProduct_right_card (S : Finset ℤ) (T : ℕ) :
    (projection (sparseReflectionProduct S T) reflectionProductRight).card ≤ T ^ 2 := by
  let F : ℤ × ℤ → (reflectionProductRight → ℝ) := fun p _ ↦ ((p.2 - 4 * (T : ℤ) * p.1 : ℤ) : ℝ)
  have hsub : projection (sparseReflectionProduct S T) reflectionProductRight ⊆
      (scalarInterval T ×ˢ scalarInterval T).image F := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨⟨s, v⟩, hsv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_, hv⟩ := Finset.mem_product.mp hsv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hab, hc⟩ := Finset.mem_product.mp ha
    refine Finset.mem_image.mpr ⟨(a.1.1, a.2), Finset.mem_product.mpr ⟨(Finset.mem_product.mp hab).1, hc⟩, ?_⟩
    funext i
    have hi : i.val = Sum.inr (Sum.inr ()) := Finset.mem_singleton.mp i.property
    simp [F, project, reflectionProductEmbedding, integerToReal, stripEncode, hi]
  calc
    _ ≤ ((scalarInterval T ×ˢ scalarInterval T).image F).card := Finset.card_le_card hsub
    _ ≤ (scalarInterval T ×ˢ scalarInterval T).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_product, scalarInterval_card]; ring

/-- This explicit complementary coordinate cut controls both actual
marginals of every normalized endpoint weight with zero error. -/
theorem sparseReflectionProduct_actual_cut {S : Finset ℤ} (hS : S.Nonempty)
    {T : ℕ} (hT : 0 < T) (f : sparseReflectionProduct S T → ℝ) (hf : ∑ x, f x ^ 2 = 1) :
    actualMarginalEnergy (sparseReflectionProduct S T) (extendWeight _ f) reflectionProductLeft ≤
      maxFan (sparseReflectionProduct S T) ∧
    actualMarginalEnergy (sparseReflectionProduct S T) (extendWeight _ f) reflectionProductRight ≤
      maxFan (sparseReflectionProduct S T) := by
  letI : DecidableEq (reflectionProductLeft → ℝ) := Classical.decEq _
  letI : DecidableEq (reflectionProductRight → ℝ) := Classical.decEq _
  have hlCard : ((projection (sparseReflectionProduct S T) reflectionProductLeft).card : ℝ) ≤
      (S.card : ℝ) * (T : ℝ) ^ 2 := by exact_mod_cast sparseReflectionProduct_left_card S T
  have hrCard : ((projection (sparseReflectionProduct S T) reflectionProductRight).card : ℝ) ≤
      (T : ℝ) ^ 2 := by exact_mod_cast sparseReflectionProduct_right_card S T
  have hleft := ((actualMarginalEnergy_unit_bounds _ reflectionProductLeft f hf).2.trans
    (energyNorm_le_card _)).trans hlCard
  have hright := ((actualMarginalEnergy_unit_bounds _ reflectionProductRight f hf).2.trans
    (energyNorm_le_card _)).trans hrCard
  have hN : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have htl : (T : ℝ) ^ 2 ≤ 2 * (T : ℝ) ^ 2 - T := by nlinarith
  have hrightfan : (T : ℝ) ^ 2 ≤ (maxFan (sparseReflectionProduct S T) : ℝ) := by
    rw [sparseReflectionProduct_fan hS hT]
    have hmul := mul_le_mul_of_nonneg_right hN (by positivity : (0 : ℝ) ≤ (T : ℝ) ^ 2)
    nlinarith [mul_le_mul_of_nonneg_left htl (Nat.cast_nonneg (α := ℝ) S.card)]
  refine ⟨hleft.trans ?_, hright.trans hrightfan⟩
  rw [sparseReflectionProduct_fan hS hT]
  exact mul_le_mul_of_nonneg_left htl (Nat.cast_nonneg (α := ℝ) S.card)

end
end Erdos539Geometry
