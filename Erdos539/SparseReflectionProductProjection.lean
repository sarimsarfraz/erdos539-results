/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SparseReflectionProductCut

namespace Erdos539Geometry
noncomputable section
open scoped Classical
local instance productProjectionRealDecidableEq {ι : Type} : DecidableEq (ι → ℝ) := Classical.decEq _
local instance productProjectionStripDecidableEq : DecidableEq ((Unit ⊕ Unit) → ℤ) := inferInstance
local instance productProjectionIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _
local instance productProjectionLeftDecidableEq : DecidableEq (reflectionProductLeft → ℝ) :=
  fun a b ↦ @Fintype.decidablePiFintype reflectionProductLeft (fun _ ↦ ℝ)
    (fun _ ↦ Classical.decEq ℝ) inferInstance a b
local instance productProjectionRightDecidableEq : DecidableEq (reflectionProductRight → ℝ) :=
  fun a b ↦ @Fintype.decidablePiFintype reflectionProductRight (fun _ ↦ ℝ)
    (fun _ ↦ Classical.decEq ℝ) inferInstance a b

theorem sparseReflectionProduct_left_card_eq (S : Finset ℤ) {T : ℕ} (hT : 0 < T) :
    (projection (sparseReflectionProduct S T) reflectionProductLeft).card = S.card * T ^ 2 := by
  apply le_antisymm (sparseReflectionProduct_left_card S T)
  let F : ℤ × (ℤ × ℤ) → (reflectionProductLeft → ℝ) := fun p ↦
    project reflectionProductLeft (reflectionProductEmbedding (p.1, stripEncode (4 * (T : ℤ)) (p.2, 0)))
  let D := S ×ˢ (scalarInterval T ×ˢ scalarInterval T)
  have h0 : (0 : ℤ) ∈ scalarInterval T := by simp [scalarInterval, hT]
  have hsub : D.image F ⊆ projection (sparseReflectionProduct S T) reflectionProductLeft := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_image.mpr ⟨reflectionProductEmbedding (p.1, stripEncode (4 * (T : ℤ)) (p.2, 0)), ?_, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(p.1, stripEncode (4 * (T : ℤ)) (p.2, 0)), Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).1, ?_⟩, rfl⟩
    exact Finset.mem_image.mpr ⟨(p.2, 0), Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).2, h0⟩, rfl⟩
  have hinj : Set.InjOn F D := by
    intro p hp q hq he
    let i0 : reflectionProductLeft := ⟨Sum.inl (), by simp [reflectionProductLeft]⟩
    let i1 : reflectionProductLeft := ⟨Sum.inr (Sum.inl ()), by simp [reflectionProductLeft]⟩
    have hs := congrFun he i0
    have ht := congrFun he i1
    change (p.1 : ℝ) = (q.1 : ℝ) at hs
    change ((4 * (T : ℤ) * p.2.1 + p.2.2 : ℤ) : ℝ) = ((4 * (T : ℤ) * q.2.1 + q.2.2 : ℤ) : ℝ) at ht
    have ht' : separatedPair (4 * (T : ℤ)) p.2 = separatedPair (4 * (T : ℤ)) q.2 := by exact_mod_cast ht
    exact Prod.ext (by exact_mod_cast hs) (separatedPair_interval_injOn (by omega)
      (Finset.mem_product.mp hp).2 (Finset.mem_product.mp hq).2 ht')
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hh
  simpa only [D, Finset.card_product, scalarInterval_card, pow_two, Nat.mul_assoc] using hh

theorem sparseReflectionProduct_right_card_eq {S : Finset ℤ} (hS : S.Nonempty) {T : ℕ} (hT : 0 < T) :
    (projection (sparseReflectionProduct S T) reflectionProductRight).card = T ^ 2 := by
  apply le_antisymm (sparseReflectionProduct_right_card S T)
  obtain ⟨s, hs⟩ := hS
  let F : ℤ × ℤ → (reflectionProductRight → ℝ) := fun p ↦
    project reflectionProductRight (reflectionProductEmbedding (s, stripEncode (4 * (T : ℤ)) ((p.1, 0), p.2)))
  let D := scalarInterval T ×ˢ scalarInterval T
  have h0 : (0 : ℤ) ∈ scalarInterval T := by simp [scalarInterval, hT]
  have hsub : D.image F ⊆ projection (sparseReflectionProduct S T) reflectionProductRight := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_image.mpr ⟨reflectionProductEmbedding (s, stripEncode (4 * (T : ℤ)) ((p.1, 0), p.2)), ?_, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(s, stripEncode (4 * (T : ℤ)) ((p.1, 0), p.2)), Finset.mem_product.mpr ⟨hs, ?_⟩, rfl⟩
    exact Finset.mem_image.mpr ⟨((p.1, 0), p.2), Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).1, h0⟩, (Finset.mem_product.mp hp).2⟩, rfl⟩
  have hinj : Set.InjOn F D := by
    intro p hp q hq he
    let i : reflectionProductRight := ⟨Sum.inr (Sum.inr ()), by simp [reflectionProductRight]⟩
    have ht := congrFun he i
    change ((p.2 - 4 * (T : ℤ) * p.1 : ℤ) : ℝ) = ((q.2 - 4 * (T : ℤ) * q.1 : ℤ) : ℝ) at ht
    have ht' : p.2 - 4 * (T : ℤ) * p.1 = q.2 - 4 * (T : ℤ) * q.1 := by exact_mod_cast ht
    have hp2 := Finset.mem_Ico.mp (Finset.mem_product.mp hp).2
    have hq2 := Finset.mem_Ico.mp (Finset.mem_product.mp hq).2
    have hh := separatedPair_injective (by omega : (0 : ℤ) < 4 * T)
      (a := (-p.1, p.2)) (b := (-q.1, q.2)) ⟨hp2.1, by omega⟩ ⟨hq2.1, by omega⟩ (by
        change 4 * (T : ℤ) * (-p.1) + p.2 = 4 * (T : ℤ) * (-q.1) + q.2
        linarith)
    have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    exact Prod.ext (by dsimp only at h1; omega) h2
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hh
  simpa only [D, Finset.card_product, scalarInterval_card, pow_two] using hh

end
end Erdos539Geometry
