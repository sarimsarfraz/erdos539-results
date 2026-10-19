/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CollectiveReflectedSupport
import Erdos539.ReflectedSignProjection
import Erdos539.SignClasses

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι H : Type*} [AddCommGroup H] [DecidableEq H]
local instance collectiveSignVectorDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance collectiveSignImageDecidableEq (S : Finset (ι → ℝ)) (φ : (ι → ℝ) → H) :
    DecidableEq (S.image φ) := Classical.decEq _

def originalFiberReflectionCenter (S : Finset (ι → ℝ)) (φ : (ι → ℝ) →+ H) (x : ι → ℝ) : ι → ℝ :=
  if hx : x ∈ S then collectiveReflectedCenter S φ (imageEndpoint S φ ⟨x, hx⟩) else 0

theorem originalFiberReflectionCenter_eq (S : Finset (ι → ℝ)) (φ : (ι → ℝ) →+ H)
    (y : S.image φ) {x : ι → ℝ} (hx : x ∈ fiber S φ y.val) :
    originalFiberReflectionCenter S φ x = collectiveReflectedCenter S φ y := by
  obtain ⟨hxS, hxy⟩ := mem_fiber.mp hx
  simp only [originalFiberReflectionCenter, dif_pos hxS]
  congr 1
  exact Subtype.ext hxy

def collectiveReflectionSignMask (S : Finset (ι → ℝ)) (φ : (ι → ℝ) →+ H) (B : Finset ι) (x : ι → ℝ) : Finset ι :=
  reflectionSignMask B (originalFiberReflectionCenter S φ x) x

/-- One common sign cell is chosen after summing the retained sizes over
all original fibers. The center used for each point is its own fiber's center. -/
theorem exists_common_reflected_sign_cell {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (φ : (ι → ℝ) →+ H) (B : Finset ι) :
    ∃ (P : Finset ι) (A : Finset (ι → ℝ)), P ⊆ B ∧ A ⊆ collectiveReflectedSubset S φ ∧ A.Nonempty ∧
      (S.card : ℝ) ^ 2 / ((2 : ℝ) ^ B.card * (S - S).card) ≤ A.card ∧
      ∀ x ∈ A, collectiveReflectionSignMask S φ B x = P := by
  let R := collectiveReflectedSubset S φ
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hd : (0 : ℝ) < (S - S).card := by
    obtain ⟨a, ha⟩ := hS
    exact_mod_cast (show (S - S).Nonempty from ⟨0, Finset.mem_sub.mpr ⟨a, ha, a, ha, sub_self a⟩⟩).card_pos
  have hl := collectiveReflectedSubset_card_lower hS φ
  have hR : R.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < R.card := (div_pos (sq_pos_of_pos hn) hd).trans_le hl
    exact_mod_cast hpos
  obtain ⟨a, ha, hc⟩ := exists_large_fiber R hR (collectiveReflectionSignMask S φ B)
  let P := collectiveReflectionSignMask S φ B a
  let A := fiber R (collectiveReflectionSignMask S φ B) P
  have hP : P ⊆ B := reflectionSignMask_subset B _ a
  have hlabels : (R.image (collectiveReflectionSignMask S φ B)).card ≤ 2 ^ B.card := by
    have hs : R.image (collectiveReflectionSignMask S φ B) ⊆ B.powerset := by
      intro Q hQ
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hQ
      exact Finset.mem_powerset.mpr (reflectionSignMask_subset B _ x)
    simpa only [Finset.card_powerset] using Finset.card_le_card hs
  have hsize : R.card ≤ 2 ^ B.card * A.card := hc.trans (Nat.mul_le_mul_right _ hlabels)
  refine ⟨P, A, hP, fun x hx ↦ (mem_fiber.mp hx).1, ⟨a, mem_fiber.mpr ⟨ha, rfl⟩⟩, ?_, ?_⟩
  · have hsizeR : (R.card : ℝ) ≤ (2 : ℝ) ^ B.card * A.card := by exact_mod_cast hsize
    apply (div_le_iff₀ (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _) hd)).mpr
    have hl' := (div_le_iff₀ hd).mp hl
    have hm := mul_le_mul_of_nonneg_right hsizeR hd.le
    dsimp only [R] at hm
    nlinarith
  · intro x hx
    exact (mem_fiber.mp hx).2

end
end Erdos539Geometry
