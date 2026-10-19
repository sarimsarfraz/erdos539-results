/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PlanarFans

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*}

/-- Coordinate restriction is injective on a slice when the retained and
conditioned coordinates together cover the ambient space. -/
theorem projection_slice_card (F : Finset (ι → ℝ)) (I J : Finset ι)
    (hcover : ∀ i, i ∈ I ∨ i ∈ J) (a : ι → ℝ) :
    (projection (slice F I a) J).card = (slice F I a).card := by
  classical
  apply Finset.card_image_of_injOn
  intro x hx y hy h
  funext i
  rcases hcover i with hi | hj
  · exact (congrFun (mem_slice.mp hx).2 ⟨i, hi⟩).trans
      (congrFun (mem_slice.mp hy).2 ⟨i, hi⟩).symm
  · exact congrFun h ⟨i, hj⟩

theorem maxFan_projection_slice_le (F : Finset (ι → ℝ)) (I J : Finset ι) (a : ι → ℝ) :
    maxFan (projection (slice F I a) J) ≤ maxRestrictedFan F I := by
  classical
  have hproj : maxFan (projection (slice F I a) J) ≤ maxFan (slice F I a) := by
    apply Finset.sup_le
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    have he : fan (projection (slice F I a) J) (project J x) =
        (fan (slice F I a) x).image (project J) := by
      ext z
      simp only [mem_fan, projection, Finset.mem_image]
      constructor
      · rintro ⟨v, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨pdiff y x, ⟨y, hy, rfl⟩, rfl⟩
      · rintro ⟨v, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨project J y, ⟨y, hy, rfl⟩, rfl⟩
    rw [he]
    exact Finset.card_image_le.trans (card_fan_le_maxFan hx)
  exact hproj.trans (maxFan_slice_le_maxRestrictedFan F I a)

/-- Fiber averaging over projection values of the fixed parent. -/
theorem exists_large_slice {A S : Finset (ι → ℝ)} (hAS : A ⊆ S) (hA : A.Nonempty)
    (I : Finset ι) :
    ∃ a ∈ A, A.card ≤ (projection S I).card * (slice A I a).card := by
  classical
  obtain ⟨a, ha, hmax⟩ := A.exists_max_image (fun a ↦ (slice A I a).card) hA
  refine ⟨a, ha, ?_⟩
  have hf (b : I → ℝ) : (fiber A (project I) b).card ≤ (slice A I a).card := by
    by_cases hb : (fiber A (project I) b).Nonempty
    · obtain ⟨x, hx⟩ := hb
      have he : fiber A (project I) b = slice A I x := by
        dsimp only [slice]
        rw [(mem_fiber.mp hx).2]
      rw [he]
      exact hmax x (mem_fiber.mp hx).1
    · rw [Finset.not_nonempty_iff_eq_empty.mp hb]
      exact Nat.zero_le _
  have hmaps : (A : Set (ι → ℝ)).MapsTo (project I) (projection S I) :=
    fun x hx ↦ Finset.mem_image_of_mem _ (hAS hx)
  calc
    A.card = ∑ b ∈ projection S I, (fiber A (project I) b).card := card_eq_sum_card_parent A _ _ hmaps
    _ ≤ ∑ _b ∈ projection S I, (slice A I a).card := Finset.sum_le_sum (fun b _ ↦ hf b)
    _ = _ := by simp

/-- Transfer a lower-dimensional fan bound through a largest coordinate slice. -/
theorem restricted_log_bound_of_slice_bound {A S : Finset (ι → ℝ)}
    (hAS : A ⊆ S) (hA : A.Nonempty) (I J : Finset ι)
    (hcover : ∀ i, i ∈ I ∨ i ∈ J) (e c : ℝ) (he : 0 ≤ e)
    (hbound : ∀ F : Finset (J → ℝ), F.Nonempty → e * Real.log F.card - c ≤ Real.log (maxFan F)) :
    e * (Real.log A.card - Real.log (projection S I).card) - c ≤ Real.log (maxRestrictedFan A I) := by
  obtain ⟨a, ha, havg⟩ := exists_large_slice hAS hA I
  have hs : (slice A I a).Nonempty := ⟨a, mem_slice.mpr ⟨ha, rfl⟩⟩
  have hF : (projection (slice A I a) J).Nonempty := hs.image _
  have hn : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hP : (0 : ℝ) < (projection S I).card := by exact_mod_cast ((hA.mono hAS).image (project I)).card_pos
  have hslice : (0 : ℝ) < (slice A I a).card := by exact_mod_cast hs.card_pos
  have havg' : (A.card : ℝ) ≤ (projection S I).card * ((slice A I a).card : ℝ) := by exact_mod_cast havg
  have hl := Real.log_le_log hn havg'
  rw [Real.log_mul hP.ne' hslice.ne'] at hl
  have hf := hbound _ hF
  rw [projection_slice_card A I J hcover a] at hf
  have hM : (0 : ℝ) < maxFan (projection (slice A I a) J) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hF))
  have hmono := Real.log_le_log hM (show (maxFan (projection (slice A I a) J) : ℝ) ≤ maxRestrictedFan A I by
    exact_mod_cast maxFan_projection_slice_le A I J a)
  have he' := mul_le_mul_of_nonneg_left (show Real.log A.card - Real.log (projection S I).card ≤
    Real.log (slice A I a).card by linarith) he
  linarith

/-- General one-sided pruning, preserving the original anchor throughout. -/
theorem one_sided_log_pruning {A : Finset (ι → ℝ)} (hA : A.Nonempty)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hI : ∀ F : Finset (I → ℝ), F.Nonempty → a * Real.log F.card - c ≤ Real.log (maxFan F))
    (hJ : ∀ F : Finset (J → ℝ), F.Nonempty → b * Real.log F.card - d ≤ Real.log (maxFan F)) :
    a * (Real.log A.card - Real.log 2 - Real.log (projection A J).card) +
      b * (Real.log A.card - Real.log 2 - Real.log (projection A I).card) - c - d ≤ Real.log (maxFan A) := by
  classical
  have hhalf (K L : Finset ι) (hcov : ∀ i, i ∈ K ∨ i ∈ L) (e loss : ℝ) (he : 0 ≤ e)
      (hbound : ∀ F : Finset (L → ℝ), F.Nonempty → e * Real.log F.card - loss ≤ Real.log (maxFan F))
      (B : Finset (ι → ℝ)) (hBA : B ⊆ A) (hlarge : A.card ≤ 2 * B.card) :
      Real.exp (e * (Real.log A.card - Real.log 2 - Real.log (projection A K).card) - loss) ≤
        maxRestrictedFan B K := by
    have hB : B.Nonempty := Finset.card_pos.mp (by have := hA.card_pos; omega)
    have hbase := restricted_log_bound_of_slice_bound hBA hB K L hcov e loss he hbound
    have hn : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hbn : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
    have hl := Real.log_le_log hn (show (A.card : ℝ) ≤ 2 * B.card by exact_mod_cast hlarge)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hbn.ne'] at hl
    have hmul := mul_le_mul_of_nonneg_left (show Real.log A.card - Real.log 2 ≤ Real.log B.card by linarith) he
    have hM : (0 : ℝ) < maxRestrictedFan B K := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxRestrictedFan hB K))
    apply (Real.le_log_iff_exp_le hM).mp
    linarith
  have hp := aggregate_pruning hA I J hcover ∅ (Finset.empty_subset _) (Finset.empty_subset _)
    (Real.exp (a * (Real.log A.card - Real.log 2 - Real.log (projection A J).card) - c))
    (Real.exp (b * (Real.log A.card - Real.log 2 - Real.log (projection A I).card) - d))
    (Real.exp_pos _).le
    (hhalf J I (fun i ↦ (hcover i).symm) a c ha hI)
    (hhalf I J hcover b d hb hJ)
  rw [maxRestrictedFan_empty, ← Real.exp_add] at hp
  have hM : (0 : ℝ) < maxFan A := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hA))
  have hl := (Real.le_log_iff_exp_le hM).mpr hp
  linarith

theorem one_dimensional_maxFan_eq_card [Fintype ι] (hd : Fintype.card ι = 1)
    (F : Finset (ι → ℝ)) : maxFan F = F.card := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (show (Finset.univ : Finset ι).card = 1 by simpa using hd)
  have hcover : ∀ j, j ∈ (∅ : Finset ι) ∨ j = i := by
    intro j
    right
    exact Finset.mem_singleton.mp (hi ▸ Finset.mem_univ j)
  have h := card_slice_le_maxRestrictedFan_one_free F ∅ i hcover (fun _ ↦ 0)
  simp only [slice_empty, maxRestrictedFan_empty] at h
  exact le_antisymm (maxFan_le_card F) h

end
end Erdos539Geometry
