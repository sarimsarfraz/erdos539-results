/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntegerGeometry
import Mathlib.Tactic.Ring

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι κ : Type*}

/-- Two blocks translated in opposite directions at an integral level. -/
def glueVector (M g : ℤ) (x : ι → ℤ) (y : κ → ℤ) : ι ⊕ κ → ℤ :=
  Sum.elim (fun i ↦ x i + g * M) (fun j ↦ y j - g * M)

def gluing (F : Finset (ι → ℤ)) (G : Finset (κ → ℤ)) (K : ℕ) (M : ℤ) :
    Finset (ι ⊕ κ → ℤ) :=
  ((Finset.range K ×ˢ F) ×ˢ G).image (fun p ↦ glueVector M p.1.1 p.1.2 p.2)

@[simp] theorem mem_gluing {F : Finset (ι → ℤ)} {G : Finset (κ → ℤ)} {K : ℕ} {M : ℤ}
    {z : ι ⊕ κ → ℤ} :
    z ∈ gluing F G K M ↔ ∃ t < K, ∃ x ∈ F, ∃ y ∈ G, glueVector M t x y = z := by
  classical
  simp only [gluing, Finset.mem_image, Prod.exists, Finset.mem_product, Finset.mem_range]
  aesop

/-- Separation in a single first-block coordinate recovers the level. -/
theorem glueVector_injective_of_gap {F : Finset (ι → ℤ)} {M : ℤ}
    (hM : 0 < M) (hgap : HasCoordinateGap F M) (i : ι)
    {g h : ℤ} {x x' : ι → ℤ} {y y' : κ → ℤ} (hx : x ∈ F) (hx' : x' ∈ F)
    (he : glueVector M g x y = glueVector M h x' y') :
    g = h ∧ x = x' ∧ y = y' := by
  have hi := congrFun he (Sum.inl i)
  change x i + g * M = x' i + h * M at hi
  have hd := abs_lt.mp (hgap x hx x' hx' i)
  have hgh : g = h := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hlt
    · have : g + 1 ≤ h := by omega
      nlinarith
    · have : h + 1 ≤ g := by omega
      nlinarith
  refine ⟨hgh, ?_, ?_⟩
  · funext j
    have hj := congrFun he (Sum.inl j)
    change x j + g * M = x' j + h * M at hj
    rw [hgh] at hj
    exact add_right_cancel hj
  · funext j
    have hj := congrFun he (Sum.inr j)
    change y j - g * M = y' j - h * M at hj
    rw [hgh] at hj
    exact sub_left_injective hj

theorem gluing_card {F : Finset (ι → ℤ)} (G : Finset (κ → ℤ)) (K : ℕ) {M : ℤ}
    (hM : 0 < M) (hgap : HasCoordinateGap F M) (i : ι) :
    (gluing F G K M).card = K * F.card * G.card := by
  classical
  rw [gluing, Finset.card_image_of_injOn]
  · simp only [Finset.card_product, Finset.card_range]
  · intro p hp q hq he
    have hpF := (Finset.mem_product.mp (Finset.mem_product.mp hp).1).2
    have hqF := (Finset.mem_product.mp (Finset.mem_product.mp hq).1).2
    obtain ⟨ht, hx, hy⟩ := glueVector_injective_of_gap hM hgap i hpF hqF he
    have ht' : p.1.1 = q.1.1 := by exact_mod_cast ht
    exact Prod.ext (Prod.ext ht' hx) hy

theorem glueVector_sub (M g h : ℤ) (x x' : ι → ℤ) (y y' : κ → ℤ) :
    glueVector M g x y - glueVector M h x' y' = glueVector M (g - h) (x - x') (y - y') := by
  funext i
  cases i with
  | inl i => simp only [Pi.sub_apply, glueVector, Sum.elim_inl]; ring
  | inr i => simp only [Pi.sub_apply, glueVector, Sum.elim_inr]; ring

theorem intPdiff_glueVector_same (M g : ℤ) (x x' : ι → ℤ) (y y' : κ → ℤ) :
    intPdiff (glueVector M g x y) (glueVector M g x' y') =
      Sum.elim (intPdiff x x') (intPdiff y y') := by
  funext i
  cases i with
  | inl i => simp [intPdiff, glueVector]
  | inr i => simp [intPdiff, glueVector]

/-- Above the diagonal of the level pair, only the first block survives. -/
theorem intPdiff_glueVector_of_gt {F : Finset (ι → ℤ)} {G : Finset (κ → ℤ)} {M : ℤ}
    (hM : 0 < M) (hF : HasCoordinateGap F M) (hG : HasCoordinateGap G M)
    {g h : ℤ} (hgh : h < g) {x x' : ι → ℤ} {y y' : κ → ℤ}
    (hx : x ∈ F) (hx' : x' ∈ F) (hy : y ∈ G) (hy' : y' ∈ G) :
    intPdiff (glueVector M g x y) (glueVector M h x' y') =
      Sum.elim (fun i ↦ (x - x') i + (g - h) * M) (fun _ ↦ 0) := by
  have hg : h + 1 ≤ g := by omega
  funext i
  cases i with
  | inl i =>
    have hb := abs_lt.mp (hF x hx x' hx' i)
    change max (x i + g * M - (x' i + h * M)) 0 = x i - x' i + (g - h) * M
    rw [max_eq_left (by nlinarith : 0 ≤ x i + g * M - (x' i + h * M))]
    ring
  | inr i =>
    have hb := abs_lt.mp (hG y hy y' hy' i)
    change max (y i - g * M - (y' i - h * M)) 0 = 0
    exact max_eq_right (by nlinarith)

/-- Below the diagonal of the level pair, only the second block survives. -/
theorem intPdiff_glueVector_of_lt {F : Finset (ι → ℤ)} {G : Finset (κ → ℤ)} {M : ℤ}
    (hM : 0 < M) (hF : HasCoordinateGap F M) (hG : HasCoordinateGap G M)
    {g h : ℤ} (hgh : g < h) {x x' : ι → ℤ} {y y' : κ → ℤ}
    (hx : x ∈ F) (hx' : x' ∈ F) (hy : y ∈ G) (hy' : y' ∈ G) :
    intPdiff (glueVector M g x y) (glueVector M h x' y') =
      Sum.elim (fun _ ↦ 0) (fun i ↦ (y - y') i + (h - g) * M) := by
  have hg : g + 1 ≤ h := by omega
  funext i
  cases i with
  | inl i =>
    have hb := abs_lt.mp (hF x hx x' hx' i)
    change max (x i + g * M - (x' i + h * M)) 0 = 0
    exact max_eq_right (by nlinarith)
  | inr i =>
    have hb := abs_lt.mp (hG y hy y' hy' i)
    change max (y i - g * M - (y' i - h * M)) 0 = y i - y' i + (h - g) * M
    rw [max_eq_left (by nlinarith : 0 ≤ y i - g * M - (y' i - h * M))]
    ring

/-- The ordinary-difference estimate needed to iterate the construction.
No separation assumption is needed for this upper bound. -/
theorem gluing_integerDifferences_card_le (F : Finset (ι → ℤ))
    (G : Finset (κ → ℤ)) (K : ℕ) (M : ℤ) :
    (integerDifferences (gluing F G K M)).card ≤
      (2 * K - 1) * (integerDifferences F).card * (integerDifferences G).card := by
  classical
  let levels : Finset ℤ := Finset.Icc (1 - (K : ℤ)) ((K : ℤ) - 1)
  let T := (levels ×ˢ integerDifferences F) ×ˢ integerDifferences G
  let f := fun p : (ℤ × (ι → ℤ)) × (κ → ℤ) ↦ glueVector M p.1.1 p.1.2 p.2
  have hsub : integerDifferences (gluing F G K M) ⊆ T.image f := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_integerDifferences.mp hz
    obtain ⟨t, ht, x, hx, y, hy, rfl⟩ := mem_gluing.mp hu
    obtain ⟨s, hs, x', hx', y', hy', rfl⟩ := mem_gluing.mp hv
    have hlev : (t : ℤ) - s ∈ levels := by
      change (t : ℤ) - s ∈ Finset.Icc (1 - (K : ℤ)) ((K : ℤ) - 1)
      simp only [Finset.mem_Icc]
      constructor <;> omega
    apply Finset.mem_image.mpr
    refine ⟨(((t : ℤ) - s, x - x'), y - y'), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hlev,
        mem_integerDifferences.mpr ⟨x, hx, x', hx', rfl⟩⟩,
        mem_integerDifferences.mpr ⟨y, hy, y', hy', rfl⟩⟩
    · exact (glueVector_sub M t s x x' y y').symm
  have hlevcard : levels.card = 2 * K - 1 := by
    dsimp only [levels]
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ (T.image f).card := Finset.card_le_card hsub
    _ ≤ T.card := Finset.card_image_le
    _ = _ := by simp only [T, Finset.card_product, hlevcard]

/-- The three sign regimes of the level difference give the sharp gluing
upper estimate for positive differences. -/
theorem gluing_integerPositiveDifferences_card_le {F : Finset (ι → ℤ)}
    {G : Finset (κ → ℤ)} (K : ℕ) {M : ℤ} (hM : 0 < M)
    (hF : HasCoordinateGap F M) (hG : HasCoordinateGap G M) :
    (integerPositiveDifferences (gluing F G K M)).card ≤
      (integerPositiveDifferences F).card * (integerPositiveDifferences G).card +
      (K - 1) * ((integerDifferences F).card + (integerDifferences G).card) := by
  classical
  let levels : Finset ℤ := Finset.Ico 1 (K : ℤ)
  let Z := (integerPositiveDifferences F ×ˢ integerPositiveDifferences G).image
    (fun p ↦ Sum.elim p.1 p.2)
  let P := (levels ×ˢ integerDifferences F).image
    (fun p ↦ Sum.elim (fun i ↦ p.2 i + p.1 * M) (fun _ : κ ↦ (0 : ℤ)))
  let N := (levels ×ˢ integerDifferences G).image
    (fun p ↦ Sum.elim (fun _ : ι ↦ (0 : ℤ)) (fun i ↦ p.2 i + p.1 * M))
  have hsub : integerPositiveDifferences (gluing F G K M) ⊆ (Z ∪ P) ∪ N := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_integerPositiveDifferences.mp hz
    obtain ⟨t, ht, x, hx, y, hy, rfl⟩ := mem_gluing.mp hu
    obtain ⟨s, hs, x', hx', y', hy', rfl⟩ := mem_gluing.mp hv
    rcases lt_trichotomy t s with hts | hts | hts
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨((s : ℤ) - t, y - y'), Finset.mem_product.mpr ⟨?_,
        mem_integerDifferences.mpr ⟨y, hy, y', hy', rfl⟩⟩, ?_⟩
      · change (s : ℤ) - t ∈ Finset.Ico 1 (K : ℤ)
        simp only [Finset.mem_Ico]
        constructor <;> omega
      · exact (intPdiff_glueVector_of_lt hM hF hG (by exact_mod_cast hts) hx hx' hy hy').symm
    · subst s
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨(intPdiff x x', intPdiff y y'), Finset.mem_product.mpr
        ⟨mem_integerPositiveDifferences.mpr ⟨x, hx, x', hx', rfl⟩,
        mem_integerPositiveDifferences.mpr ⟨y, hy, y', hy', rfl⟩⟩, ?_⟩
      exact (intPdiff_glueVector_same M t x x' y y').symm
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨((t : ℤ) - s, x - x'), Finset.mem_product.mpr ⟨?_,
        mem_integerDifferences.mpr ⟨x, hx, x', hx', rfl⟩⟩, ?_⟩
      · change (t : ℤ) - s ∈ Finset.Ico 1 (K : ℤ)
        simp only [Finset.mem_Ico]
        constructor <;> omega
      · exact (intPdiff_glueVector_of_gt hM hF hG (by exact_mod_cast hts) hx hx' hy hy').symm
  have hlevcard : levels.card = K - 1 := by
    dsimp only [levels]
    rw [Int.card_Ico]
    omega
  have hZ : Z.card ≤ (integerPositiveDifferences F).card * (integerPositiveDifferences G).card :=
    Finset.card_image_le.trans (by rw [Finset.card_product])
  have hP : P.card ≤ (K - 1) * (integerDifferences F).card :=
    Finset.card_image_le.trans (by rw [Finset.card_product, hlevcard])
  have hN : N.card ≤ (K - 1) * (integerDifferences G).card :=
    Finset.card_image_le.trans (by rw [Finset.card_product, hlevcard])
  have hU := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hUP := Finset.card_union_le Z P
  nlinarith

end
end Erdos539Geometry
