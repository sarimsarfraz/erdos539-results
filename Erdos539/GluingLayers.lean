/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.LayerTranslations
import Erdos539.PowerConstruction

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι κ : Type}

/-- A fixed-instance real model, independent of available finite-coordinate instances. -/
def integerRealSet (F : Finset (ι → ℤ)) : Finset (ι → ℝ) := F.image integerToReal

@[simp] theorem mem_integerRealSet {F : Finset (ι → ℤ)} {z : ι → ℝ} :
    z ∈ integerRealSet F ↔ ∃ x ∈ F, integerToReal x = z := Finset.mem_image

theorem integerRealSet_nonempty {F : Finset (ι → ℤ)} (hF : F.Nonempty) :
    (integerRealSet F).Nonempty := hF.image integerToReal

def glueLeftLayer (F : Finset (ι → ℤ)) (M : ℤ) (t : ℕ) : Finset (ι → ℝ) :=
  translateRealSet (integerRealSet F) (fun _ ↦ (((t : ℤ) * M : ℤ) : ℝ))

def glueRightLayer (G : Finset (κ → ℤ)) (M : ℤ) (t : ℕ) : Finset (κ → ℝ) :=
  translateRealSet (integerRealSet G) (fun _ ↦ -(((t : ℤ) * M : ℤ) : ℝ))

/-- The original integer gluing is literally an ordered product of translated layers. -/
theorem gluing_real_eq_layers (F : Finset (ι → ℤ)) (G : Finset (κ → ℤ)) (K : ℕ) (M : ℤ) :
    integerRealSet (gluing F G K M) =
      orderedLayerProduct (Finset.range K) (glueLeftLayer F M) (glueRightLayer G M) := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := mem_integerRealSet.mp hz
    obtain ⟨t, ht, x, hx, y, hy, rfl⟩ := mem_gluing.mp hw
    apply mem_orderedLayerProduct.mpr
    refine ⟨t, Finset.mem_range.mpr ht, mem_coordinateProduct.mpr
      ⟨integerToReal x + (fun _ ↦ (((t : ℤ) * M : ℤ) : ℝ)),
      mem_translateRealSet.mpr ⟨integerToReal x, mem_integerRealSet.mpr ⟨x, hx, rfl⟩, rfl⟩,
      integerToReal y + (fun _ ↦ -(((t : ℤ) * M : ℤ) : ℝ)),
      mem_translateRealSet.mpr ⟨integerToReal y, mem_integerRealSet.mpr ⟨y, hy, rfl⟩, rfl⟩, ?_⟩⟩
    funext k
    cases k <;> simp [integerToReal, glueVector, sub_eq_add_neg]
  · intro hz
    obtain ⟨t, ht, hz⟩ := mem_orderedLayerProduct.mp hz
    obtain ⟨x', hx', y', hy', rfl⟩ := mem_coordinateProduct.mp hz
    obtain ⟨x'', hx'', rfl⟩ := mem_translateRealSet.mp hx'
    obtain ⟨y'', hy'', rfl⟩ := mem_translateRealSet.mp hy'
    obtain ⟨x, hx, rfl⟩ := mem_integerRealSet.mp hx''
    obtain ⟨y, hy, rfl⟩ := mem_integerRealSet.mp hy''
    refine mem_integerRealSet.mpr ⟨glueVector M t x y,
      mem_gluing.mpr ⟨t, Finset.mem_range.mp ht, x, hx, y, hy, rfl⟩, ?_⟩
    funext k
    cases k <;> simp [integerToReal, glueVector, sub_eq_add_neg]

theorem gluing_isOrderedLayers {F : Finset (ι → ℤ)} {G : Finset (κ → ℤ)} (K : ℕ)
    {M : ℤ} (hM : 0 < M) (hF : HasCoordinateGap F M) (hG : HasCoordinateGap G M) :
    IsOrderedLayers (Finset.range K) (glueLeftLayer F M) (glueRightLayer G M) := by
  constructor
  · intro t _ht s _hs hts x hx y hy k
    obtain ⟨x', hx', rfl⟩ := mem_translateRealSet.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_translateRealSet.mp hy
    obtain ⟨u, hu, rfl⟩ := mem_integerRealSet.mp hx'
    obtain ⟨v, hv, rfl⟩ := mem_integerRealSet.mp hy'
    have hg := abs_lt.mp (hF u hu v hv k)
    have hts' : (t : ℤ) + 1 ≤ s := by omega
    have hh : u k + (t : ℤ) * M < v k + (s : ℤ) * M := by nlinarith
    change (u k : ℝ) + (((t : ℤ) * M : ℤ) : ℝ) < (v k : ℝ) + (((s : ℤ) * M : ℤ) : ℝ)
    exact_mod_cast hh
  · intro t _ht s _hs hts x hx y hy k
    obtain ⟨x', hx', rfl⟩ := mem_translateRealSet.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_translateRealSet.mp hy
    obtain ⟨u, hu, rfl⟩ := mem_integerRealSet.mp hx'
    obtain ⟨v, hv, rfl⟩ := mem_integerRealSet.mp hy'
    have hg := abs_lt.mp (hG v hv u hu k)
    have hts' : (t : ℤ) + 1 ≤ s := by omega
    have hh : v k + -((s : ℤ) * M) < u k + -((t : ℤ) * M) := by nlinarith
    change (v k : ℝ) + -(((s : ℤ) * M : ℤ) : ℝ) < (u k : ℝ) + -(((t : ℤ) * M : ℤ) : ℝ)
    exact_mod_cast hh

/-- Separated gluing preserves the exact recursive layer class. -/
theorem LayerConstructible.gluing [Fintype ι] [Fintype κ]
    {F : Finset (ι → ℤ)} {G : Finset (κ → ℤ)} (hCF : LayerConstructible ι (integerRealSet F))
    (hCG : LayerConstructible κ (integerRealSet G)) (hFn : F.Nonempty) (hGn : G.Nonempty)
    {K : ℕ} (hK : 0 < K) {M : ℤ} (hM : 0 < M)
    (hF : HasCoordinateGap F M) (hG : HasCoordinateGap G M) :
    LayerConstructible (ι ⊕ κ) (integerRealSet (gluing F G K M)) := by
  rw [gluing_real_eq_layers]
  exact .layers (Finset.range K) ⟨0, Finset.mem_range.mpr hK⟩ _ _
    (gluing_isOrderedLayers K hM hF hG)
    (fun _ _ ↦ translateRealSet_nonempty (integerRealSet_nonempty hFn) _)
    (fun _ _ ↦ translateRealSet_nonempty (integerRealSet_nonempty hGn) _)
    (fun _ _ ↦ hCF.translate _) (fun _ _ ↦ hCG.translate _)

/-- Coordinate reindexing commutes exactly with the integral-to-real model. -/
theorem integerRealSet_reindex [DecidableEq (κ → ℤ)] (e : ι ≃ κ) (F : Finset (ι → ℤ)) :
    integerRealSet (F.image (reindexInteger e)) = reindexRealSet e (integerRealSet F) := by
  ext z
  simp only [mem_integerRealSet, Finset.mem_image, mem_reindexRealSet]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨integerToReal x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨reindexInteger e x, ⟨x, hx, rfl⟩, rfl⟩

/-- The numerical gluing construction and its layer certificate are realized together. -/
theorem exists_layer_gluing [Fintype ι] [Fintype κ]
    (F : Finset (ι → ℤ)) (G : Finset (κ → ℤ)) (K : ℕ) (i : ι)
    (hCF : LayerConstructible ι (integerRealSet F)) (hCG : LayerConstructible κ (integerRealSet G))
    (hFn : F.Nonempty) (hGn : G.Nonempty) (hK : 0 < K) :
    ∃ H : Finset (ι ⊕ κ → ℤ),
      H.card = K * F.card * G.card ∧
      (integerPositiveDifferences H).card ≤
        (integerPositiveDifferences F).card * (integerPositiveDifferences G).card +
        (K - 1) * ((integerDifferences F).card + (integerDifferences G).card) ∧
      (integerDifferences H).card ≤
        (2 * K - 1) * (integerDifferences F).card * (integerDifferences G).card ∧
      LayerConstructible (ι ⊕ κ) (integerRealSet H) := by
  obtain ⟨M₁, hM₁, hF⟩ := exists_coordinate_gap F
  obtain ⟨M₂, _hM₂, hG⟩ := exists_coordinate_gap G
  let M := max M₁ M₂
  have hM : 0 < M := hM₁.trans_le (le_max_left _ _)
  have hF' : HasCoordinateGap F M := fun x hx y hy i ↦ (hF x hx y hy i).trans_le (le_max_left _ _)
  have hG' : HasCoordinateGap G M := fun x hx y hy i ↦ (hG x hx y hy i).trans_le (le_max_right _ _)
  exact ⟨gluing F G K M, gluing_card G K hM hF' i,
    gluing_integerPositiveDifferences_card_le K hM hF' hG',
    gluing_integerDifferences_card_le F G K M,
    hCF.gluing hCG hFn hGn hK hM hF' hG'⟩

end
end Erdos539Geometry
