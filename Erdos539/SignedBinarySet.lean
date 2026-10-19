/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignedBinaryOrder
import Erdos539.LayerSharpness

namespace Erdos539Geometry
noncomputable section
open scoped Classical
variable {ι : Type} {m : ℕ}

def signedBinarySet (m : ℕ) (σ : Fin m → ι → Bool) : Finset (ι → ℤ) :=
  Finset.univ.image (signedBinaryCode m σ)

theorem signedBinarySet_card (σ : Fin m → ι → Bool) (i : ι) : (signedBinarySet m σ).card = 2 ^ m := by
  have hi : Function.Injective (signedBinaryCode m σ) := by
    intro η ξ he
    exact signedBinaryCode_coordinate_injective σ i (congrFun he i)
  rw [signedBinarySet, Finset.card_image_of_injective _ hi]
  simp

theorem signedBinarySet_real_mem (σ : Fin m → ι → Bool) {x : ι → ℝ} :
    x ∈ integerRealSet (signedBinarySet m σ) ↔ ∃ η, integerToReal (signedBinaryCode m σ η) = x := by
  simp only [mem_integerRealSet, signedBinarySet, Finset.mem_image, Finset.mem_univ, true_and]
  aesop

theorem signedBinarySet_no_between (σ : Fin m → ι → Bool) (i₀ : ι)
    (hfirst : ∀ j, σ j i₀ = true) (hs : Function.Injective σ)
    {a b c : ι → ℝ} (ha : a ∈ integerRealSet (signedBinarySet m σ))
    (hb : b ∈ integerRealSet (signedBinarySet m σ)) (hc : c ∈ integerRealSet (signedBinarySet m σ))
    (hab : a ≠ b) (hbc : b ≠ c) : ¬ InCornerBox a c b := by
  obtain ⟨η, rfl⟩ := (signedBinarySet_real_mem σ).mp ha
  obtain ⟨ξ, rfl⟩ := (signedBinarySet_real_mem σ).mp hb
  obtain ⟨ζ, rfl⟩ := (signedBinarySet_real_mem σ).mp hc
  have hηξ : η ≠ ξ := by intro he; subst ξ; exact hab rfl
  have hξζ : ξ ≠ ζ := by intro he; subst ζ; exact hbc rfl
  intro hbox
  apply signedBinaryCode_no_between i₀ hfirst hs hηξ hξζ
  intro i
  have h := hbox i
  change min ((signedBinaryCode m σ η i : ℤ) : ℝ) ((signedBinaryCode m σ ζ i : ℤ) : ℝ) ≤
      (signedBinaryCode m σ ξ i : ℤ) ∧ (signedBinaryCode m σ ξ i : ℤ) ≤
        max ((signedBinaryCode m σ η i : ℤ) : ℝ) ((signedBinaryCode m σ ζ i : ℤ) : ℝ) at h
  exact_mod_cast h

/-- Every box contains just its corners, including the coincident-corner case. -/
theorem signedBinarySet_cornerSlice (σ : Fin m → ι → Bool) (i₀ : ι)
    (hfirst : ∀ j, σ j i₀ = true) (hs : Function.Injective σ)
    {a b : ι → ℝ} (ha : a ∈ integerRealSet (signedBinarySet m σ))
    (hb : b ∈ integerRealSet (signedBinarySet m σ)) :
    cornerSlice (integerRealSet (signedBinarySet m σ)) a b = {a, b} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxS, hbox⟩ := mem_cornerSlice.mp hx
    by_cases hxa : x = a
    · simp [hxa]
    by_cases hxb : x = b
    · simp [hxb]
    exact False.elim (signedBinarySet_no_between σ i₀ hfirst hs ha hxS hb (Ne.symm hxa) hxb hbox)
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact mem_cornerSlice.mpr ⟨ha, inCornerBox_left _ _⟩
    · have hx' := Finset.mem_singleton.mp hx
      subst x
      exact mem_cornerSlice.mpr ⟨hb, inCornerBox_right a b⟩

/-- The selector obstruction itself has maximal fans, since every one of
its scalar coordinates is injective. -/
theorem signedBinarySet_maxFan (σ : Fin m → ι → Bool) (i : ι) :
    maxFan (integerRealSet (signedBinarySet m σ)) = 2 ^ m := by
  have hc : (integerRealSet (signedBinarySet m σ)).card = 2 ^ m := by
    rw [integerRealSet_card, signedBinarySet_card σ i]
  have hp : ((integerRealSet (signedBinarySet m σ)).image (fun x ↦ x i)).card = 2 ^ m := by
    simp only [integerRealSet, signedBinarySet, Finset.image_image]
    rw [Finset.card_image_of_injective _ (by
      intro η ξ he
      have hh : (signedBinaryCode m σ η i : ℝ) = (signedBinaryCode m σ ξ i : ℝ) := he
      apply signedBinaryCode_coordinate_injective σ i
      exact_mod_cast hh)]
    simp
  have hlo := coordinate_card_le_maxFan (integerRealSet (signedBinarySet m σ)) i
  rw [hp] at hlo
  exact le_antisymm ((maxFan_le_card _).trans_eq hc) hlo

end
end Erdos539Geometry
