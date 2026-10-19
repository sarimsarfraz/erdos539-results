/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StripEncoding
import Erdos539.ProductEnergy

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators Pointwise

abbrev CalibrationThreeCoordinates := (Unit ⊕ Unit) ⊕ Unit
abbrev CalibrationThreeDigits := (ℤ × ((ℤ × ℤ) × ℤ)) × ℤ
local instance calibrationThreeIntegerDecidableEq : DecidableEq (CalibrationThreeCoordinates → ℤ) := Classical.decEq _

def calibrationThreeDigits (T : ℕ) : Finset CalibrationThreeDigits :=
  (scalarInterval (T ^ 2) ×ˢ stripDigits T) ×ˢ scalarInterval (T ^ 3)

/-- Literal source coordinates (M0*t+M1*r+a, M0*t-M1*r+b, -M0*t+c). -/
def calibrationThreeEncode (M0 M1 : ℤ) : CalibrationThreeDigits →+ (CalibrationThreeCoordinates → ℤ) where
  toFun a := Sum.elim (fun i ↦ stripEncode M1 a.1.2 i + M0 * a.1.1) (fun _ ↦ a.2 - M0 * a.1.1)
  map_zero' := by funext i; cases i <;> simp
  map_add' a b := by
    funext i
    cases i <;> simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Sum.elim_inl, Sum.elim_inr, map_add]
    all_goals ring

def calibrationThree (T : ℕ) : Finset (CalibrationThreeCoordinates → ℤ) :=
  (calibrationThreeDigits T).image (calibrationThreeEncode (10 * (T : ℤ) ^ 3) (4 * T))

theorem calibrationThreeDigits_card (T : ℕ) : (calibrationThreeDigits T).card = T ^ 8 := by
  simp only [calibrationThreeDigits, Finset.card_product, scalarInterval_card, stripDigits_card]
  ring

theorem calibrationThreeEncode_injOn {T : ℕ} {M0 M1 : ℤ}
    (h0 : (T : ℤ) ^ 3 < M0) (h1 : (T : ℤ) < M1) :
    Set.InjOn (calibrationThreeEncode M0 M1) (calibrationThreeDigits T) := by
  intro a ha b hb he
  obtain ⟨⟨hat, has⟩, hac⟩ := Finset.mem_product.mp ha |>.imp_left Finset.mem_product.mp
  obtain ⟨⟨hbt, hbs⟩, hbc⟩ := Finset.mem_product.mp hb |>.imp_left Finset.mem_product.mp
  have hac' := Finset.mem_Ico.mp hac
  have hbc' := Finset.mem_Ico.mp hbc
  have h0p : 0 < M0 := lt_of_le_of_lt (pow_nonneg (Int.natCast_nonneg T) _) h0
  have hlast := congrFun he (Sum.inr ())
  have hp : separatedPair M0 (-a.1.1, a.2) = separatedPair M0 (-b.1.1, b.2) := by
    change a.2 - M0 * a.1.1 = b.2 - M0 * b.1.1 at hlast
    dsimp [separatedPair]
    linarith
  have hpair := separatedPair_injective h0p
    (show 0 ≤ a.2 ∧ a.2 < M0 from ⟨hac'.1, hac'.2.trans (by exact_mod_cast h0)⟩)
    (show 0 ≤ b.2 ∧ b.2 < M0 from ⟨hbc'.1, hbc'.2.trans (by exact_mod_cast h0)⟩) hp
  have ht : a.1.1 = b.1.1 := by
    have hh := congrArg Prod.fst hpair
    change -a.1.1 = -b.1.1 at hh
    exact neg_injective hh
  have hs : stripEncode M1 a.1.2 = stripEncode M1 b.1.2 := by
    funext i
    have hh := congrFun he (Sum.inl i)
    change stripEncode M1 a.1.2 i + M0 * a.1.1 = stripEncode M1 b.1.2 i + M0 * b.1.1 at hh
    rw [ht] at hh
    exact add_right_cancel hh
  have hc : a.2 = b.2 := congrArg (fun p : ℤ × ℤ ↦ p.2) hpair
  exact Prod.ext (Prod.ext ht (stripEncode_injOn h1 has hbs hs)) hc

theorem calibrationThreeDigits_add_subset (T : ℕ) :
    calibrationThreeDigits T + calibrationThreeDigits T ⊆ calibrationThreeDigits (2 * T) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨⟨hat, has⟩, hac⟩ := Finset.mem_product.mp ha |>.imp_left Finset.mem_product.mp
  obtain ⟨⟨hbt, hbs⟩, hbc⟩ := Finset.mem_product.mp hb |>.imp_left Finset.mem_product.mp
  refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · have ha' := Finset.mem_Ico.mp hat
    have hb' := Finset.mem_Ico.mp hbt
    apply Finset.mem_Ico.mpr
    change 0 ≤ a.1.1 + b.1.1 ∧ a.1.1 + b.1.1 < ((2 * T) ^ 2 : ℕ)
    push_cast at ha' hb' ⊢
    constructor <;> nlinarith [sq_nonneg (T : ℤ)]
  · exact stripDigits_add_subset T (Finset.mem_add.mpr ⟨a.1.2, has, b.1.2, hbs, rfl⟩)
  · have ha' := Finset.mem_Ico.mp hac
    have hb' := Finset.mem_Ico.mp hbc
    apply Finset.mem_Ico.mpr
    change 0 ≤ a.2 + b.2 ∧ a.2 + b.2 < ((2 * T) ^ 3 : ℕ)
    push_cast at ha' hb' ⊢
    constructor <;> nlinarith [pow_nonneg (Int.natCast_nonneg T) 3]

theorem calibrationThree_card {T : ℕ} (hT : 0 < T) : (calibrationThree T).card = T ^ 8 := by
  have ht : (0 : ℤ) < T := by exact_mod_cast hT
  rw [calibrationThree, Finset.card_image_of_injOn, calibrationThreeDigits_card]
  exact calibrationThreeEncode_injOn (by nlinarith [pow_pos ht 3]) (by omega)

/-- Exact counting energy of the literal five-parameter construction. -/
theorem calibrationThree_countingEnergy {T : ℕ} (hT : 0 < T) :
    countingEnergy (calibrationThree T) = countingEnergy (scalarInterval (T ^ 2)) *
      countingEnergy (scalarInterval T) ^ 3 * countingEnergy (scalarInterval (T ^ 3)) := by
  have ht : (0 : ℤ) < T := by exact_mod_cast hT
  have h1 : Set.InjOn (calibrationThreeEncode (10 * (T : ℤ) ^ 3) (4 * T)) (calibrationThreeDigits T) :=
    calibrationThreeEncode_injOn (by nlinarith [pow_pos ht 3]) (by omega)
  have h2 : Set.InjOn (calibrationThreeEncode (10 * (T : ℤ) ^ 3) (4 * T)) (calibrationThreeDigits (2 * T)) := by
    apply calibrationThreeEncode_injOn
    · push_cast
      nlinarith [pow_pos ht 3]
    · push_cast
      omega
  rw [calibrationThree, countingEnergy_image_of_sum_injective _ _ h1 (h2.mono (calibrationThreeDigits_add_subset T))]
  simp only [calibrationThreeDigits, stripDigits, countingEnergy_product]
  ring

end
end Erdos539Geometry
