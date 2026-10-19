/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntervalCountingEnergy
import Erdos539.ReflectedCountingTransport
import Erdos539.GluingLayers

namespace Erdos539Geometry
noncomputable section
open scoped Classical Pointwise

def separatedPair (H : ℤ) : ℤ × ℤ →+ ℤ where
  toFun a := H * a.1 + a.2
  map_zero' := by simp
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add]; ring

theorem separatedPair_injective {H : ℤ} (hH : 0 < H) {a b : ℤ × ℤ}
    (ha : 0 ≤ a.2 ∧ a.2 < H) (hb : 0 ≤ b.2 ∧ b.2 < H)
    (he : separatedPair H a = separatedPair H b) : a = b := by
  have hm := congrArg (fun z : ℤ ↦ z % H) he
  simp only [separatedPair, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Int.add_emod, Int.mul_emod, Int.emod_self, Int.zero_emod, zero_mul, zero_add,
    Int.emod_eq_of_lt ha.1 ha.2, Int.emod_eq_of_lt hb.1 hb.2] at hm
  apply Prod.ext
  · change H * a.1 + a.2 = H * b.1 + b.2 at he
    nlinarith
  · exact hm

def stripDigits (T : ℕ) : Finset ((ℤ × ℤ) × ℤ) :=
  (scalarInterval T ×ˢ scalarInterval T) ×ˢ scalarInterval T

def stripEncode (H : ℤ) : ((ℤ × ℤ) × ℤ) →+ ((Unit ⊕ Unit) → ℤ) where
  toFun a := Sum.elim (fun _ ↦ H * a.1.1 + a.1.2) (fun _ ↦ a.2 - H * a.1.1)
  map_zero' := by funext i; cases i <;> simp
  map_add' a b := by funext i; cases i <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr,
      Prod.fst_add, Prod.snd_add]; all_goals ring

def gibbsStrip (T : ℕ) (H : ℤ) : Finset ((Unit ⊕ Unit) → ℤ) :=
  (stripDigits T).image (stripEncode H)

def stripProjection : ((Unit ⊕ Unit) → ℤ) →+ ℤ where
  toFun x := x (Sum.inl ())
  map_zero' := rfl
  map_add' _ _ := rfl

def stripProjected (T : ℕ) (H : ℤ) : Finset ℤ :=
  (scalarInterval T ×ˢ scalarInterval T).image (separatedPair H)

theorem stripDigits_card (T : ℕ) : (stripDigits T).card = T ^ 3 := by
  simp only [stripDigits, Finset.card_product, scalarInterval_card]
  ring

theorem stripDigits_nonempty {T : ℕ} (hT : 0 < T) : (stripDigits T).Nonempty :=
  ((scalarInterval_nonempty hT).product (scalarInterval_nonempty hT)).product (scalarInterval_nonempty hT)

theorem stripDigits_add_subset (T : ℕ) : stripDigits T + stripDigits T ⊆ stripDigits (2 * T) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
  simp only [stripDigits, Finset.mem_product, scalarInterval, Finset.mem_Ico] at ha hb ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  omega

theorem stripEncode_injOn {T : ℕ} {H : ℤ} (hH : (T : ℤ) < H) :
    Set.InjOn (stripEncode H) (stripDigits T) := by
  intro a ha b hb he
  have ha' := Finset.mem_product.mp ha
  have hb' := Finset.mem_product.mp hb
  have hax := Finset.mem_Ico.mp (Finset.mem_product.mp ha'.1).2
  have hbx := Finset.mem_Ico.mp (Finset.mem_product.mp hb'.1).2
  have hab := separatedPair_injective (lt_of_le_of_lt (Int.natCast_nonneg T) hH)
    ⟨hax.1, hax.2.trans hH⟩ ⟨hbx.1, hbx.2.trans hH⟩ (congrFun he (Sum.inl ()))
  have hy := congrFun he (Sum.inr ())
  change a.2 - H * a.1.1 = b.2 - H * b.1.1 at hy
  exact Prod.ext hab (by rw [hab] at hy; omega)

theorem gibbsStrip_card {T : ℕ} {H : ℤ} (hH : (T : ℤ) < H) :
    (gibbsStrip T H).card = T ^ 3 := by
  rw [gibbsStrip, Finset.card_image_of_injOn (stripEncode_injOn hH), stripDigits_card]

theorem gibbsStrip_nonempty {T : ℕ} (hT : 0 < T) (H : ℤ) : (gibbsStrip T H).Nonempty :=
  (stripDigits_nonempty hT).image _

theorem gibbsStrip_countingEnergy {T : ℕ} {H : ℤ} (hH : 2 * (T : ℤ) < H) :
    countingEnergy (gibbsStrip T H) = countingEnergy (scalarInterval T) ^ 3 := by
  rw [gibbsStrip, countingEnergy_image_of_sum_injective _ _ (stripEncode_injOn (by omega))
    ((stripEncode_injOn (T := 2 * T) (by simpa using hH)).mono (stripDigits_add_subset T))]
  simp only [stripDigits, countingEnergy_product]
  ring

end
end Erdos539Geometry
