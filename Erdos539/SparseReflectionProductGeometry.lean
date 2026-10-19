/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectionRatioTransport
import Erdos539.ThreeDimensionalCalibrationEnergy
import Erdos539.UniformEnergyWeight

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
local instance productRealDecidableEq {ι : Type} : DecidableEq (ι → ℝ) := Classical.decEq _
local instance fixedStripIntegerDecidableEq : DecidableEq ((Unit ⊕ Unit) → ℤ) := inferInstance
local instance sparseProductIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _

abbrev ReflectionProductCoordinates := Unit ⊕ (Unit ⊕ Unit)

def reflectionProductEmbedding : (ℤ × ((Unit ⊕ Unit) → ℤ)) →+ (ReflectionProductCoordinates → ℝ) where
  toFun p := Sum.elim (fun _ ↦ (p.1 : ℝ)) (integerToReal p.2)
  map_zero' := by funext i; cases i <;> simp [integerToReal]
  map_add' p q := by funext i; cases i <;> simp [integerToReal]

theorem reflectionProductEmbedding_injective : Function.Injective reflectionProductEmbedding := by
  intro p q he
  apply Prod.ext
  · have h := congrFun he (Sum.inl ())
    change (p.1 : ℝ) = (q.1 : ℝ) at h
    exact_mod_cast h
  · funext i
    have h := congrFun he (Sum.inr i)
    change (p.2 i : ℝ) = (q.2 i : ℝ) at h
    exact_mod_cast h

def sparseReflectionProduct (S : Finset ℤ) (T : ℕ) : Finset (ReflectionProductCoordinates → ℝ) :=
  (S ×ˢ gibbsStrip T (4 * (T : ℤ))).image reflectionProductEmbedding

theorem sparseReflectionProduct_eq (S : Finset ℤ) (T : ℕ) :
    sparseReflectionProduct S T = coordinateProduct
      (S.image (fun z : ℤ ↦ fun _ : Unit ↦ (z : ℝ))) (integerRealSet (gibbsStrip T (4 * (T : ℤ)))) := by
  ext z
  simp only [sparseReflectionProduct, coordinateProduct, integerRealSet, Finset.mem_image,
    Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨s, b, ⟨hs, hb⟩, rfl⟩
    exact ⟨(fun _ ↦ (s : ℝ)), integerToReal b, ⟨⟨s, hs, rfl⟩, ⟨b, hb, rfl⟩⟩, rfl⟩
  · rintro ⟨a, b, ⟨⟨s, hs, rfl⟩, ⟨v, hv, rfl⟩⟩, rfl⟩
    exact ⟨s, v, ⟨hs, hv⟩, rfl⟩

theorem sparseReflectionProduct_nonempty {S : Finset ℤ} (hS : S.Nonempty) {T : ℕ} (hT : 0 < T) :
    (sparseReflectionProduct S T).Nonempty :=
  (hS.product (gibbsStrip_nonempty hT _)).image _

theorem sparseReflectionProduct_card (S : Finset ℤ) {T : ℕ} (hT : 0 < T) :
    (sparseReflectionProduct S T).card = S.card * T ^ 3 := by
  rw [sparseReflectionProduct, Finset.card_image_of_injective _ reflectionProductEmbedding_injective,
    Finset.card_product, gibbsStrip_card (by omega : (T : ℤ) < 4 * T)]

theorem sparseReflectionProduct_norm (S : Finset ℤ) (T : ℕ) :
    energyNorm (sparseReflectionProduct S T) = energyNorm S * energyNorm (gibbsStrip T (4 * (T : ℤ))) := by
  rw [sparseReflectionProduct, energyNorm_image_of_injective _ _ reflectionProductEmbedding_injective,
    energyNorm_product]

theorem sparseReflectionProduct_fan {S : Finset ℤ} (hS : S.Nonempty) {T : ℕ} (hT : 0 < T) :
    (maxFan (sparseReflectionProduct S T) : ℝ) = (S.card : ℝ) * (2 * (T : ℝ) ^ 2 - T) := by
  rw [sparseReflectionProduct_eq, maxFan_coordinateProduct (hS.image _)
    (show (integerRealSet (gibbsStrip T (4 * (T : ℤ)))).Nonempty from
      (gibbsStrip_nonempty hT _).image _), Nat.cast_mul,
    gibbsStrip_maxFan_real hT (by omega), maxFan_eq_card_one_dimensional (),
    Finset.card_image_of_injective]
  intro a b he
  have h := congrFun he ()
  change (a : ℝ) = (b : ℝ) at h
  exact_mod_cast h

theorem gibbsStrip_energyNorm_lower {T : ℕ} (hT : 0 < T) :
    (8 / 27 : ℝ) * (T : ℝ) ^ 3 ≤ energyNorm (gibbsStrip T (4 * (T : ℤ))) := by
  letI : DecidableEq ℤ := Int.instDecidableEq
  have hb := uniformEnergyWeight_admissible (gibbsStrip_nonempty hT (4 * (T : ℤ)))
  have he := energyNorm_ge_admissible hb
  rw [uniformEnergyWeight_energy, gibbsStrip_countingEnergy (by omega),
    gibbsStrip_card (by omega), Nat.cast_pow] at he
  have hl := countingEnergy_interval_cubic T
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hc := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 / 3 * (T : ℝ) ^ 3) hl 3
  have hh : (8 / 27 : ℝ) * (T : ℝ) ^ 3 ≤ countingEnergy (scalarInterval T) ^ 3 / ((T : ℝ) ^ 3) ^ 2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hc]
  exact hh.trans he

end
end Erdos539Geometry
