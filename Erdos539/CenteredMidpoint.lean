/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CenteredChildren
import Erdos539.CenteredEstimates
import Erdos539.SharpExponents

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
universe u v

/-- Positive parts are nonempty whenever the actual group set is nonempty. -/
theorem embeddedPositiveParts_nonempty {ι M : Type*} [AddCommGroup M]
    (e : M →ₗ[ℤ] (ι → ℝ)) {F : Finset M} (hF : F.Nonempty) :
    (embeddedPositiveParts e F).Nonempty := (hF.image e).image _

/-- Sharp centered midpoint theorem, retaining the actual free-group rank.
This is the manuscript's constant 2^(-d-2r), in logarithmic form. -/
theorem centered_midpoint_log_bound (d : ℕ) :
    ∀ (ι : Type u) [Fintype ι], Fintype.card ι = d → 0 < d →
      ∀ (M : Type v) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
        (e : M →ₗ[ℤ] (ι → ℝ)), Function.Injective e →
        ∀ (F : Finset M), 0 ∈ F → GroupSymmetric F → GroupMidpointClosed F →
          (sharpExponent d : ℝ) * Real.log F.card -
            ((d : ℝ) + 2 * Module.finrank ℤ M) * Real.log 2 ≤
              Real.log (embeddedPositiveParts e F).card := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro ι inst hdim hd M instM instFree instFinite e he F hzero hsym hF
    have hFn : F.Nonempty := ⟨0, hzero⟩
    have hn : (0 : ℝ) < F.card := by exact_mod_cast hFn.card_pos
    have hnlog : 0 ≤ Real.log F.card := Real.log_nonneg (by exact_mod_cast hFn.card_pos)
    have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    let q := (embeddedPositiveParts e F).card
    have hq : (0 : ℝ) < q := by
      exact_mod_cast (embeddedPositiveParts_nonempty e hFn).card_pos
    obtain ⟨I, J, hIJ, hcover, hcard, E, hEF, hE, hlarge, hP, hQ⟩ :=
      exists_centered_sign_partition hFn hsym e
    rw [hdim] at hcard hlarge
    have hempty (T : Finset ι) (hfull : ∀ i, i ∈ T)
        (hT : (E.image (fun x ↦ project T (e x))).card ≤ q) :
        (sharpExponent d : ℝ) * Real.log F.card -
          ((d : ℝ) + 2 * Module.finrank ℤ M) * Real.log 2 ≤ Real.log q := by
      rw [full_embedded_projection_card e he T hfull E] at hT
      have hc := hlarge.trans (Nat.mul_le_mul_left _ hT)
      have hl := Real.log_le_log hn (show (F.card : ℝ) ≤ (2 : ℝ) ^ d * q by exact_mod_cast hc)
      rw [Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne' hq.ne', Real.log_pow] at hl
      exact centered_empty_log_closes (by exact_mod_cast (sharpExponent_bounds d).2)
        hnlog (Nat.cast_nonneg _) hL hl
    by_cases hpzero : I.card = 0
    · apply hempty J _ hQ
      intro i
      exact (hcover i).resolve_left (by rw [Finset.card_eq_zero.mp hpzero]; simp)
    by_cases hszero : J.card = 0
    · apply hempty I _ hP
      intro i
      exact (hcover i).resolve_right (by rw [Finset.card_eq_zero.mp hszero]; simp)
    have hp : 0 < I.card := Nat.pos_of_ne_zero hpzero
    have hs : 0 < J.card := Nat.pos_of_ne_zero hszero
    have hpLt : I.card < d := by omega
    have hsLt : J.card < d := by omega
    have child_bound (T : Finset ι) (hT : 0 < T.card) (hTd : T.card < d) :
        (sharpExponent T.card : ℝ) * Real.log (midpointDescendant F e he T).card -
          ((T.card : ℝ) + 2 * Module.finrank ℤ (latticeSupported e T)) * Real.log 2 ≤
            Real.log (embeddedPositiveParts (supportedChildEmbedding e T) (midpointDescendant F e he T)).card := by
      exact ih T.card hTd T (by simp only [Fintype.card_coe]) hT
        (latticeSupported e T) (supportedChildEmbedding e T) (supportedChildEmbedding_injective e he T)
        (midpointDescendant F e he T) (zero_mem_midpointDescendant hzero e he T)
        (hsym.descendant e he T) (hF.descendant e he T)
    have hAI := child_bound I hp hpLt
    have hBJ := child_bound J hs hsLt
    have child_card_log (T U : Finset ι) (hTU : ∀ i, i ∈ T ∨ i ∈ U)
        (hU : (E.image (fun x ↦ project U (e x))).card ≤ q) :
        Real.log F.card ≤ (d : ℝ) * Real.log 2 + Real.log q +
          2 * Module.finrank ℤ (latticeSupported e T) * Real.log 2 +
            Real.log (midpointDescendant F e he T).card := by
      have hc := centered_child_from_sign_class hF hsym hEF hE e he T U hTU hU (hdim ▸ hlarge)
      rw [hdim] at hc
      have hchild : (0 : ℝ) < (midpointDescendant F e he T).card := by
        exact_mod_cast (Finset.card_pos.mpr ⟨0, zero_mem_midpointDescendant hzero e he T⟩)
      have hl := Real.log_le_log hn (show (F.card : ℝ) ≤ (2 : ℝ) ^ d * q *
        (4 : ℝ) ^ Module.finrank ℤ (latticeSupported e T) * (midpointDescendant F e he T).card by exact_mod_cast hc)
      rw [Real.log_mul (by positivity) hchild.ne', Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) hq.ne', Real.log_pow, Real.log_pow] at hl
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        have hh := Real.log_pow (2 : ℝ) 2
        norm_num at hh
        exact hh
      rw [h4] at hl
      linarith
    have hA := child_card_log I J hcover hQ
    have hB := child_card_log J I (fun i ↦ (hcover i).symm) hP
    have hprod :
        Real.log (embeddedPositiveParts (supportedChildEmbedding e I) (midpointDescendant F e he I)).card +
        Real.log (embeddedPositiveParts (supportedChildEmbedding e J) (midpointDescendant F e he J)).card ≤
          Real.log q := by
      have hqi : (0 : ℝ) < (embeddedPositiveParts (supportedChildEmbedding e I) (midpointDescendant F e he I)).card := by
        exact_mod_cast (embeddedPositiveParts_nonempty _ ⟨0, zero_mem_midpointDescendant hzero e he I⟩).card_pos
      have hqj : (0 : ℝ) < (embeddedPositiveParts (supportedChildEmbedding e J) (midpointDescendant F e he J)).card := by
        exact_mod_cast (embeddedPositiveParts_nonempty _ ⟨0, zero_mem_midpointDescendant hzero e he J⟩).card_pos
      have hEq (T : Finset ι) :
          embeddedPositiveParts (supportedChildEmbedding e T) (midpointDescendant F e he T) =
          fan ((midpointDescendant F e he T).image (supportedChildEmbedding e T)) 0 := by
        ext z
        simp only [embeddedPositiveParts, mem_fan, Finset.mem_image]
      have hc := midpointDescendant_positive_product_le hF e he I J hIJ hcover
      have hl := Real.log_le_log (mul_pos hqi hqj) (show
        ((embeddedPositiveParts (supportedChildEmbedding e I) (midpointDescendant F e he I)).card : ℝ) *
        (embeddedPositiveParts (supportedChildEmbedding e J) (midpointDescendant F e he J)).card ≤ q by
          rw [hEq I, hEq J]
          dsimp only [q, embeddedPositiveParts]
          exact_mod_cast hc)
      rwa [Real.log_mul hqi.ne' hqj.ne'] at hl
    have hsplit : (sharpExponent d : ℝ) ≤
        ((sharpExponent I.card : ℝ) + sharpExponent J.card) /
          (1 + (sharpExponent I.card : ℝ) + sharpExponent J.card) := by
      have h : (sharpExponent (I.card + J.card) : ℝ) ≤
          (combineExponent (sharpExponent I.card) (sharpExponent J.card) : ℝ) := by
        exact_mod_cast sharpExponent_le_split hp hs
      rw [hcard, combineExponent] at h
      push_cast at h
      exact h
    exact centered_log_closes
      (by exact_mod_cast (sharpExponent_pos I.card).le)
      (by exact_mod_cast (sharpExponent_pos J.card).le) hnlog hL
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast latticeSupported_finrank_add_le e I J he hIJ)
      (by exact_mod_cast hcard) hsplit hA hB hAI hBJ hprod

end
end Erdos539Geometry
