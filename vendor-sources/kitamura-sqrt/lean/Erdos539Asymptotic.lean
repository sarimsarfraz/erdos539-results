import Erdos539Factorization
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat

/-! Cardinal bounds at bounded doubling imply the negative square-root targets. -/
namespace Erdos539Asymptotic

noncomputable section
open Filter
open scoped Asymptotics Topology
open Erdos539Geometry

/-- The finitary conclusion needed for the asymptotic argument. -/
def PositiveBoundedDoubling : Prop :=
  ∀ K : ℝ, 0 < K → ∃ N : ℕ, ∀ A : Finset ℕ,
    (∀ a ∈ A, 0 < a) →
    ((cofactors A).card : ℝ) ^ 2 ≤ K * A.card → A.card ≤ N

/-- This is definitionally the zero-inclusive Formal Conjectures threshold. -/
def threshold (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ (cofactors A).card}

private theorem bounds_bddAbove (n : ℕ) :
    BddAbove {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ (cofactors A).card} := by
  refine ⟨n * n, ?_⟩
  intro m hm
  calc
    m ≤ (cofactors (Finset.range n)).card := hm _ (Finset.card_range n)
    _ ≤ (Finset.range n ×ˢ Finset.range n).card := Finset.card_image_le
    _ = n * n := by simp

theorem threshold_attained (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ (cofactors A).card = threshold n := by
  classical
  have hne : ({m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ (cofactors A).card} :
      Set ℕ).Nonempty := ⟨0,fun _ _ ↦ Nat.zero_le _⟩
  have hlower : ∀ A : Finset ℕ, A.card = n → threshold n ≤ (cofactors A).card :=
    Nat.sSup_mem hne (bounds_bddAbove n)
  have hex : ∃ m : ℕ, ∃ A : Finset ℕ, A.card = n ∧ (cofactors A).card = m :=
    ⟨_,Finset.range n,Finset.card_range n,rfl⟩
  obtain ⟨A,hA,hq⟩ := Nat.find_spec hex
  have hmin : ∀ B : Finset ℕ, B.card = n → Nat.find hex ≤ (cofactors B).card := by
    intro B hB
    exact Nat.find_min' hex ⟨B,hB,rfl⟩
  have hlo : Nat.find hex ≤ threshold n := le_csSup (bounds_bddAbove n) hmin
  have hhi := hlower A hA
  exact ⟨A,hA,by omega⟩

theorem cofactors_mono {A B : Finset ℕ} (h : A ⊆ B) :
    cofactors A ⊆ cofactors B := by
  classical
  exact Finset.image_subset_image (Finset.product_subset_product h h)

theorem positive_subset_pred {A : Finset ℕ} (hA : A.Nonempty) :
    ∃ B : Finset ℕ, B ⊆ A ∧ B.card = A.card - 1 ∧ ∀ b ∈ B, 0 < b := by
  classical
  by_cases hz : 0 ∈ A
  · refine ⟨A.erase 0,Finset.erase_subset _ _,Finset.card_erase_of_mem hz,?_⟩
    intro b hb
    exact Nat.pos_of_ne_zero (Finset.mem_erase.mp hb).1
  · obtain ⟨a,ha⟩ := hA
    refine ⟨A.erase a,Finset.erase_subset _ _,Finset.card_erase_of_mem ha,?_⟩
    intro b hb
    exact Nat.pos_of_ne_zero fun hb0 ↦ hz (hb0 ▸ (Finset.mem_erase.mp hb).2)

theorem eventually_mul_sqrt_lt (bounded : PositiveBoundedDoubling) (M : ℝ)
    (_hM : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop, M * Real.sqrt (n : ℝ) < (threshold n : ℝ) := by
  obtain ⟨N,hN⟩ := bounded (2 * M ^ 2 + 1) (by positivity)
  filter_upwards [eventually_ge_atTop (N + 2)] with n hn
  obtain ⟨A,hA,hq⟩ := threshold_attained n
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨B,hBA,hB,hpos⟩ := positive_subset_pred hAne
  have hn2 : 2 ≤ n := by omega
  have hcard : B.card = n - 1 := by omega
  have hpred : (n : ℝ) ≤ 2 * (B.card : ℝ) := by
    exact_mod_cast (show n ≤ 2 * B.card by omega)
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast (show 0 < B.card by omega)
  by_contra hnot
  have hsmall : (threshold n : ℝ) ≤ M * Real.sqrt (n : ℝ) := le_of_not_gt hnot
  have hcof : ((cofactors B).card : ℝ) ≤ (threshold n : ℝ) := by
    exact_mod_cast (show (cofactors B).card ≤ threshold n from
      hq ▸ Finset.card_le_card (cofactors_mono hBA))
  have hsq : ((cofactors B).card : ℝ) ^ 2 ≤ M ^ 2 * (n : ℝ) := by
    calc
      ((cofactors B).card : ℝ) ^ 2 ≤ (M * Real.sqrt (n : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (hcof.trans hsmall) 2
      _ = M ^ 2 * (n : ℝ) := by rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hbnd : ((cofactors B).card : ℝ) ^ 2 ≤ (2 * M ^ 2 + 1) * B.card := by
    have hh := mul_le_mul_of_nonneg_left hpred (sq_nonneg M)
    nlinarith
  have hBN := hN B hpos hbnd
  omega

theorem threshold_div_sqrt_tendsto (bounded : PositiveBoundedDoubling) :
    Tendsto (fun n : ℕ ↦ (threshold n : ℝ) / Real.sqrt (n : ℝ)) atTop atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  filter_upwards [eventually_mul_sqrt_lt bounded (max b 0) (le_max_right _ _),
    eventually_ge_atTop 1] with n hn hn1
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  exact (le_max_left b 0).trans ((lt_div_iff₀ hs).2 hn).le

theorem not_isBigO_of_positive_bounded (bounded : PositiveBoundedDoubling) :
    ¬ ((fun n : ℕ ↦ (threshold n : ℝ)) =O[atTop] fun n ↦ Real.sqrt (n : ℝ)) := by
  intro h
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp h
  have hlarge := eventually_mul_sqrt_lt bounded (max C 0) (le_max_right _ _)
  have hbad : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hC,hlarge] with n hn hlt
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg (threshold n) : (0 : ℝ) ≤ (threshold n : ℝ)),
      abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))] at hn
    have hCmax := mul_le_mul_of_nonneg_right (le_max_left C 0)
      (Real.sqrt_nonneg (n : ℝ))
    exact (not_lt_of_ge (hn.trans hCmax)) hlt
  obtain ⟨n,hn⟩ := hbad.exists
  exact hn

theorem not_isTheta_of_positive_bounded (bounded : PositiveBoundedDoubling) :
    ¬ ((fun n : ℕ ↦ (threshold n : ℝ)) =Θ[atTop] fun n ↦ Real.sqrt (n : ℝ)) := by
  intro h
  exact not_isBigO_of_positive_bounded bounded h.isBigO

/-- A growth exponent above one half bounds cardinality at bounded doubling. -/
theorem cardinal_bound_of_growth {n q c η K a : ℝ}
    (hn : 0 < n) (_hq : 0 ≤ q) (hc : 0 < c) (hη : 0 < η) (hK : 0 < K)
    (ha : 1 / 2 < a)
    (hgrowth : c * (η * n) ^ a ≤ q) (hdoubling : q ^ 2 ≤ K * n) :
    n ≤ (K / (c ^ 2 * η ^ (2 * a))) ^ ((2 * a - 1)⁻¹) := by
  have hs : 0 < 2 * a - 1 := by linarith
  have hC : 0 < c ^ 2 * η ^ (2 * a) := by positivity
  have hp : (c * (η * n) ^ a) ^ 2 ≤ q ^ 2 :=
    pow_le_pow_left₀ (by positivity) hgrowth 2
  have hpow : ((η * n) ^ a) ^ 2 = η ^ (2 * a) * n ^ (2 * a) := by
    rw [← Real.rpow_natCast ((η * n) ^ a) 2, ← Real.rpow_mul (by positivity)]
    norm_num
    rw [mul_comm a (2 : ℝ),Real.mul_rpow hη.le hn.le]
  rw [mul_pow,hpow] at hp
  have hnfac : n ^ (2 * a) = n ^ (2 * a - 1) * n := by
    calc
      n ^ (2 * a) = n ^ ((2 * a - 1) + 1) := by congr 1; ring
      _ = n ^ (2 * a - 1) * n := by rw [Real.rpow_add hn,Real.rpow_one]
  rw [hnfac] at hp
  have hcn : (c ^ 2 * η ^ (2 * a) * n ^ (2 * a - 1)) * n ≤ K * n := by
    nlinarith [hp.trans hdoubling]
  have hcp : c ^ 2 * η ^ (2 * a) * n ^ (2 * a - 1) ≤ K :=
    (mul_le_mul_iff_left₀ hn).mp hcn
  have hbound : n ^ (2 * a - 1) ≤ K / (c ^ 2 * η ^ (2 * a)) :=
    (le_div_iff₀ hC).mpr (by nlinarith [hcp])
  exact (Real.le_rpow_inv_iff_of_pos hn.le (by positivity) hs).mpr hbound

/-- Natural-number form, with a bound depending only on the constants. -/
theorem exists_cardinal_bound_of_growth {c η K a : ℝ}
    (hc : 0 < c) (hη : 0 < η) (hK : 0 < K) (ha : 1 / 2 < a) :
    ∃ N : ℕ, ∀ n : ℕ, ∀ q : ℝ, 0 ≤ q →
      c * (η * n) ^ a ≤ q → q ^ 2 ≤ K * n → n ≤ N := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((K / (c ^ 2 * η ^ (2 * a))) ^ ((2 * a - 1)⁻¹))
  refine ⟨N,?_⟩
  intro n q hq hgrowth hdoubling
  by_cases hn : n = 0
  · omega
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hb := cardinal_bound_of_growth hnpos hq hc hη hK ha hgrowth hdoubling
    exact_mod_cast (hb.trans hN.le)

end
end Erdos539Asymptotic

#print axioms Erdos539Asymptotic.threshold_attained
#print axioms Erdos539Asymptotic.threshold_div_sqrt_tendsto
#print axioms Erdos539Asymptotic.not_isBigO_of_positive_bounded

#print axioms Erdos539Asymptotic.exists_cardinal_bound_of_growth
