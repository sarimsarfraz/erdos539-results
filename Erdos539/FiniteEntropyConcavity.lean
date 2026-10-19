/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteCouplings

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Finite pushforward is a real linear map, including signed weights. -/
def finitePushLinear {α β : Type*} [Fintype α] (e : α → β) :
    (α → ℝ) →ₗ[ℝ] (β → ℝ) where
  toFun p := finitePush p e
  map_add' p q := by
    funext b
    simp only [finitePush, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  map_smul' c p := by
    funext b
    simp only [finitePush, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring

@[simp] theorem finitePushLinear_apply {α β : Type*} [Fintype α]
    (e : α → β) (p : α → ℝ) : finitePushLinear e p = finitePush p e := rfl

/-- Concavity includes all boundary points of the nonnegative orthant. -/
theorem finiteEntropy_concave {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * finiteEntropy p + b * finiteEntropy q ≤ finiteEntropy (a • p + b • q) := by
  simp only [finiteEntropy, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  exact Real.concaveOn_negMulLog.2 (hp x) (hq x) ha hb hab

/-- Couplings with only the first marginal prescribed. These form the
compact convex domain used before imposing the stationary target marginal. -/
def rowCouplings {α : Type*} [Fintype α] (ν : α → ℝ) : Set (α × α → ℝ) :=
  {p | (∀ z, 0 ≤ p z) ∧ finitePush p Prod.fst = ν}

theorem stationaryCouplings_subset_rowCouplings {α : Type*} [Fintype α] (ν : α → ℝ) :
    stationaryCouplings ν ⊆ rowCouplings ν := fun _ hp ↦ ⟨hp.1, hp.2.1⟩

theorem rowCouplings_isCompact {α : Type*} [Fintype α]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) :
    IsCompact (rowCouplings ν) := by
  have he : rowCouplings ν = Set.Icc (0 : α × α → ℝ) 1 ∩
      {p | finitePush p Prod.fst = ν} := by
    ext p
    constructor
    · rintro ⟨hp, hfirst⟩
      refine ⟨⟨hp, ?_⟩, hfirst⟩
      intro z
      have hle := le_finitePush p Prod.fst hp z
      rw [hfirst] at hle
      have hνle : ν z.1 ≤ 1 := by
        rw [← hs]
        exact Finset.single_le_sum (fun a _ ↦ hν a) (Finset.mem_univ z.1)
      exact hle.trans hνle
    · rintro ⟨⟨hp, _⟩, hfirst⟩
      exact ⟨hp, hfirst⟩
  rw [he]
  exact isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)

theorem rowCouplings_convex {α : Type*} [Fintype α] (ν : α → ℝ) :
    Convex ℝ (rowCouplings ν) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun z ↦ add_nonneg (mul_nonneg ha (hp.1 z)) (mul_nonneg hb (hq.1 z)), ?_⟩
  change finitePushLinear Prod.fst (a • p + b • q) = ν
  rw [map_add, map_smul, map_smul]
  change a • finitePush p Prod.fst + b • finitePush q Prod.fst = ν
  rw [hp.2, hq.2, ← add_smul, hab, one_smul]

theorem couplingOutputEntropy_concaveOn {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (channel : α → α → β) :
    ConcaveOn ℝ (rowCouplings ν) (couplingOutputEntropy ν channel) := by
  refine ⟨rowCouplings_convex ν, ?_⟩
  intro p hp q hq a b ha hb hab
  let e : α × α → α × β := fun z ↦ (z.1, channel z.1 z.2)
  have h := finiteEntropy_concave (finitePush p e) (finitePush q e)
    (finitePush_nonneg p e hp.1) (finitePush_nonneg q e hq.1) ha hb hab
  have he : finitePush (a • p + b • q) e = a • finitePush p e + b • finitePush q e := by
    exact (finitePushLinear e).map_add _ _ |>.trans (by rw [map_smul, map_smul]; rfl)
  dsimp [couplingOutputEntropy]
  change a * (finiteEntropy (finitePush p e) - finiteEntropy ν) +
    b * (finiteEntropy (finitePush q e) - finiteEntropy ν) ≤
    finiteEntropy (finitePush (a • p + b • q) e) - finiteEntropy ν
  rw [he]
  have hconst : a * finiteEntropy ν + b * finiteEntropy ν = finiteEntropy ν := by
    rw [← add_mul, hab, one_mul]
  nlinarith

end
end Erdos539Geometry
