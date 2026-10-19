/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryMixtureLaw

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {G H α : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype α]

namespace StationaryAdditiveLaw
variable {S : Finset G} {T : Finset H} {ν : S → ℝ}

omit [AddCommGroup G] [AddCommGroup H] [Fintype α] in
theorem mixtureFour_injective (e : α → S → T)
    (he : Function.Injective (fun z : α × S ↦ e z.1 z.2)) : Function.Injective (mixtureFour e) := by
  intro a b h
  have h₁ : (a.1, a.2.1.1) = (b.1, b.2.1.1) := he (congrArg (fun z ↦ z.1.1) h)
  have h₂ : (a.1, a.2.1.2) = (b.1, b.2.1.2) := he (congrArg (fun z ↦ z.1.2) h)
  have h₃ : (a.1, a.2.2.1) = (b.1, b.2.2.1) := he (congrArg (fun z ↦ z.2.1) h)
  have h₄ : (a.1, a.2.2.2) = (b.1, b.2.2.2) := he (congrArg (fun z ↦ z.2.2) h)
  exact Prod.ext (congrArg (fun z : α × S ↦ z.1) h₁)
    (Prod.ext (Prod.ext (congrArg (fun z : α × S ↦ z.2) h₁) (congrArg (fun z : α × S ↦ z.2) h₂))
      (Prod.ext (congrArg (fun z : α × S ↦ z.2) h₃) (congrArg (fun z : α × S ↦ z.2) h₄)))

/-- Disjoint component embeddings preserve the full label entropy in the
additive quadruple witness. -/
theorem mixture_entropy_eq (Q : StationaryAdditiveLaw S ν) (ρ : α → ℝ)
    (hρ : ∀ l, 0 ≤ ρ l) (hsρ : ∑ l, ρ l = 1) (hsν : ∑ x, ν x = 1)
    (e : α → S → T)
    (hrel : ∀ l (a b c d : S), a.val + b.val = c.val + d.val →
      (e l a).val + (e l b).val = (e l c).val + (e l d).val)
    (he : Function.Injective (fun z : α × S ↦ e z.1 z.2)) :
    (Q.mixture ρ hρ e hrel).entropy = finiteEntropy ρ + Q.entropy := by
  rw [mixture_entropy]
  rw [finiteEntropy_push_eq_of_support_injective _ _
    (fun a b _ _ h ↦ mixtureFour_injective e he h)]
  have hq : ∑ z, Q.flat z = 1 := by
    simpa only [flat, Fintype.sum_prod_type] using Q.total_mass hsν
  rw [finiteProductWeight_entropy _ _ hsρ hq]
  simp only [finiteEntropy, flat, entropy, Fintype.sum_prod_type]

end StationaryAdditiveLaw

/-- A uniform component mixture pays two label entropies in stationary
defect. This is an actual additive-law witness, not a counting-energy proxy. -/
theorem stationaryEntropyDefect_mixture_le {S : Finset G} {T : Finset H}
    (ρ : α → ℝ) (ν : S → ℝ) (hρ : ∀ l, 0 ≤ ρ l) (hsρ : ∑ l, ρ l = 1)
    (hν : ∀ x, 0 ≤ ν x) (hsν : ∑ x, ν x = 1) (e : α → S → T)
    (hrel : ∀ l (a b c d : S), a.val + b.val = c.val + d.val →
      (e l a).val + (e l b).val = (e l c).val + (e l d).val)
    (he : Function.Injective (fun z : α × S ↦ e z.1 z.2)) :
    stationaryEntropyDefect T (finitePush (finiteProductWeight ρ ν) (fun z ↦ e z.1 z.2)) ≤
      2 * finiteEntropy ρ + stationaryEntropyDefect S ν := by
  obtain ⟨Q, hQ⟩ := stationaryAdditiveEntropy_attained S ν hν hsν
  have hm : ∀ y, 0 ≤ finitePush (finiteProductWeight ρ ν) (fun z ↦ e z.1 z.2) y :=
    finitePush_nonneg _ _ (finiteProductWeight_nonneg _ _ hρ hν)
  have hs : ∑ y, finitePush (finiteProductWeight ρ ν) (fun z ↦ e z.1 z.2) y = 1 := by
    rw [finitePush_sum, finiteProductWeight_sum, hsρ, hsν, one_mul]
  have ha := (Q.mixture ρ hρ e hrel).entropy_le_stationaryAdditiveEntropy hm hs
  rw [Q.mixture_entropy_eq ρ hρ hsρ hsν e hrel he, hQ] at ha
  have hE : finiteEntropy (finitePush (finiteProductWeight ρ ν) (fun z ↦ e z.1 z.2)) =
      finiteEntropy ρ + finiteEntropy ν := by
    rw [finiteEntropy_push_eq_of_support_injective _ _ (fun a b _ _ h ↦ he h),
      finiteProductWeight_entropy _ _ hsρ hsν]
  unfold stationaryEntropyDefect
  rw [hE]
  linarith

end
end Erdos539Geometry
