/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryEntropyMaximum
import Erdos539.FiniteMixturePush

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {G H α : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype α]

namespace StationaryAdditiveLaw
variable {S : Finset G} {T : Finset H} {ν : S → ℝ}

def mixtureFour (e : α → S → T) (z : α × ((S × S) × (S × S))) : (T × T) × (T × T) :=
  mapFour (e z.1) z.2

/-- Choose one component label and transport all four endpoints through
that component's affine additive embedding. -/
def mixture (Q : StationaryAdditiveLaw S ν) (ρ : α → ℝ) (hρ : ∀ l, 0 ≤ ρ l)
    (e : α → S → T)
    (hrel : ∀ l (a b c d : S), a.val + b.val = c.val + d.val →
      (e l a).val + (e l b).val = (e l c).val + (e l d).val) :
    StationaryAdditiveLaw T (finitePush (finiteProductWeight ρ ν) (fun z ↦ e z.1 z.2)) :=
  ofFlat (p := finitePush (finiteProductWeight ρ Q.flat) (mixtureFour e)) (by
    refine ⟨finitePush_nonneg _ _ (fun z ↦ mul_nonneg (hρ z.1)
      (Q.nonneg z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2)), ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      apply finitePush_eq_zero_of_fiber_zero
      intro w hw
      have hq : Q.flat w.2 = 0 := by
        apply Q.supported
        intro h
        have hh := hrel w.1 w.2.1.1 w.2.1.2 w.2.2.1 w.2.2.2 h
        have he := congrArg (fun v : (T × T) × (T × T) ↦
          v.1.1.val + v.1.2.val = v.2.1.val + v.2.2.val) hw
        exact hz (he.mp hh)
      simp only [finiteProductWeight, hq, mul_zero]
    · rw [finitePush_comp]
      change finitePush (finiteProductWeight ρ Q.flat) (fun z ↦ e z.1 z.2.1.1) = _
      rw [finitePush_mixture_component ρ Q.flat (fun z ↦ z.1.1) e, Q.flat_first]
    · rw [finitePush_comp]
      change finitePush (finiteProductWeight ρ Q.flat) (fun z ↦ e z.1 z.2.1.2) = _
      rw [finitePush_mixture_component ρ Q.flat (fun z ↦ z.1.2) e, Q.flat_second]
    · rw [finitePush_comp]
      change finitePush (finiteProductWeight ρ Q.flat) (fun z ↦ e z.1 z.2.2.1) = _
      rw [finitePush_mixture_component ρ Q.flat (fun z ↦ z.2.1) e, Q.flat_third]
    · rw [finitePush_comp]
      change finitePush (finiteProductWeight ρ Q.flat) (fun z ↦ e z.1 z.2.2.2) = _
      rw [finitePush_mixture_component ρ Q.flat (fun z ↦ z.2.2) e, Q.flat_fourth])

theorem mixture_entropy (Q : StationaryAdditiveLaw S ν) (ρ : α → ℝ) (hρ : ∀ l, 0 ≤ ρ l)
    (e : α → S → T)
    (hrel : ∀ l (a b c d : S), a.val + b.val = c.val + d.val →
      (e l a).val + (e l b).val = (e l c).val + (e l d).val) :
    (Q.mixture ρ hρ e hrel).entropy =
      finiteEntropy (finitePush (finiteProductWeight ρ Q.flat) (mixtureFour e)) :=
  ofFlat_entropy _

end StationaryAdditiveLaw
end
end Erdos539Geometry
