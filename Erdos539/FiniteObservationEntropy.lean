/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteBlockEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {α β κ : Type*} [Fintype α] [Fintype β]

def maskObservation (O : κ → α → β) (I : Finset κ) (a : α) : I → β := fun i ↦ O i.val a

def observationEntropy (p : α → ℝ) (O : κ → α → β) (I : Finset κ) : ℝ :=
  finiteEntropy (finitePush p (maskObservation O I))

omit [Fintype α] [Fintype β] in
theorem maskObservation_eq_iff (O : κ → α → β) (I : Finset κ) (a b : α) :
    maskObservation O I a = maskObservation O I b ↔ ∀ i ∈ I, O i a = O i b := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.val i.property

theorem observationEntropy_mono (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (O : κ → α → β)
    {I J : Finset κ} (hIJ : I ⊆ J) : observationEntropy p O I ≤ observationEntropy p O J := by
  have h := finiteEntropy_push_le (finitePush p (maskObservation O J))
    (fun x : J → β ↦ fun i : I ↦ x ⟨i.val, hIJ i.property⟩) (finitePush_nonneg p _ hp)
  rw [finitePush_comp] at h
  exact h

theorem observationEntropy_empty (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    (O : κ → α → β) : observationEntropy p O ∅ = 0 := by
  have he := finiteEntropy_push_eq_of_fibers p hp (maskObservation O ∅) (fun _ : α ↦ Unit.unit) (by
    intro a b
    rw [maskObservation_eq_iff]
    simp)
  change finiteEntropy (finitePush p (maskObservation O ∅)) = 0
  rw [he]
  have hv : finitePush p (fun _ : α ↦ Unit.unit) = fun _ : Unit ↦ (1 : ℝ) := by
    funext x
    cases x
    simpa only [finitePush, if_true] using hs
  rw [hv]
  simp [finiteEntropy]

theorem observationEntropy_pair (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (O : κ → α → β)
    (i : κ) (J : Finset κ) :
    finiteEntropy (finitePush p (fun a ↦ (O i a, maskObservation O J a))) = observationEntropy p O (insert i J) := by
  apply finiteEntropy_push_eq_of_fibers p hp
  intro a b
  rw [maskObservation_eq_iff, Prod.mk.injEq, maskObservation_eq_iff]
  simp only [Finset.mem_insert, forall_eq_or_imp]

theorem observationEntropy_increment_antitone (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (O : κ → α → β)
    {I J : Finset κ} (hIJ : I ⊆ J) (i : κ) :
    observationEntropy p O (insert i J) - observationEntropy p O J ≤
      observationEntropy p O (insert i I) - observationEntropy p O I := by
  let X := O i
  let F := maskObservation O J
  let G := maskObservation O I
  let q := finitePush p (fun a ↦ (X a, F a))
  let h : (J → β) → (I → β) := fun x j ↦ x ⟨j.val, hIJ j.property⟩
  have hF : finitePush q Prod.snd = finitePush p F := by rw [finitePush_comp]; rfl
  have hG : finitePush (finitePush p F) h = finitePush p G := by rw [finitePush_comp]; rfl
  have hpair : finitePush q (mapSecond h) = finitePush p (fun a ↦ (X a, G a)) := by
    rw [finitePush_comp]; rfl
  have hc := finite_conditionalEntropy_map_condition q (finitePush_nonneg p _ hp) h
  rw [hF, hG, hpair] at hc
  have hJ := observationEntropy_pair p hp O i J
  have hI := observationEntropy_pair p hp O i I
  change finiteEntropy q = _ at hJ
  change finiteEntropy (finitePush p (fun a ↦ (X a, G a))) = _ at hI
  rw [hJ, hI] at hc
  exact hc

theorem observation_maskCMI_nonneg (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (O : κ → α → β)
    (A B C : Finset κ) : 0 ≤ maskCMI (observationEntropy p O) A B C :=
  maskCMI_nonneg _ (fun _ _ h ↦ observationEntropy_mono p hp O h)
    (fun {_ _} h i ↦ observationEntropy_increment_antitone p hp O h i) A B C

end
end Erdos539Geometry
