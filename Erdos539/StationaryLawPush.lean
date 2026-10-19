/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryEntropyEnergy
import Erdos539.FinitePushProducts

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

def flat (Q : StationaryAdditiveLaw S ν) : (S × S) × (S × S) → ℝ :=
  fun z ↦ Q.mass z.1.1 z.1.2 z.2.1 z.2.2

theorem flat_first (Q : StationaryAdditiveLaw S ν) :
    finitePush Q.flat (fun z ↦ z.1.1) = ν := by
  funext a
  rw [finitePush_first4]
  exact Q.first a

theorem flat_second (Q : StationaryAdditiveLaw S ν) :
    finitePush Q.flat (fun z ↦ z.1.2) = ν := by
  funext b
  rw [finitePush_second4]
  exact Q.second b

theorem flat_third (Q : StationaryAdditiveLaw S ν) :
    finitePush Q.flat (fun z ↦ z.2.1) = ν := by
  funext c
  rw [finitePush_third4]
  exact Q.third c

theorem flat_fourth (Q : StationaryAdditiveLaw S ν) :
    finitePush Q.flat (fun z ↦ z.2.2) = ν := by
  funext d
  rw [finitePush_fourth4]
  exact Q.fourth d

def mapFour {α β : Type*} (e : α → β) : (α × α) × (α × α) → (β × β) × (β × β) :=
  fun z ↦ ((e z.1.1, e z.1.2), (e z.2.1, e z.2.2))

/-- Push all four endpoints through the same map preserving additive
relations. The endpoint law is the actual pushforward of the original law. -/
def map (Q : StationaryAdditiveLaw S ν) {T : Finset H} (e : S → T)
    (hrel : ∀ a b c d : S, a.val + b.val = c.val + d.val →
      (e a).val + (e b).val = (e c).val + (e d).val) :
    StationaryAdditiveLaw T (finitePush ν e) where
  mass a b c d := finitePush Q.flat (mapFour e) ((a, b), (c, d))
  nonneg a b c d := finitePush_nonneg Q.flat (mapFour e)
    (fun z ↦ Q.nonneg z.1.1 z.1.2 z.2.1 z.2.2) _
  supported := by
    intro a b c d habcd
    apply finitePush_eq_zero_of_fiber_zero
    intro z hz
    apply Q.supported
    intro h
    have he := hrel z.1.1 z.1.2 z.2.1 z.2.2 h
    have ha := congrArg (fun z ↦ z.1.1) hz
    have hb := congrArg (fun z ↦ z.1.2) hz
    have hc := congrArg (fun z ↦ z.2.1) hz
    have hd := congrArg (fun z ↦ z.2.2) hz
    change e z.1.1 = a at ha
    change e z.1.2 = b at hb
    change e z.2.1 = c at hc
    change e z.2.2 = d at hd
    rw [ha, hb, hc, hd] at he
    exact habcd he
  first := by
    intro a
    rw [← finitePush_first4, finitePush_comp]
    change finitePush Q.flat (e ∘ (fun z ↦ z.1.1)) a = _
    rw [← finitePush_comp, Q.flat_first]
  second := by
    intro b
    rw [← finitePush_second4, finitePush_comp]
    change finitePush Q.flat (e ∘ (fun z ↦ z.1.2)) b = _
    rw [← finitePush_comp, Q.flat_second]
  third := by
    intro c
    rw [← finitePush_third4, finitePush_comp]
    change finitePush Q.flat (e ∘ (fun z ↦ z.2.1)) c = _
    rw [← finitePush_comp, Q.flat_third]
  fourth := by
    intro d
    rw [← finitePush_fourth4, finitePush_comp]
    change finitePush Q.flat (e ∘ (fun z ↦ z.2.2)) d = _
    rw [← finitePush_comp, Q.flat_fourth]

/-- The projected law inherits the Gibbs energy bound, without changing
its endpoint law or claiming that it optimizes the projected support. -/
theorem map_entropy_le_log_energy (Q : StationaryAdditiveLaw S ν)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) {T : Finset H} (e : S → T)
    (hrel : ∀ a b c d : S, a.val + b.val = c.val + d.val →
      (e a).val + (e b).val = (e c).val + (e d).val) :
    (Q.map e hrel).entropy - 2 * finiteEntropy (finitePush ν e) ≤
      Real.log (weightedEnergy T (extendWeight T (fun x ↦ Real.sqrt (finitePush ν e x)))) := by
  exact (Q.map e hrel).entropy_le_log_energy (finitePush_nonneg ν e hν)
    (by rw [finitePush_sum, hs])

end StationaryAdditiveLaw
end
end Erdos539Geometry
