/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryLawPush
import Erdos539.StationaryTripleLaw
import Erdos539.QuadrupleEntropy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

def forgetFourth {α : Type*} : (α × α) × (α × α) → (α × α) × α :=
  fun z ↦ (z.1, z.2.1)

/-- The triple marginal of the actual quadruple law. -/
def triple (Q : StationaryAdditiveLaw S ν) : StationaryTripleLaw S ν where
  mass := finitePush Q.flat forgetFourth
  nonneg := finitePush_nonneg Q.flat forgetFourth (fun z ↦ Q.nonneg z.1.1 z.1.2 z.2.1 z.2.2)
  first := by rw [finitePush_comp]; exact Q.flat_first
  second := by rw [finitePush_comp]; exact Q.flat_second
  third := by rw [finitePush_comp]; exact Q.flat_third

/-- Three endpoints determine the fourth on the actual nonzero support,
so passing to the triple marginal loses no entropy. -/
theorem triple_entropy_eq (Q : StationaryAdditiveLaw S ν) :
    finiteEntropy Q.triple.mass = Q.entropy := by
  have hinj : ∀ a b, Q.flat a ≠ 0 → Q.flat b ≠ 0 → forgetFourth a = forgetFourth b → a = b := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ hp hq he
    have hleft : (a, b) = (a', b') := congrArg Prod.fst he
    have hc : c = c' := congrArg Prod.snd he
    obtain ⟨ha, hb⟩ := Prod.mk.inj hleft
    subst a'
    subst b'
    subst c'
    have hpRel : a.val + b.val = c.val + d.val := by
      by_contra hh
      exact hp (Q.supported a b c d hh)
    have hqRel : a.val + b.val = c.val + d'.val := by
      by_contra hh
      exact hq (Q.supported a b c d' hh)
    have hd : d = d' := Subtype.ext (add_left_cancel (hpRel.symm.trans hqRel))
    subst d'
    rfl
  calc
    _ = finiteEntropy Q.flat := finiteEntropy_push_eq_of_support_injective Q.flat forgetFourth hinj
    _ = Q.entropy := by simp only [finiteEntropy, flat, entropy, Fintype.sum_prod_type]

theorem triple_map_mass (Q : StationaryAdditiveLaw S ν) {T : Finset H} (e : S → T)
    (hrel : ∀ a b c d : S, a.val + b.val = c.val + d.val →
      (e a).val + (e b).val = (e c).val + (e d).val) :
    (Q.map e hrel).triple.mass = (Q.triple.map e).mass := by
  change finitePush (finitePush Q.flat (mapFour e)) forgetFourth =
    finitePush (finitePush Q.flat forgetFourth) (mapThree e)
  rw [finitePush_comp, finitePush_comp]
  rfl

/-- The manuscript's correlation profile for an actual stationary law. -/
def correlation (Q : StationaryAdditiveLaw S ν) : ℝ := 3 * finiteEntropy ν - Q.entropy

theorem correlation_nonneg (Q : StationaryAdditiveLaw S ν)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) : 0 ≤ Q.correlation := by
  have h := Q.triple.correlation_nonneg hν hs
  rwa [Q.triple_entropy_eq] at h

/-- Correlation decreases when every endpoint is pushed through the same
additive-relation-preserving map. No new optimizer is introduced. -/
theorem correlation_map_le (Q : StationaryAdditiveLaw S ν) (hν : ∀ x, 0 ≤ ν x)
    {T : Finset H} (e : S → T)
    (hrel : ∀ a b c d : S, a.val + b.val = c.val + d.val →
      (e a).val + (e b).val = (e c).val + (e d).val) :
    (Q.map e hrel).correlation ≤ Q.correlation := by
  have h := Q.triple.correlation_map_le hν e
  rw [← Q.triple_map_mass e hrel, (Q.map e hrel).triple_entropy_eq, Q.triple_entropy_eq] at h
  exact h

end StationaryAdditiveLaw

variable [DecidableEq G]

/-- At an exact optimizer, total correlation is the manuscript's entropy
defect H(mu)-log Lambda, with the previously proved canonical law. -/
theorem optimizerStationaryAdditiveLaw_correlation {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    (optimizerStationaryAdditiveLaw hS hf hE).correlation =
      finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm S) := by
  have h := optimizerQuadrupleEntropy_eq hS hf hE
  change 3 * finiteEntropy (fun x ↦ f x ^ 2) - optimizerQuadrupleEntropy S f = _
  linarith

end
end Erdos539Geometry
