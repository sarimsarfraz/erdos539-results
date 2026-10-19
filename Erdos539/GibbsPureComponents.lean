/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsInterleavedBudget
import Erdos539.UniformImageFibers

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]
local instance pureComponentsFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance pureComponentsImageDecidableEq (s : GibbsReference G) (n : ℕ) (label : G → Fin n) :
    DecidableEq (s.support.image label) := Classical.decEq _

namespace GibbsReference

omit [AddCommGroup G] [DecidableEq G] in
theorem component_uniform (s : GibbsReference G) (hs : s.weight = uniformReference s.support)
    (n : ℕ) (label : G → Fin n) (i : s.support.image label) :
    (s.component label i).weight = uniformReference (s.component label i).support := by
  change imageFiberReference s.support label s.weight i = uniformReference _
  rw [hs, uniformReference_imageFiber s.nonempty]

end GibbsReference

namespace GibbsInterleavedRecursion

/-- A finite actual recursion containing only separated-component selections. -/
def IsPure : {s : GibbsReference G} → GibbsInterleavedRecursion s → Prop
  | _, .leaf _ => True
  | _, .cut _ _ _ _ => False
  | _, .select _ _ _ _ f => ∀ i, (f i).IsPure

def selectedLeaf : {s : GibbsReference G} → (t : GibbsInterleavedRecursion s) → t.IsPure → t.Outcome → GibbsReference G
  | _, .leaf s, _, _ => s
  | _, .cut _ _ _ _, hp, _ => hp.elim
  | _, .select _ _ _ _ f, hp, x => (f x.1).selectedLeaf (hp x.1) x.2

def logMassCost : {s : GibbsReference G} → (t : GibbsInterleavedRecursion s) → t.IsPure → t.Outcome → ℝ
  | _, .leaf _, _, _ => 0
  | _, .cut _ _ _ _, hp, _ => hp.elim
  | _, .select s _ label _ f, hp, x =>
    -Real.log (finitePush s.weight (imageEndpoint s.support label) x.1) +
      (f x.1).logMassCost (hp x.1) x.2

theorem selectedLeaf_subset {s : GibbsReference G} (t : GibbsInterleavedRecursion s)
    (hp : t.IsPure) (x : t.Outcome) : (t.selectedLeaf hp x).support ⊆ s.support := by
  induction t with
  | leaf s => exact Finset.Subset.refl _
  | cut s φ p f ihp ihf => exact hp.elim
  | select s n label hsep f ih =>
    exact (ih x.1 (hp x.1) x.2).trans (fun _ hx ↦ (mem_fiber.mp hx).1)

theorem selectedLeaf_uniform {s : GibbsReference G} (t : GibbsInterleavedRecursion s)
    (hp : t.IsPure) (hs : s.weight = uniformReference s.support) (x : t.Outcome) :
    (t.selectedLeaf hp x).weight = uniformReference (t.selectedLeaf hp x).support := by
  induction t with
  | leaf s => exact hs
  | cut s φ p f ihp ihf => exact hp.elim
  | select s n label hsep f ih =>
    exact ih x.1 (hp x.1) (s.component_uniform hs n label x.1) x.2

/-- The actual carried-reference charges telescope along every selected path,
not only in expectation. -/
theorem logMassCost_eq {s : GibbsReference G} (t : GibbsInterleavedRecursion s)
    (hp : t.IsPure) (hs : s.weight = uniformReference s.support) (x : t.Outcome) :
    t.logMassCost hp x = Real.log (s.support.card : ℝ) - Real.log ((t.selectedLeaf hp x).support.card : ℝ) := by
  induction t with
  | leaf s => simp only [logMassCost, selectedLeaf, sub_self]
  | cut s φ p f ihp ihf => exact hp.elim
  | select s n label hsep f ih =>
    change -Real.log (finitePush s.weight (imageEndpoint s.support label) x.1) +
      (f x.1).logMassCost (hp x.1) x.2 = _
    rw [ih x.1 (hp x.1) (s.component_uniform hs n label x.1) x.2,
      hs, uniformReference_image_mass]
    have hN : (0 : ℝ) < s.support.card := by exact_mod_cast s.nonempty.card_pos
    have hA : (0 : ℝ) < (Erdos539Geometry.fiber s.support label x.1.val).card := by
      exact_mod_cast (imageFiber_nonempty s.support label x.1).card_pos
    rw [Real.log_div hA.ne' hN.ne']
    change -(Real.log _ - Real.log _) + (Real.log _ - Real.log _) = _
    simp only [GibbsReference.component, selectedLeaf]
    ring

theorem logMassCost_eq_log_ratio {s : GibbsReference G} (t : GibbsInterleavedRecursion s)
    (hp : t.IsPure) (hs : s.weight = uniformReference s.support) (x : t.Outcome) :
    t.logMassCost hp x = Real.log ((s.support.card : ℝ) / (t.selectedLeaf hp x).support.card) := by
  have hN : (s.support.card : ℝ) ≠ 0 := by exact_mod_cast s.nonempty.card_pos.ne'
  have hT : ((t.selectedLeaf hp x).support.card : ℝ) ≠ 0 := by
    exact_mod_cast (t.selectedLeaf hp x).nonempty.card_pos.ne'
  rw [Real.log_div hN hT, t.logMassCost_eq hp hs x]

end GibbsInterleavedRecursion
end
end Erdos539Geometry
