/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FourLeafBranch
import Erdos539.FiniteUniformImage
import Erdos539.FiniteEntropyKernel

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical

def fourLeafObserve (T : ℕ) (I : Finset (Fin 4)) (a : Fin 7 → Fin T) :
    (fourLeafBranch T).image (fun x (i : I) ↦ x i.val) :=
  imageEndpoint (fourLeafBranch T) (fun x (i : I) ↦ x i.val) (finiteImageEndpoint (fourLeafEncode T) a)

theorem fourLeafObserve_same_fibers {T : ℕ} (hT : 0 < T) (I : Finset (Fin 4))
    (a b : Fin 7 → Fin T) :
    fourLeafObserve T I a = fourLeafObserve T I b ↔
      (fun j : fourLeafActiveDigits I ↦ a j.val) = (fun j : fourLeafActiveDigits I ↦ b j.val) := by
  have ha : ∀ j, 0 ≤ (a j : ℤ) ∧ (a j : ℤ) < 10 * T := by
    intro j; have := (a j).isLt; constructor <;> omega
  have hb : ∀ j, 0 ≤ (b j : ℤ) ∧ (b j : ℤ) < 10 * T := by
    intro j; have := (b j).isLt; constructor <;> omega
  have hh := fourLeaf_projection_eq_iff (by omega : (0 : ℤ) < 10 * T) ha hb I
  constructor
  · intro h
    have hobs : ∀ i ∈ I, fourLeafLinear (10 * T) (fun j ↦ (a j : ℤ)) i =
        fourLeafLinear (10 * T) (fun j ↦ (b j : ℤ)) i := by
      intro i hi
      exact congrFun (congrArg Subtype.val h) ⟨i, hi⟩
    funext j
    apply Fin.ext
    exact_mod_cast hh.mp hobs j.val j.property
  · intro h
    apply Subtype.ext
    funext i
    apply hh.mpr _ i.val i.property
    intro j hj
    have he := congrFun h ⟨j, hj⟩
    exact_mod_cast congrArg Fin.val he

/-- Exact projection entropy of the literal seven-digit branch for every
coordinate subset, not just a lower bound or a finite-size experiment. -/
theorem fourLeafBranch_projection_entropy {T : ℕ} (hT : 0 < T) (I : Finset (Fin 4)) :
    finiteEntropy (finitePush (uniformReference (fourLeafBranch T))
      (imageEndpoint (fourLeafBranch T) (fun x (i : I) ↦ x i.val))) =
      ((fourLeafActiveDigits I).card : ℝ) * Real.log (T : ℝ) := by
  haveI : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  have h := finiteEntropy_push_eq_of_same_fibers
    (finiteUniformWeight (Fin 7 → Fin T)) (fourLeafObserve T I)
    (fun a (j : fourLeafActiveDigits I) ↦ a j.val) (fourLeafObserve_same_fibers hT I)
  have hr := finiteUniformWeight_restrict_entropy (α := Fin T) (fourLeafActiveDigits I)
  have hfinal := h.trans hr
  have he : finitePush (finiteUniformWeight (Fin 7 → Fin T)) (fourLeafObserve T I) =
      finitePush (uniformReference (fourLeafBranch T))
        (imageEndpoint (fourLeafBranch T) (fun x (i : I) ↦ x i.val)) := by
    have hw := finiteUniformWeight_image (fourLeafEncode T) (fourLeafEncode_injective T)
    change finitePush (finiteUniformWeight (Fin 7 → Fin T)) (finiteImageEndpoint (fourLeafEncode T)) =
      uniformReference (fourLeafBranch T) at hw
    rw [← hw]
    exact (finitePush_comp (finiteUniformWeight (Fin 7 → Fin T))
      (finiteImageEndpoint (fourLeafEncode T))
      (imageEndpoint (fourLeafBranch T) (fun x (i : I) ↦ x i.val))).symm
  simpa only [he, Fintype.card_fin] using hfinal

end
end Erdos539Geometry
