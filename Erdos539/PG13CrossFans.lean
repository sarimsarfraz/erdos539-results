/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13BranchFans
import Erdos539.ImageFiberCardBound

namespace Erdos539Geometry
noncomputable section
open scoped Classical

/-- With an anchor on another line, equality at the unique intersection
coordinate determines the entire positive-difference output. -/
theorem pg13_cross_fan_fiber {T : ℕ} (hT : 0 < T) {l m q : Fin 13}
    (hinter : pg13LineSet l ∩ pg13LineSet m = {q})
    {a x y : Fin 13 → ℤ} (ha : a ∈ pg13Branch T l)
    (hx : x ∈ pg13Branch T m) (hy : y ∈ pg13Branch T m) (hxy : x q = y q) :
    intPdiff x a = intPdiff y a := by
  funext j
  change max (x j - a j) 0 = max (y j - a j) 0
  by_cases hjl : j ∈ pg13LineSet l
  · by_cases hjm : j ∈ pg13LineSet m
    · have hj : j = q := by
        have hmem := Finset.mem_inter.mpr ⟨hjl, hjm⟩
        rwa [hinter, Finset.mem_singleton] at hmem
      subst j
      rw [hxy]
    · rw [(pg13Branch_coordinate_bounds hT m hx j).2 hjm,
        (pg13Branch_coordinate_bounds hT m hy j).2 hjm]
  · have haj := (pg13Branch_coordinate_bounds hT l ha j).2 hjl
    by_cases hjm : j ∈ pg13LineSet m
    · have hxj := ((pg13Branch_coordinate_bounds hT m hx j).1 hjm).2
      have hyj := ((pg13Branch_coordinate_bounds hT m hy j).1 hjm).2
      rw [max_eq_right (by omega), max_eq_right (by omega)]
    · rw [(pg13Branch_coordinate_bounds hT m hx j).2 hjm,
        (pg13Branch_coordinate_bounds hT m hy j).2 hjm]

/-- Every cross-branch fan has at most T^3 values, for each actual anchor. -/
theorem pg13_cross_fan_card {T : ℕ} (hT : 0 < T) {l m : Fin 13} (hlm : l ≠ m)
    {a : Fin 13 → ℤ} (ha : a ∈ pg13Branch T l) :
    (integerFan (pg13Branch T m) a).card ≤ T ^ 3 := by
  have hcard := pg13_incidence_certificate.2.2.2.2.2.2 l m hlm
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
  have hqm : q ∈ pg13LineSet m := by
    have hh : q ∈ pg13LineSet l ∩ pg13LineSet m := by rw [hq]; simp
    exact (Finset.mem_inter.mp hh).2
  calc
    _ ≤ ((pg13Branch T m).image (fun x ↦ x q)).card :=
      @card_image_le_of_fibers _ _ _ (Classical.decEq _) Int.instDecidableEq (pg13Branch T m) (fun x ↦ intPdiff x a) (fun x ↦ x q)
        (fun _ hx _ hy he ↦ pg13_cross_fan_fiber hT hq ha hx hy he)
    _ = T ^ 3 := pg13Branch_coordinate_card hT m hqm

end
end Erdos539Geometry
