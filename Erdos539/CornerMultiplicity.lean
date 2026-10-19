/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CornerSelection
import Mathlib.Data.Fintype.Prod

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*}

def flipCornerTriple (t : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ)) :
    ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ) := ((t.1.2, t.1.1), t.2)

theorem flipCornerTriple_mem {S : Finset (ι → ℝ)} {t : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ)}
    (ht : t ∈ cornerTriples S) : flipCornerTriple t ∈ cornerTriples S := by
  obtain ⟨hp, hb⟩ := Finset.mem_filter.mp ht
  obtain ⟨hab, hz⟩ := Finset.mem_product.mp hp
  obtain ⟨ha, hc⟩ := Finset.mem_product.mp hab
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hc, ha⟩, hz⟩, ?_⟩
  intro i
  simpa only [flipCornerTriple, min_comm, max_comm] using hb i

theorem cornerTripleSet_flip (t : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ)) :
    cornerTripleSet (flipCornerTriple t) = cornerTripleSet t := by
  simp only [cornerTripleSet, flipCornerTriple, Finset.insert_comm]

/-- Every three-point edge supplies two distinct ordered corner witnesses. -/
theorem two_mul_card_cornerEdges_le_triples (S : Finset (ι → ℝ)) :
    2 * (cornerEdges S).card ≤ (cornerTriples S).card := by
  have hw (e : cornerEdges S) : ∃ t ∈ cornerTriples S, cornerTripleSet t = e.val := by
    exact Finset.mem_image.mp (Finset.mem_filter.mp e.property).1
  choose w hwm hwe using hw
  have hne (e : cornerEdges S) : w e ≠ flipCornerTriple (w e) := by
    intro he
    have hab : (w e).1.1 = (w e).1.2 := congrArg (fun t ↦ t.1.1) he
    have hc := (cornerEdges_spec S e.property).2
    rw [← hwe e] at hc
    have hsmall : (cornerTripleSet (w e)).card ≤ 2 := by
      simp only [cornerTripleSet, hab, Finset.insert_idem]
      have hpair := Finset.card_pair_eq_one_or_two (a := (w e).1.2) (b := (w e).2)
      omega
    omega
  let g : (cornerEdges S) × Bool → cornerTriples S := fun z ↦
    if z.2 then ⟨w z.1, hwm z.1⟩ else ⟨flipCornerTriple (w z.1), flipCornerTriple_mem (hwm z.1)⟩
  have hset (z : (cornerEdges S) × Bool) : cornerTripleSet (g z).val = z.1.val := by
    rcases z with ⟨e, b⟩
    cases b <;> simp only [g, Bool.false_eq_true, ↓reduceIte, cornerTripleSet_flip, hwe]
  have hinj : Function.Injective g := by
    rintro ⟨e, b⟩ ⟨e', b'⟩ he
    have hes := congrArg (fun t : cornerTriples S ↦ cornerTripleSet t.val) he
    change cornerTripleSet (g (e, b)).val = cornerTripleSet (g (e', b')).val at hes
    rw [hset, hset] at hes
    have hee : e = e' := Subtype.ext hes
    subst e'
    have ht := congrArg Subtype.val he
    cases b <;> cases b' <;> simp only [g, Bool.false_eq_true, ↓reduceIte] at ht ⊢
    · exact False.elim (hne e ht.symm)
    · exact False.elim (hne e ht)
  have hc := Fintype.card_le_of_injective g hinj
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, Nat.mul_comm] using hc

/-- Ordered corner incidences are at most N squared times the largest box. -/
theorem card_cornerTriples_le (S : Finset (ι → ℝ)) {B : ℕ}
    (hB : ∀ a ∈ S, ∀ b ∈ S, (cornerSlice S a b).card ≤ B) :
    (cornerTriples S).card ≤ S.card ^ 2 * B := by
  have maps : (cornerTriples S : Set (((ι → ℝ) × (ι → ℝ)) × (ι → ℝ))).MapsTo
      Prod.fst (↑(S ×ˢ S) : Set ((ι → ℝ) × (ι → ℝ))) := by
    intro t ht
    exact (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1
  rw [card_eq_sum_card_parent (cornerTriples S) Prod.fst (S ×ˢ S) maps]
  calc
    _ ≤ ∑ _ab ∈ S ×ˢ S, B := by
      apply Finset.sum_le_sum
      intro ab hab
      have hf := Finset.card_le_card_of_injOn Prod.snd
        (s := fiber (cornerTriples S) Prod.fst ab) (t := cornerSlice S ab.1 ab.2) ?_ ?_
      · exact hf.trans (hB ab.1 (Finset.mem_product.mp hab).1 ab.2 (Finset.mem_product.mp hab).2)
      · intro t ht
        obtain ⟨ht, he⟩ := mem_fiber.mp ht
        obtain ⟨hp, hb⟩ := Finset.mem_filter.mp ht
        apply mem_cornerSlice.mpr
        refine ⟨(Finset.mem_product.mp hp).2, ?_⟩
        simpa only [he] using hb
      · intro t ht u hu he
        exact Prod.ext ((mem_fiber.mp ht).2.trans (mem_fiber.mp hu).2.symm) he
    _ = _ := by simp [pow_two]

end
end Erdos539Geometry
