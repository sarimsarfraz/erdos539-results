/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ChannelPotentials

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Reverse rank inside one bin of a finite linearly ordered support. -/
def binUpperSet {α γ : Type*} [Fintype α] [LinearOrder α]
    (bin : α → γ) (a : α) : Finset α :=
  Finset.univ.filter (fun x ↦ bin x = bin a ∧ a ≤ x)

def binReverseRank {α γ : Type*} [Fintype α] [LinearOrder α]
    (bin : α → γ) (a : α) : ℕ := (binUpperSet bin a).card

theorem self_mem_binUpperSet {α γ : Type*} [Fintype α] [LinearOrder α]
    (bin : α → γ) (a : α) : a ∈ binUpperSet bin a := by simp [binUpperSet]

theorem binReverseRank_pos {α γ : Type*} [Fintype α] [LinearOrder α]
    (bin : α → γ) (a : α) : 0 < binReverseRank bin a :=
  Finset.card_pos.mpr ⟨a, self_mem_binUpperSet bin a⟩

theorem binReverseRank_le_card {α γ : Type*} [Fintype α] [LinearOrder α]
    (bin : α → γ) (a : α) : binReverseRank bin a ≤ Fintype.card α := by
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_univ)

theorem binReverseRank_strictAnti {α γ : Type*} [Fintype α] [LinearOrder α]
    (bin : α → γ) {a b : α} (hbin : bin a = bin b) (hab : a < b) :
    binReverseRank bin b < binReverseRank bin a := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨_, hxbin, hbx⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hxbin.trans hbin.symm, hab.le.trans hbx⟩
  · intro he
    have ha := self_mem_binUpperSet bin a
    rw [← he] at ha
    have hba := (Finset.mem_filter.mp ha).2.2
    exact (not_le.mpr hab) hba

def binRankIndex {α γ : Type*} [Fintype α] [LinearOrder α]
    (bin : α → γ) (a : α) : Fin (Fintype.card α) :=
  ⟨binReverseRank bin a - 1, by
    have hp := binReverseRank_pos bin a
    have hb := binReverseRank_le_card bin a
    omega⟩

theorem binRankIndex_add_one {α γ : Type*} [Fintype α] [LinearOrder α]
    (bin : α → γ) (a : α) : (binRankIndex bin a).val + 1 = binReverseRank bin a := by
  exact Nat.sub_add_cancel (binReverseRank_pos bin a)

theorem bin_rank_injective {α γ : Type*} [Fintype α] [LinearOrder α] (bin : α → γ) :
    Function.Injective (fun a ↦ (bin a, binRankIndex bin a)) := by
  intro a b he
  have hbin := congrArg Prod.fst he
  have hr := congrArg (fun z : γ × Fin (Fintype.card α) ↦ z.2.val + 1) he
  simp only [binRankIndex_add_one] at hr
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim ((ne_of_gt (binReverseRank_strictAnti bin hbin hab)) hr)
  · exact hab
  · exact False.elim ((ne_of_lt (binReverseRank_strictAnti bin hbin.symm hab)) hr)

end
end Erdos539Geometry
