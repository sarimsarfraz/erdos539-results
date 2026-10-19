/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SidonFiberSharpness

namespace Erdos539Geometry
open scoped Pointwise

def scalarSidonCode (n a : ℕ) : ℕ := a + 2 * n * a ^ 2

def scalarSidonSet (n : ℕ) : Finset ℤ :=
  (Finset.range n).image (fun a ↦ (scalarSidonCode n a : ℤ))

theorem scalarSidonCode_strictMono (n : ℕ) : StrictMono (scalarSidonCode n) := by
  intro a b hab
  unfold scalarSidonCode
  exact Nat.add_lt_add_of_lt_of_le hab (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab.le 2))

theorem scalarSidonSet_card (n : ℕ) : (scalarSidonSet n).card = n := by
  rw [scalarSidonSet, Finset.card_image_of_injective]
  · exact Finset.card_range n
  · intro a b h
    exact (scalarSidonCode_strictMono n).injective (Int.ofNat.inj h)

private theorem code_sum_recovers {n a b c d : ℕ}
    (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n)
    (he : scalarSidonCode n a + scalarSidonCode n b = scalarSidonCode n c + scalarSidonCode n d) :
    a + b = c + d ∧ a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by
  have he' : (a + b) + (a ^ 2 + b ^ 2) * (2 * n) =
      (c + d) + (c ^ 2 + d ^ 2) * (2 * n) := by
    calc
      _ = scalarSidonCode n a + scalarSidonCode n b := by unfold scalarSidonCode; ring
      _ = scalarSidonCode n c + scalarSidonCode n d := he
      _ = _ := by unfold scalarSidonCode; ring
  have hmod := congrArg (fun z : ℕ ↦ z % (2 * n)) he'
  have hab : a + b < 2 * n := by omega
  have hcd : c + d < 2 * n := by omega
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt hcd] at hmod
  refine ⟨hmod, ?_⟩
  have hp : 0 < 2 * n := by omega
  exact Nat.eq_of_mul_eq_mul_right hp (Nat.add_left_cancel (hmod ▸ he'))

private theorem pair_of_sum_and_squares {a b c d : ℤ}
    (hs : a + b = c + d) (hq : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hs2 := congrArg (fun z : ℤ ↦ z ^ 2) hs
  have hsa := congrArg (fun z : ℤ ↦ a * z) hs
  have hp : (a - c) * (a - d) = 0 := by nlinarith
  rcases mul_eq_zero.mp hp with h | h
  · left; constructor <;> omega
  · right; constructor <;> omega

/-- An explicit scalar Sidon set of every prescribed cardinality. -/
theorem scalarSidonSet_sidon (n : ℕ) : HasSidonSums (scalarSidonSet n) := by
  intro a ha b hb c hc d hd he
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hd
  have he' : scalarSidonCode n i + scalarSidonCode n j = scalarSidonCode n k + scalarSidonCode n l := by
    exact_mod_cast he
  obtain ⟨hs, hq⟩ := code_sum_recovers (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
    (Finset.mem_range.mp hk) (Finset.mem_range.mp hl) he'
  have hs' : (i : ℤ) + j = k + l := by exact_mod_cast hs
  have hq' : (i : ℤ) ^ 2 + j ^ 2 = k ^ 2 + l ^ 2 := by exact_mod_cast hq
  rcases pair_of_sum_and_squares hs' hq' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have hi : i = k := by exact_mod_cast h₁
    have hj : j = l := by exact_mod_cast h₂
    subst k; subst l
    exact Or.inl ⟨rfl, rfl⟩
  · have hi : i = l := by exact_mod_cast h₁
    have hj : j = k := by exact_mod_cast h₂
    subst l; subst k
    exact Or.inr ⟨rfl, rfl⟩

end Erdos539Geometry
