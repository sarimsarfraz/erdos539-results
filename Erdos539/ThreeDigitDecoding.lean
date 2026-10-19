/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarRadixEmbedding

namespace Erdos539Geometry

theorem bounded_radix_recover {B u v a b : ℤ} (hB : 0 < B)
    (hu : 0 ≤ u ∧ u < B) (hv : 0 ≤ v ∧ v < B)
    (he : u + B * a = v + B * b) : u = v ∧ a = b := by
  have hm := congrArg (fun z : ℤ ↦ z % B) he
  simp only [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hu.1 hu.2,
    Int.emod_eq_of_lt hv.1 hv.2] at hm
  refine ⟨hm, ?_⟩
  rw [hm] at he
  exact mul_left_cancel₀ hB.ne' (add_left_cancel he)

/-- All three digits are recovered even with either sign at either high
place. The low and middle digits are in a single radix interval. -/
theorem signed_three_digit_recover {B u v s t r q ε δ : ℤ} (hB : 0 < B)
    (hu : 0 ≤ u ∧ u < B) (hv : 0 ≤ v ∧ v < B)
    (hs : 0 ≤ s ∧ s < B) (ht : 0 ≤ t ∧ t < B)
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1)
    (he : ε * B ^ 2 * r + δ * B * s + u = ε * B ^ 2 * q + δ * B * t + v) :
    u = v ∧ s = t ∧ r = q := by
  have he' : u + B * (δ * s + B * (ε * r)) = v + B * (δ * t + B * (ε * q)) := by
    nlinarith [he]
  obtain ⟨huv, hhigh⟩ := bounded_radix_recover hB hu hv he'
  refine ⟨huv, ?_⟩
  rcases hδ with rfl | rfl
  · simp only [one_mul] at hhigh
    obtain ⟨hst, hrq⟩ := bounded_radix_recover hB hs ht hhigh
    refine ⟨hst, ?_⟩
    rcases hε with rfl | rfl <;> linarith
  · have he2 : s + B * (-ε * r) = t + B * (-ε * q) := by nlinarith [hhigh]
    obtain ⟨hst, hrq⟩ := bounded_radix_recover hB hs ht he2
    refine ⟨hst, ?_⟩
    rcases hε with rfl | rfl <;> linarith

end Erdos539Geometry
