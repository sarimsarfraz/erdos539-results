/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Gluing

namespace Erdos539Geometry
noncomputable section
open scoped Classical
variable {ι κ : Type*}

theorem gluing_diameter {F : Finset (ι → ℤ)} {G : Finset (κ → ℤ)}
    {B L : ℤ} (hB : 0 ≤ B) (K : ℕ)
    (hF : ∀ x ∈ F, ∀ y ∈ F, ∀ i, |x i - y i| ≤ L)
    (hG : ∀ x ∈ G, ∀ y ∈ G, ∀ i, |x i - y i| ≤ L) :
    ∀ x ∈ gluing F G K B, ∀ y ∈ gluing F G K B, ∀ i,
      |x i - y i| ≤ L + (K : ℤ) * B := by
  intro x hx y hy i
  obtain ⟨s, hs, a, ha, b, hb, rfl⟩ := mem_gluing.mp hx
  obtain ⟨t, ht, c, hc, d, hd, rfl⟩ := mem_gluing.mp hy
  have hst : |(s : ℤ) - t| ≤ K := by apply abs_le.mpr; constructor <;> omega
  have hshift : |((s : ℤ) - t) * B| ≤ (K : ℤ) * B := by
    rw [abs_mul, abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_right hst hB
  cases i with
  | inl i =>
    change |a i + (s : ℤ) * B - (c i + (t : ℤ) * B)| ≤ _
    calc
      _ = |(a i - c i) + ((s : ℤ) - t) * B| := by congr 1; ring
      _ ≤ |a i - c i| + |((s : ℤ) - t) * B| := abs_add_le _ _
      _ ≤ _ := add_le_add (hF a ha c hc i) hshift
  | inr i =>
    change |b i - (s : ℤ) * B - (d i - (t : ℤ) * B)| ≤ _
    calc
      _ = |(b i - d i) - ((s : ℤ) - t) * B| := by congr 1; ring
      _ ≤ |b i - d i| + |((s : ℤ) - t) * B| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (b i - d i) 0 (((s : ℤ) - t) * B))
      _ ≤ _ := add_le_add (hG b hb d hd i) hshift

end
end Erdos539Geometry
