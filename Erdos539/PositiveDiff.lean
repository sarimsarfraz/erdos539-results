/-
Copyright 2026 Kenta Kitamura
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Coordinatewise positive differences and the disjoint fiber count. -/
namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι κ : Type*}

def pdiff (x y : ι → ℝ) : ι → ℝ := fun i ↦ max (x i - y i) 0

def posDiff (F : Finset (ι → ℝ)) : Finset (ι → ℝ) := by
  classical
  exact (F ×ˢ F).image fun p ↦ pdiff p.1 p.2

@[simp] theorem mem_posDiff {F : Finset (ι → ℝ)} {u : ι → ℝ} :
    u ∈ posDiff F ↔ ∃ x ∈ F, ∃ y ∈ F, pdiff x y = u := by
  classical
  simp only [posDiff, Finset.mem_image, Prod.exists, Finset.mem_product]
  aesop

theorem posDiff_mono {F G : Finset (ι → ℝ)} (h : F ⊆ G) :
    posDiff F ⊆ posDiff G := by
  intro u hu
  obtain ⟨x,hx,y,hy,rfl⟩ := mem_posDiff.mp hu
  exact mem_posDiff.mpr ⟨x,h hx,y,h hy,rfl⟩

@[simp] theorem pdiff_translate (x y a : ι → ℝ) :
    pdiff (x + a) (y + a) = pdiff x y := by
  ext i
  simp [pdiff]

theorem posDiff_translate (F : Finset (ι → ℝ)) (a : ι → ℝ) :
    posDiff (F.image (fun x ↦ x + a)) = posDiff F := by
  classical
  ext u
  simp only [mem_posDiff, Finset.mem_image]
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,hu⟩
    exact ⟨x,hx,y,hy,by simpa using hu⟩
  · rintro ⟨x,hx,y,hy,rfl⟩
    exact ⟨x+a,⟨x,hx,rfl⟩,y+a,⟨y,hy,rfl⟩,pdiff_translate x y a⟩

@[simp] theorem pdiff_comp (x y : ι → ℝ) (f : κ → ι) :
    pdiff (x ∘ f) (y ∘ f) = pdiff x y ∘ f := rfl

theorem posDiff_image_comp (F : Finset (ι → ℝ)) (f : κ → ι) :
    posDiff (F.image (fun x ↦ x ∘ f)) = (posDiff F).image (fun x ↦ x ∘ f) := by
  classical
  ext u
  simp only [mem_posDiff, Finset.mem_image]
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,hu⟩
    exact ⟨pdiff x y,⟨x,hx,y,hy,rfl⟩,hu⟩
  · rintro ⟨_,hu,rfl⟩
    obtain ⟨x,hx,y,hy,rfl⟩ := hu
    exact ⟨x ∘ f,⟨x,hx,rfl⟩,y ∘ f,⟨y,hy,rfl⟩,rfl⟩

def join (x : ι → ℝ) (y : κ → ℝ) : (ι ⊕ κ) → ℝ := Sum.elim x y

def mixed (x : ι → ℝ) (y : κ → ℝ) : (ι ⊕ κ) → ℝ :=
  join x (fun j ↦ -y j)

def mixedSet (E : Finset ((ι → ℝ) × (κ → ℝ))) : Finset ((ι ⊕ κ) → ℝ) := by
  classical
  exact E.image fun e ↦ mixed e.1 e.2

@[simp] theorem pdiff_mixed (x x' : ι → ℝ) (y y' : κ → ℝ) :
    pdiff (mixed x y') (mixed x' y) = join (pdiff x x') (pdiff y y') := by
  funext i
  cases i <;> simp [pdiff, mixed, join, sub_eq_add_neg, add_comm]

/-- The second-coordinate family may depend on the first positive difference. -/
theorem sum_card_posDiff_le (E : Finset ((ι → ℝ) × (κ → ℝ)))
    (U : Finset (ι → ℝ)) (C : (ι → ℝ) → Finset (κ → ℝ))
    (hC : ∀ u ∈ posDiff U, ∃ x ∈ U, ∃ x' ∈ U,
      pdiff x x' = u ∧ ∀ y ∈ C u, (x,y) ∈ E ∧ (x',y) ∈ E) :
    ∑ u ∈ posDiff U, (posDiff (C u)).card ≤ (posDiff (mixedSet E)).card := by
  classical
  let S := (posDiff U).sigma fun u ↦ posDiff (C u)
  let f : (Σ _ : ι → ℝ, κ → ℝ) → (ι ⊕ κ) → ℝ := fun z ↦ join z.1 z.2
  have hf : Function.Injective f := by
    intro z z' h
    have hu : z.1 = z'.1 := funext fun i ↦ congrFun h (Sum.inl i)
    have hv : z.2 = z'.2 := funext fun j ↦ congrFun h (Sum.inr j)
    cases z
    cases z'
    cases hu
    cases hv
    rfl
  have hmaps : ∀ z ∈ S, f z ∈ posDiff (mixedSet E) := by
    intro z hz
    obtain ⟨hu,hv⟩ := Finset.mem_sigma.mp hz
    obtain ⟨x,hx,x',hx',hu',hxy⟩ := hC z.1 hu
    obtain ⟨y,hy,y',hy',hv'⟩ := mem_posDiff.mp hv
    apply mem_posDiff.mpr
    refine ⟨mixed x y',Finset.mem_image.mpr ⟨(x,y'),(hxy y' hy').1,rfl⟩,
      mixed x' y,Finset.mem_image.mpr ⟨(x',y),(hxy y hy).2,rfl⟩,?_⟩
    simp [f, ← hu', ← hv']
  calc
    _ = S.card := (Finset.card_sigma _ _).symm
    _ ≤ _ := Finset.card_le_card_of_injOn f hmaps hf.injOn

end
end Erdos539Geometry
