/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Mathlib.CategoryTheory.Galois.FiberAutMap

/-!
# Injectivity of `Aut F → Aut G`

Let `C` be a Galois category with fibre functor `F`, `H : D ⥤ C` a functor and
`e : H ⋙ F ≅ G`. If every connected object of `C` is a subobject of some `H.obj A`, then
`fiberAutMap e : Aut F →* Aut G` is injective (SGA 1 V.6.11, Stacks 0BN6 (2)): an automorphism
acting trivially on all fibres `F(H A)` acts trivially on their subobjects, hence on all connected
objects, hence on every fibre.
-/

@[expose] public section

universe u₁ u₂ u₃ u₄

namespace CategoryTheory.PreGaloisCategory

open Limits Functor

variable {C : Type u₁} [Category.{u₂} C] {D : Type u₃} [Category.{u₄} D]
  [GaloisCategory C] (F : C ⥤ FintypeCat.{u₂}) [FiberFunctor F] {G : D ⥤ FintypeCat.{u₂}}

/-- **Injectivity criterion** (SGA 1 V.6.11): if every connected object of `C` admits a
monomorphism into an object in the image of `H`, then `Aut F → Aut G` is injective. -/
theorem fiberAutMap_injective {H : D ⥤ C} (e : H ⋙ F ≅ G)
    (hH : ∀ X : C, IsConnected X → ∃ (A : D) (i : X ⟶ H.obj A), Mono i) :
    Function.Injective (fiberAutMap e) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  -- `σ` acts trivially on the fibres of objects in the image of `H`.
  have hHA (A : D) (y : F.obj (H.obj A)) : σ.hom.app (H.obj A) y = y := by
    have h1 := congr_arg (fun τ : Aut G ↦ τ.hom.app A (e.hom.app A y)) hσ
    simp only [fiberAutMap_hom_app_apply] at h1
    have h2 : e.inv.app A (e.hom.app A y) = y := FintypeCat.hom_inv_id_apply (e.app A) y
    rw [h2] at h1
    change e.hom.app A (σ.hom.app (H.obj A) y) = e.hom.app A y at h1
    have h3 := congr_arg (e.inv.app A) h1
    have h4 (z : F.obj (H.obj A)) : e.inv.app A (e.hom.app A z) = z :=
      FintypeCat.hom_inv_id_apply (e.app A) z
    rwa [h4, h4] at h3
  -- hence on the fibres of connected objects
  have hconn (X : C) [IsConnected X] (x : F.obj X) : σ.hom.app X x = x := by
    obtain ⟨A, i, hi⟩ := hH X inferInstance
    have hinj : Function.Injective (F.map i) :=
      (ConcreteCategory.mono_iff_injective_of_preservesPullback (F.map i)).mp inferInstance
    apply hinj
    have := congr_arg (fun f ↦ f x) (σ.hom.naturality i)
    simp only at this
    change (F.map i) (σ.hom.app X x) = F.map i x
    rw [← FintypeCat.comp_apply, ← this, FintypeCat.comp_apply, hHA]
  -- hence everywhere
  refine Iso.ext (NatTrans.ext (funext fun X ↦ FintypeCat.hom_ext _ _ fun x ↦ ?_))
  obtain ⟨A, f, a, hA, rfl⟩ := exists_hom_from_galois_of_fiber F X x
  have := congr_arg (fun g ↦ g a) (σ.hom.naturality f)
  simp only at this
  change σ.hom.app X (F.map f a) = F.map f a
  rw [← FintypeCat.comp_apply, this, FintypeCat.comp_apply, hconn]

end CategoryTheory.PreGaloisCategory
