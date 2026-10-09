/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Orbicurve.Core
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Composition of finite étale morphisms of affine orbicurves; transport of cores

* `AffOrbicurve.Hom.id`, `AffOrbicurve.Hom.comp`: finite étale morphisms compose (ramification
  indices are multiplicative in towers);
* `AffOrbicurve.Iso`: isomorphisms;
* `AffOrbicurve.IsCoreOf.of_hom`: if `A → B` is finite étale, a core of `B` is a core of `A`;
  `AffOrbicurve.IsCoreOf.of_hom_of_pullback`: conversely, if moreover every `Z → B` is dominated
  by some `Z' → A` (a component of `Z ×_B A`), a core of `A` is a core of `B`;
* `AffOrbicurve.IsCoreOf.congr_left`, `AffOrbicurve.IsCoreOf.congr_right`: cores are invariant
  under isomorphisms.
-/

@[expose] public section

universe u

open Ideal

namespace AffOrbicurve

variable {k : Type u} [Field k]

section Hom

/-- The identity morphism. -/
def Hom.id (X : AffOrbicurve k) : Hom X X where
  f := AlgHom.id k X.A
  injective := Function.injective_id
  isIntegral := RingHom.IsIntegral.of_finite (by
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom]; exact RingHom.Finite.id _)
  etale w hw := by
    have halg : (AlgHom.id k X.A).toRingHom.toAlgebra = Algebra.id X.A :=
      Algebra.algebra_ext _ _ (fun _ => rfl)
    rw [halg, Ideal.ramificationIdx_eq_one w X.A, one_mul]
    rfl

lemma ramificationIdx_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDedekindDomain B] (g : A →+* B) (f : B →+* C) [IsDomain C]
    (hf : Function.Injective f) (w : Ideal C) :
    (letI := (f.comp g).toAlgebra; w.ramificationIdx A) =
      (letI := g.toAlgebra; (w.comap f).ramificationIdx A) *
        (letI := f.toAlgebra; w.ramificationIdx B) := by
  letI := g.toAlgebra
  letI := f.toAlgebra
  letI := (f.comp g).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : (w.comap f).LiesOver (w.comap f) := ⟨rfl⟩
  haveI : w.LiesOver (w.comap f) := ⟨rfl⟩
  haveI : Module.IsTorsionFree B C := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hf
  exact Ideal.ramificationIdx_tower (R := A) (S := B) (T := C) (w.comap f) w

/-- **Composition of finite étale morphisms.** -/
def Hom.comp {Z Y C : AffOrbicurve k} (φ : Hom Z Y) (ψ : Hom Y C) : Hom Z C where
  f := φ.f.comp ψ.f
  injective := φ.injective.comp ψ.injective
  isIntegral := RingHom.IsIntegral.trans ψ.f.toRingHom φ.f.toRingHom ψ.isIntegral φ.isIntegral
  etale w hw := by
    have h1 := ramificationIdx_comp ψ.f.toRingHom φ.f.toRingHom φ.injective w
    have hq : (w.comap φ.f).IsMaximal := by
      letI := φ.f.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral Y.A Z.A := ⟨φ.isIntegral⟩
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal w
    rw [show (φ.f.comp ψ.f).toRingHom = φ.f.toRingHom.comp ψ.f.toRingHom from rfl, h1, mul_assoc,
      φ.etale w hw]
    exact ψ.etale _ hq

@[simp] lemma Hom.comp_f {Z Y C : AffOrbicurve k} (φ : Hom Z Y) (ψ : Hom Y C) :
    (φ.comp ψ).f = φ.f.comp ψ.f := rfl

@[simp] lemma Hom.id_f (X : AffOrbicurve k) : (Hom.id X).f = AlgHom.id k X.A := rfl

/-- **Isomorphisms** of affine orbicurves. -/
structure Iso (X Y : AffOrbicurve k) where
  /-- The morphism `X → Y`. -/
  hom : Hom X Y
  /-- The morphism `Y → X`. -/
  inv : Hom Y X
  hom_inv : hom.f.comp inv.f = AlgHom.id k X.A
  inv_hom : inv.f.comp hom.f = AlgHom.id k Y.A

/-- The inverse isomorphism. -/
def Iso.symm {X Y : AffOrbicurve k} (e : Iso X Y) : Iso Y X := ⟨e.inv, e.hom, e.inv_hom, e.hom_inv⟩

end Hom

section Core

lemma LocBar.self (X : AffOrbicurve k) : LocBar X X := ⟨X, ⟨Hom.id X⟩, ⟨Hom.id X⟩⟩

lemma LocBar.of_hom {X Y : AffOrbicurve k} (φ : Hom Y X) : LocBar X Y := ⟨Y, ⟨φ⟩, ⟨Hom.id Y⟩⟩

lemma LocBar.trans_hom {A B Y : AffOrbicurve k} (φ : Hom A B) (h : LocBar A Y) : LocBar B Y := by
  obtain ⟨Z, ⟨f⟩, ⟨g⟩⟩ := h
  exact ⟨Z, ⟨f.comp φ⟩, ⟨g⟩⟩

/-- If `A → B` is finite étale, the `k`-core of `B` is the `k`-core of `A`. -/
theorem IsCoreOf.of_hom {A B C : AffOrbicurve k} (φ : Hom A B) (h : IsCoreOf B C) :
    IsCoreOf A C := by
  refine ⟨?_, fun Y hY => h.2 Y (hY.trans_hom φ)⟩
  obtain ⟨ψ, -⟩ := h.2 A (LocBar.of_hom φ)
  exact ⟨A, ⟨Hom.id A⟩, ψ⟩

/-- If `A → B` is finite étale and every finite étale `Z → B` is dominated by a finite étale
`Z' → A` (e.g. by a component of `Z ×_B A`), the `k`-core of `A` is the `k`-core of `B`. -/
theorem IsCoreOf.of_hom_of_pullback {A B C : AffOrbicurve k} (φ : Hom A B)
    (hpb : ∀ Z : AffOrbicurve k, Hom Z B → ∃ Z' : AffOrbicurve k,
      Nonempty (Hom Z' Z) ∧ Nonempty (Hom Z' A))
    (h : IsCoreOf A C) : IsCoreOf B C := by
  refine ⟨h.1.trans_hom φ, fun Y hY => h.2 Y ?_⟩
  obtain ⟨Z, ⟨f⟩, ⟨g⟩⟩ := hY
  obtain ⟨Z', ⟨p⟩, ⟨q⟩⟩ := hpb Z f
  exact ⟨Z', ⟨q⟩, ⟨p.comp g⟩⟩

/-- Cores are invariant under isomorphisms of the core. -/
theorem IsCoreOf.congr_right {X C C' : AffOrbicurve k} (e : Iso C C') (h : IsCoreOf X C) :
    IsCoreOf X C' := by
  refine ⟨?_, fun Y hY => ?_⟩
  · obtain ⟨Z, f, ⟨g⟩⟩ := h.1
    exact ⟨Z, f, ⟨g.comp e.hom⟩⟩
  · obtain ⟨⟨ψ⟩, hsub⟩ := h.2 Y hY
    refine ⟨⟨ψ.comp e.hom⟩, ⟨fun a b => ?_⟩⟩
    have := hsub.elim (a.comp e.inv) (b.comp e.inv)
    apply Hom.ext
    have h2 := congrArg (fun φ : Hom Y C => (Hom.f φ).comp e.hom.f) this
    simpa only [Hom.comp_f, AlgHom.comp_assoc, e.inv_hom, AlgHom.comp_id] using h2

/-- Cores are invariant under isomorphisms of the curve. -/
theorem IsCoreOf.congr_left {X X' C : AffOrbicurve k} (e : Iso X X') (h : IsCoreOf X C) :
    IsCoreOf X' C := by
  refine ⟨h.1.trans_hom e.hom, fun Y hY => h.2 Y (hY.trans_hom e.inv)⟩

end Core

end AffOrbicurve
