/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étale morphisms are geometrically reduced

An étale scheme over a field is reduced (its affine pieces are étale, hence formally unramified,
algebras over the field: `Algebra.FormallyUnramified.isReduced_of_field`), so étale morphisms
are geometrically reduced (`AlgebraicGeometry.geometricallyReduced_of_etale`). Consequently a
scheme étale over a reduced locally noetherian scheme is reduced
(`AlgebraicGeometry.isReduced_of_etale`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The spectrum of an étale algebra over a field is reduced. -/
lemma isReduced_Spec_of_etale {K : Type u} [Field K] {S : CommRingCat.{u}}
    (φ : CommRingCat.of K ⟶ S) [h : Etale (Spec.map φ)] : IsReduced (Spec S) := by
  have h' : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp h
  algebraize [φ.hom]
  have : _root_.IsReduced S := Algebra.FormallyUnramified.isReduced_of_field K S
  infer_instance

/-- A scheme étale over a field is reduced. -/
lemma isReduced_of_etale_of_field {Z : Scheme.{u}} {K : Type u} [Field K]
    (p : Z ⟶ Spec (.of K)) [Etale p] : IsReduced Z := by
  have (i : Z.affineCover.I₀) : IsReduced (Z.affineCover.X i) := by
    haveI : IsOpenImmersion (Z.affineCover.f i) := Z.affineCover.map_prop i
    haveI : Etale (Z.affineCover.f i) := inferInstance
    have hE : Etale (Z.affineCover.f i ≫ p) := MorphismProperty.comp_mem @Etale _ _ ‹_› ‹_›
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.affineCover.f i ≫ p)
    have hE' : Etale (Spec.map φ) := by rw [hφ]; exact hE
    exact isReduced_Spec_of_etale (h := hE') φ
  exact IsReduced.of_openCover (𝒰 := Z.affineCover)

/-- **Étale morphisms are geometrically reduced.** -/
instance (priority := 900) geometricallyReduced_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] : GeometricallyReduced f := by
  rw [geometricallyReduced_iff]
  intro K _ y Z fst snd h
  have : Etale snd := MorphismProperty.of_isPullback h ‹_›
  exact isReduced_of_etale_of_field snd

/-- A scheme étale over a reduced locally noetherian scheme is reduced. -/
lemma isReduced_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsReduced Y]
    [IsLocallyNoetherian Y] : IsReduced X :=
  GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f

end AlgebraicGeometry
