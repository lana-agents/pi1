/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Trivial relative normalizations

For a quasi-compact quasi-separated morphism `f : X ⟶ Y`, the relative normalization
`f.fromNormalization : f.normalization ⟶ Y` is an isomorphism as soon as, for every affine open
`U ⊆ Y`, the ring `Γ(Y, U)` maps injectively onto its integral closure in `Γ(X, f⁻¹ U)`
(`AlgebraicGeometry.Scheme.Hom.isIso_fromNormalization_of_forall`). The typical case is a dense
open immersion into a normal scheme.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

section Trivial

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- **The relative normalization is trivial** if, over every affine open `U` of the target,
`Γ(Y, U) → Γ(X, f⁻¹ U)` is injective and every element of `Γ(X, f⁻¹ U)` integral over `Γ(Y, U)`
comes from `Γ(Y, U)`. -/
theorem isIso_fromNormalization_of_forall
    (h : ∀ U : Y.affineOpens, letI := (f.app U).hom.toAlgebra
      Function.Injective (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) ∧
        integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U) = ⊥) :
    IsIso f.fromNormalization := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := .isomorphisms _)
    fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  refine ⟨U, hxU, (isIso_morphismRestrict_iff_isIso_app _ hU).mpr ?_⟩
  letI := (f.app U).hom.toAlgebra
  obtain ⟨hinj, hbot⟩ := h ⟨U, hU⟩
  rw [f.fromNormalization_app hU]
  suffices IsIso (CommRingCat.ofHom (algebraMap Γ(Y, U)
      (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)))) from inferInstance
  have hbij : Function.Bijective (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))) := by
    refine ⟨fun a b hab ↦ hinj (congrArg Subtype.val hab), fun y ↦ ?_⟩
    have hy : (y : Γ(X, f ⁻¹ᵁ U)) ∈ (⊥ : Subalgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := hbot ▸ y.2
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hy
    exact ⟨a, Subtype.ext ha⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

end Trivial

section Iso

variable {W' W T : Scheme.{u}} (e : W' ≅ W) (g : W ⟶ T) [QuasiCompact g] [QuasiSeparated g]

/-- The normalization of `T` in `W` does not change when `W` is replaced by an isomorphic
scheme: the comparison map `(e.hom ≫ g).normalization ⟶ g.normalization`. -/
noncomputable def normalizationIsoOfIso : (e.hom ≫ g).normalization ≅ g.normalization where
  hom := (e.hom ≫ g).normalizationDesc (e.hom ≫ g.toNormalization) g.fromNormalization
    (by simp)
  inv := g.normalizationDesc (e.inv ≫ (e.hom ≫ g).toNormalization) (e.hom ≫ g).fromNormalization
    (by simp)
  hom_inv_id := by
    refine normalization.hom_ext (e.hom ≫ g) _ _ (e.hom ≫ g).fromNormalization ?_ (by simp)
      (Category.id_comp _)
    simp
  inv_hom_id := by
    refine normalization.hom_ext g _ _ g.fromNormalization ?_ (by simp) (Category.id_comp _)
    simp

@[reassoc (attr := simp)]
lemma normalizationIsoOfIso_hom_fromNormalization :
    (normalizationIsoOfIso e g).hom ≫ g.fromNormalization = (e.hom ≫ g).fromNormalization :=
  (e.hom ≫ g).normalizationDesc_comp _ _ (by simp)

omit [QuasiCompact g] [QuasiSeparated g] in
/-- Transport triviality of the normalization along an equality of morphisms (the instance
arguments may differ). -/
lemma isIso_fromNormalization_of_eq {g h : W ⟶ T} (H : g = h) [QuasiCompact g]
    [QuasiSeparated g] [QuasiCompact h] [QuasiSeparated h] [IsIso g.fromNormalization] :
    IsIso h.fromNormalization := by
  subst H
  assumption

/-- Triviality of the relative normalization is invariant under isomorphisms of the source. -/
lemma isIso_fromNormalization_iso_comp [IsIso g.fromNormalization] :
    IsIso (e.hom ≫ g).fromNormalization := by
  rw [← normalizationIsoOfIso_hom_fromNormalization]
  infer_instance

end Iso

section Smooth

variable {U X Y : Scheme.{u}} (j : U ⟶ X) [QuasiCompact j] [QuasiSeparated j] (f : Y ⟶ X)

/-- If the normalization of `X` in `U` is trivial, so is the normalization of `Y` in `U ×_X Y`
for any smooth (e.g. étale) `Y ⟶ X`: normalization commutes with smooth base change. -/
theorem isIso_fromNormalization_pullback_snd [Smooth f] [IsIso j.fromNormalization] :
    IsIso (pullback.snd j f).fromNormalization := by
  rw [← j.normalizationPullback_snd f]
  infer_instance

/-- `isIso_fromNormalization_pullback_snd` with the factors of the fibre product swapped. -/
theorem isIso_fromNormalization_pullback_fst [Smooth f] [IsIso j.fromNormalization] :
    IsIso (pullback.fst f j).fromNormalization := by
  have := isIso_fromNormalization_pullback_snd j f
  have := isIso_fromNormalization_iso_comp (pullbackSymmetry f j) (pullback.snd j f)
  exact isIso_fromNormalization_of_eq (pullbackSymmetry_hom_comp_snd f j)

end Smooth

section Integral

variable {W T X : Scheme.{u}} (a : W ⟶ T) (b : T ⟶ X) [IsIntegralHom b]
  [QuasiCompact a] [QuasiSeparated a]

/-- The map `(a ≫ b).normalization ⟶ T` given by the universal property, for `b` integral. -/
noncomputable abbrev normalizationCompDesc : (a ≫ b).normalization ⟶ T :=
  (a ≫ b).normalizationDesc a b rfl

/-- **Normalization over an integral morphism.** Let `a : W ⟶ T` with trivial normalization
(`T` is "normal relative to `W`") and `W` reduced, and `b : T ⟶ X` integral. Then the
normalization of `X` in `W` (along `a ≫ b`) is `T`. -/
theorem isIso_normalizationCompDesc [IsReduced W] [IsIso a.fromNormalization] :
    IsIso (normalizationCompDesc a b) := by
  set g := a ≫ b with hg
  have hw : g.toNormalization ≫ g.fromNormalization = a ≫ b := g.toNormalization_fromNormalization
  let χ := normalizationCompDesc a b
  -- `ψ₀ : a.normalization ⟶ g.normalization ×_X T`, from `a = W ⟶ g.normalization ×_X T ⟶ T`.
  let ψ₀ : a.normalization ⟶ pullback g.fromNormalization b :=
    a.normalizationDesc (pullback.lift g.toNormalization a hw) (pullback.snd _ _)
      (pullback.lift_snd _ _ _).symm
  let ψ : T ⟶ g.normalization := inv a.fromNormalization ≫ ψ₀ ≫ pullback.fst _ _
  have hψ₀ : a.toNormalization ≫ ψ₀ = pullback.lift g.toNormalization a hw :=
    a.toNormalization_normalizationDesc _ _ _
  have hψ₀snd : ψ₀ ≫ pullback.snd _ _ = a.fromNormalization :=
    a.normalizationDesc_comp _ _ _
  have hχ : g.toNormalization ≫ χ = a := g.toNormalization_normalizationDesc _ _ _
  have hχb : χ ≫ b = g.fromNormalization := g.normalizationDesc_comp _ _ _
  have hψ : a ≫ ψ = g.toNormalization := by
    simp only [ψ, ← a.toNormalization_fromNormalization, Category.assoc, IsIso.hom_inv_id_assoc,
      reassoc_of% hψ₀, pullback.lift_fst]
  have hψg : ψ ≫ g.fromNormalization = b := by
    simp only [ψ, Category.assoc]
    rw [pullback.condition, reassoc_of% hψ₀snd, IsIso.inv_hom_id_assoc]
  refine ⟨ψ, ?_, ?_⟩
  · refine normalization.hom_ext g _ _ g.fromNormalization ?_ ?_ (Category.id_comp _)
    · rw [reassoc_of% hχ, hψ, Category.comp_id]
    · rw [Category.assoc, hψg, hχb]
  · -- maps `T ⟶ T`; precompose with the isomorphism `a.fromNormalization`
    rw [← cancel_epi a.fromNormalization]
    refine ext_of_isDominant_of_isSeparated b ?_ a.toNormalization ?_
    · rw [Category.comp_id, Category.assoc, Category.assoc, hχb, ← Category.assoc,
        Category.assoc, hψg]
    · rw [Category.comp_id, a.toNormalization_fromNormalization_assoc, reassoc_of% hψ, hχ,
        a.toNormalization_fromNormalization]

end Integral

end AlgebraicGeometry.Scheme.Hom
