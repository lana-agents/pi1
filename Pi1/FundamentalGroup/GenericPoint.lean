/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.FundamentalGroup.DenseOpen
public import Pi1.FundamentalGroup.Point

/-!
# The Galois action through a field-valued point

Let `F` be a field, `Ω` a separably closed Galois extension of `F` and `j : Spec F ⟶ X` a
morphism of schemes (e.g. the generic point of an integral scheme with function field `F`). Then
`Gal(Ω / F) = π₁ᵉᵗ(Spec F)` (`FiniteEtale.mulEquivAutFiber`) acts on the fibre functor of `X` at
`η = (Spec Ω ⟶ Spec F ⟶ X)` through `fundamentalGroupMap j`
(`AlgebraicGeometry.FiniteEtale.galoisAction`), and the action is the intrinsic one: `g` acts on
a point `x : Spec Ω ⟶ A` of a finite étale `X`-scheme `A` by precomposition with `Spec g`
(`FiniteEtale.galoisAction_hom_app_left`). This action is natural in `X`
(`FiniteEtale.fundamentalGroupMap_galoisAction`).

If `X = Spec R` is affine, `R → F` injective and `R` integrally closed in `F`, the relative
normalization of `Spec R` in `Spec F` is trivial, hence `galoisAction` is surjective
(`FiniteEtale.galoisAction_surjective`).

We also record the pointwise description of `pullbackFiberIso`
(`FiniteEtale.pullbackFiberIso_hom_app_left`) and an affine-target criterion for trivial
relative normalizations (`Scheme.Hom.isIso_fromNormalization_of_isAffine`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- **The relative normalization over an affine target is trivial** if `Γ(Y, ⊤) → Γ(X, ⊤)` is
injective and every element of `Γ(X, ⊤)` integral over `Γ(Y, ⊤)` comes from `Γ(Y, ⊤)`. -/
theorem isIso_fromNormalization_of_isAffine [IsAffine Y]
    (hinj : letI := (f.app ⊤).hom.toAlgebra
      Function.Injective (algebraMap Γ(Y, ⊤) Γ(X, f ⁻¹ᵁ ⊤)))
    (hbot : letI := (f.app ⊤).hom.toAlgebra
      integralClosure Γ(Y, ⊤) Γ(X, f ⁻¹ᵁ ⊤) = ⊥) :
    IsIso f.fromNormalization := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := .isomorphisms _)
    fun x ↦ ⟨⊤, trivial, (isIso_morphismRestrict_iff_isIso_app _ (isAffineOpen_top Y)).mpr ?_⟩
  letI := (f.app ⊤).hom.toAlgebra
  rw [f.fromNormalization_app (isAffineOpen_top Y)]
  suffices IsIso (CommRingCat.ofHom (algebraMap Γ(Y, ⊤)
      (integralClosure Γ(Y, ⊤) Γ(X, f ⁻¹ᵁ ⊤)))) from inferInstance
  have hbij : Function.Bijective
      (algebraMap Γ(Y, ⊤) (integralClosure Γ(Y, ⊤) Γ(X, f ⁻¹ᵁ ⊤))) := by
    refine ⟨fun a b hab ↦ hinj (congrArg Subtype.val hab), fun y ↦ ?_⟩
    have hy : (y : Γ(X, f ⁻¹ᵁ ⊤)) ∈ (⊥ : Subalgebra Γ(Y, ⊤) Γ(X, f ⁻¹ᵁ ⊤)) := hbot ▸ y.2
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hy
    exact ⟨a, Subtype.ext ha⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

end Scheme.Hom

/-- **The normalization of `Spec R` in `Spec S` is trivial** if `R → S` is injective and `R` is
integrally closed in `S`. -/
theorem isIso_fromNormalization_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [QuasiCompact (Spec.map φ)] [QuasiSeparated (Spec.map φ)]
    (hinj : Function.Injective φ)
    (hint : ∀ s : S, (letI := φ.hom.toAlgebra; _root_.IsIntegral R s) → s ∈ Set.range φ) :
    IsIso (Spec.map φ).fromNormalization := by
  have hnat := Scheme.ΓSpecIso_naturality φ
  refine (Spec.map φ).isIso_fromNormalization_of_isAffine ?_ ?_
  · letI := ((Spec.map φ).app ⊤).hom.toAlgebra
    intro a b hab
    have h1 : ((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso S).hom) a =
        ((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso S).hom) b := by
      simp only [CommRingCat.comp_apply]
      exact congrArg _ hab
    rw [hnat, CommRingCat.comp_apply, CommRingCat.comp_apply] at h1
    exact (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective (hinj h1)
  · letI := ((Spec.map φ).app ⊤).hom.toAlgebra
    letI := φ.hom.toAlgebra
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    have hx' : _root_.IsIntegral R ((Scheme.ΓSpecIso S).hom x) :=
      IsIntegral.map_of_comp_eq (S := Γ(Spec S, Spec.map φ ⁻¹ᵁ ⊤))
        (Scheme.ΓSpecIso R).hom.hom (Scheme.ΓSpecIso S).hom.hom
        (congrArg CommRingCat.Hom.hom hnat).symm hx
    obtain ⟨r, hr⟩ := hint _ hx'
    refine Algebra.mem_bot.mpr ⟨(Scheme.ΓSpecIso R).inv r, ?_⟩
    apply (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv.injective
    change ((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso S).hom) ((Scheme.ΓSpecIso R).inv r) = _
    rw [hnat, CommRingCat.comp_apply]
    have hr' : (Scheme.ΓSpecIso R).hom ((Scheme.ΓSpecIso R).inv r) = r :=
      Iso.inv_hom_id_apply _ _
    rw [hr', hr]
    rfl

namespace FiniteEtale

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **`pullbackFiberIso` on points**: a point `Spec Ω ⟶ f^* A` over `p` is sent to its
composite with the projection `f^* A ⟶ A`. -/
lemma pullbackFiberIso_hom_app_left (f : Y ⟶ X) {p : Spec (.of Ω) ⟶ Y} {η : Spec (.of Ω) ⟶ X}
    (h : p ≫ f = η) (A : FiniteEtale X) (x : (fiber p).obj ((pullback f).obj A)) :
    (fiberObjEquivHom η A ((pullbackFiberIso f h).hom.app A x)).left =
      (fiberObjEquivHom p _ x).left ≫ Limits.pullback.fst A.hom f := by
  obtain ⟨x, rfl⟩ := (fiberObjEquivHom p _).symm.surjective x
  rw [Equiv.apply_symm_apply]
  have hw : (x.left ≫ Limits.pullback.fst A.hom f) ≫ A.hom = η := by
    have h1 : x.left ≫ Limits.pullback.snd A.hom f = p := Over.w x
    have hc : Limits.pullback.fst A.hom f ≫ A.hom = Limits.pullback.snd A.hom f ≫ f :=
      Limits.pullback.condition
    exact (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hc).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) h1).trans h)))
  suffices (pullbackFiberIso f h).hom.app A ((fiberObjEquivHom p _).symm x) =
      (fiberObjEquivHom η A).symm (Over.homMk (x.left ≫ Limits.pullback.fst A.hom f) hw) by
    rw [this, Equiv.apply_symm_apply]
    rfl
  rw [pullbackFiberIso_hom_app, fiberObjEquivHom_symm_apply, fiberObjEquivHom_symm_apply]
  change ((MorphismProperty.Over.pullbackComp p f η h.symm).inv.app A).left
    (Limits.pullback.lift x.left (𝟙 _) _ _) = _
  have key (x' : Spec (.of Ω) ⟶ Limits.pullback A.hom f)
      (hx' : x' ≫ Limits.pullback.snd A.hom f = p) :
      Limits.pullback.lift x' (𝟙 _) (by simp [hx']) ≫
        (pullbackLeftPullbackSndIso A.hom f p).hom ≫
          Limits.pullback.map A.hom (p ≫ f) A.hom η (𝟙 _) (𝟙 _) (𝟙 _) (by simp)
            (by simp [h]) =
        Limits.pullback.lift (x' ≫ Limits.pullback.fst A.hom f) (𝟙 _)
          (by simp [Limits.pullback.condition, reassoc_of% hx', h]) := by
    apply Limits.pullback.hom_ext <;> simp
  have hcomp : Limits.pullback.lift x.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w x) ≫
      ((MorphismProperty.Over.pullbackComp p f η h.symm).inv.app A).left =
      Limits.pullback.lift (x.left ≫ Limits.pullback.fst A.hom f) (𝟙 _)
        (by rw [Category.id_comp]; exact hw) := by
    simp only [MorphismProperty.Over.pullbackComp_inv_app_left]
    exact key x.left (Over.w x)
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans congr($hcomp _)

variable (F : Type u) [Field F] [Algebra F Ω]

omit [IsSepClosed Ω] in
/-- The morphism `Spec g : Spec Ω ⟶ Spec Ω` over `Spec F` for `g ∈ Gal(Ω / F)`. -/
lemma specMap_algEquiv_comp (g : Ω ≃ₐ[F] Ω) :
    Spec.map (CommRingCat.ofHom (g : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap F Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AlgEquiv.toAlgHom_toRingHom,
    AlgHom.comp_algebraMap]

variable [IsGalois F Ω]

/-- **The Galois action through a field-valued point** `j : Spec F ⟶ X`: the composite
`Gal(Ω / F) ≅ π₁ᵉᵗ(Spec F) → π₁ᵉᵗ(X, η)`, where `η = Spec Ω ⟶ Spec F ⟶ X`. -/
noncomputable def galoisAction (j : Spec (.of F) ⟶ X) {η : Spec (.of Ω) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η) :
    (Ω ≃ₐ[F] Ω) →* π₁ᵉᵗ(η) :=
  (fundamentalGroupMap j h : π₁ᵉᵗ(_) →* π₁ᵉᵗ(η)).comp (mulEquivAutFiber F Ω).toMonoidHom

lemma continuous_galoisAction (j : Spec (.of F) ⟶ X) {η : Spec (.of Ω) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η) :
    Continuous (galoisAction F j h) :=
  (fundamentalGroupMap j h).continuous.comp (isHomeomorph_mulEquivAutFiber F Ω).continuous

/-- **The Galois action is the intrinsic one**: `g ∈ Gal(Ω / F)` acts on a point
`x : Spec Ω ⟶ A` of a finite étale `X`-scheme by precomposition with `Spec g`. -/
lemma galoisAction_hom_app_left (j : Spec (.of F) ⟶ X) {η : Spec (.of Ω) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η) (g : Ω ≃ₐ[F] Ω)
    (A : FiniteEtale X) (x : (fiber η).obj A) :
    (fiberObjEquivHom η A ((galoisAction F j h g).hom.app A x)).left =
      Spec.map (CommRingCat.ofHom (g : Ω →+* Ω)) ≫ (fiberObjEquivHom η A x).left := by
  let e := pullbackFiberIso j h
  obtain ⟨y, rfl⟩ : ∃ y, e.hom.app A y = x :=
    ⟨e.inv.app A x, FintypeCat.inv_hom_id_apply (e.app A) x⟩
  change (fiberObjEquivHom η A (fiberAutMap e (mulEquivAutFiber F Ω g) |>.hom.app A
    (e.hom.app A y))).left = _
  rw [fiberAutMap_hom_app_apply]
  have hy : e.inv.app A (e.hom.app A y) = y := FintypeCat.hom_inv_id_apply (e.app A) y
  rw [hy, pullbackFiberIso_hom_app_left, pullbackFiberIso_hom_app_left, mulEquivAutFiber,
    toAutMulEquiv_apply, toAut_hom_app_apply, algEquiv_smul_fiber_def, Equiv.apply_symm_apply,
    algEquiv_smul_hom]
  exact Category.assoc _ _ _

/-- **Naturality of the Galois action** along `f : Y ⟶ X`. -/
lemma fundamentalGroupMap_galoisAction (j : Spec (.of F) ⟶ Y) (f : Y ⟶ X)
    {p : Spec (.of Ω) ⟶ Y} {η : Spec (.of Ω) ⟶ X}
    (h₁ : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = p) (h₂ : p ≫ f = η)
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j ≫ f = η) (g : Ω ≃ₐ[F] Ω) :
    fundamentalGroupMap f h₂ (galoisAction F j h₁ g) = galoisAction F (j ≫ f) h g := by
  simp only [galoisAction, MonoidHom.comp_apply, fundamentalGroupMap_comp j f h₁ h₂ h]
  rfl

omit [IsSepClosed Ω] [IsGalois F Ω] in
lemma specMap_algebraMap_comp (R : Type u) [CommRing R] [Algebra R F] [Algebra R Ω]
    [IsScalarTower R F Ω] :
    Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R F)) =
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- **Surjectivity from the generic point.** If `R → F` is injective and `R` is integrally
closed in `F`, then `Gal(Ω / F) → π₁ᵉᵗ(Spec R)` is surjective. -/
theorem galoisAction_surjective (R : Type u) [CommRing R] [IsDomain R] [Algebra R F]
    [Algebra R Ω] [IsScalarTower R F Ω] (hinj : Function.Injective (algebraMap R F))
    (hint : ∀ x : F, _root_.IsIntegral R x → x ∈ Set.range (algebraMap R F)) :
    Function.Surjective (galoisAction F (Spec.map (CommRingCat.ofHom (algebraMap R F)))
      (η := Spec.map (CommRingCat.ofHom (algebraMap R Ω))) (specMap_algebraMap_comp F R)) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap R F))).fromNormalization :=
    -- `IsIntegral` only depends on `algebraMap`, which agrees for the two algebra structures
    isIso_fromNormalization_specMap _ hinj fun s hs ↦
      hint s (show (algebraMap R F).IsIntegralElem s from hs)
  have hj := fundamentalGroupMap_surjective_of_isIso_fromNormalization
    (Spec.map (CommRingCat.ofHom (algebraMap R F))) (specMap_algebraMap_comp F R (Ω := Ω))
  simp only [galoisAction, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, MonoidHom.coe_coe]
  exact hj.comp (mulEquivAutFiber F Ω).surjective

/-- **Elements of `π₁ᵉᵗ(η)` are determined by their action on points** `Spec Ω ⟶ A`. -/
lemma ext_of_hom_app_left {η : Spec (.of Ω) ⟶ X} {γ₁ γ₂ : π₁ᵉᵗ(η)}
    (h : ∀ (A : FiniteEtale X) (x : (fiber η).obj A),
      (fiberObjEquivHom η A (γ₁.hom.app A x)).left =
        (fiberObjEquivHom η A (γ₂.hom.app A x)).left) :
    γ₁ = γ₂ :=
  Iso.ext (NatTrans.ext (funext fun A => FintypeCat.hom_ext _ _ fun x =>
    (fiberObjEquivHom η A).injective (Over.OverMorphism.ext (h A x))))

/-- **The Galois action only depends on the automorphism of `Ω`**: for two fields `F`, `F'`
with points `Spec F ⟶ X`, `Spec F' ⟶ X` inducing the same geometric point `η`, automorphisms
`g` of `Ω / F` and `g'` of `Ω / F'` with the same underlying map act in the same way. -/
lemma galoisAction_eq_of_apply_eq {F' : Type u} [Field F'] [Algebra F' Ω] [IsGalois F' Ω]
    (j : Spec (.of F) ⟶ X) (j' : Spec (.of F') ⟶ X) {η : Spec (.of Ω) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η)
    (h' : Spec.map (CommRingCat.ofHom (algebraMap F' Ω)) ≫ j' = η)
    (g : Ω ≃ₐ[F] Ω) (g' : Ω ≃ₐ[F'] Ω) (hg : ∀ x, g x = g' x) :
    galoisAction F j h g = galoisAction F' j' h' g' := by
  refine ext_of_hom_app_left fun A x => ?_
  rw [galoisAction_hom_app_left, galoisAction_hom_app_left]
  have : (g : Ω →+* Ω) = (g' : Ω →+* Ω) := RingHom.ext hg
  rw [this]

lemma galoisAction_congr {j j' : Spec (.of F) ⟶ X} (hj : j = j') {η : Spec (.of Ω) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η)
    (h' : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j' = η) :
    galoisAction F j h = galoisAction F j' h' := by
  subst hj
  rfl

end FiniteEtale

end AlgebraicGeometry
