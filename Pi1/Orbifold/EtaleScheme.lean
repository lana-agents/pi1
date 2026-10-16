/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.FundamentalGroup.BaseChangeInjective
public import Pi1.Orbifold.EtaleMathlib

/-!
# The algebraic and the scheme-theoretic `π₁ᵉᵗ` of an affine scheme

For a ring `R` and a separably closed field `Ω` with `R → Ω`, the functor
`S ↦ Spec S` is an equivalence between `(CommAlgCat.FiniteEtale R)ᵒᵖ` and the category
`FiniteEtale (Spec R)` of finite étale `Spec R`-schemes (`FiniteEtale.specFunctor`), and it
identifies Mathlib's fibre functor `S ↦ (S →ₐ[R] Ω)` with the fibre functor of
`FiniteEtale (Spec R)` at the geometric point `ξ = Spec Ω ⟶ Spec R`
(`FiniteEtale.specFunctorFiberIso`). Hence

* `AlgebraicGeometry.FiniteEtale.autFiberSpecEquiv :
    π₁ᵉᵗ(ξ) ≃ₜ* Aut (CommAlgCat.FiniteEtale.fiber R Ω)`, and
* `AlgebraicGeometry.FiniteEtale.etalePi1SpecEquiv : π₁ᵉᵗ(ξ) ≃ₜ* etalePi1 R PUnit Ω`,

so pi1's algebraic model `etalePi1 R PUnit Ω` (`Pi1.Orbifold`), in which the comparison with
Galois groups (`Pi1.Orbifold.GaloisData.equivPi1`) is proved, is the étale fundamental group of
the scheme `Spec R`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

variable (R : Type u) [CommRing R]

instance (S : CommAlgCat.FiniteEtale.{u} R) : Algebra.FiniteEtale R S := ⟨⟩

/-- `S ↦ Spec S`, from finite étale `R`-algebras to finite étale `Spec R`-schemes. -/
noncomputable def specFunctor : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ⥤ FiniteEtale (Spec (.of R)) where
  obj S := ofAlgebra R S.unop
  map {S T} f := MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext r
      exact f.unop.hom.hom.commutes r) trivial
  map_id S := by
    apply MorphismProperty.Over.Hom.ext
    simp
    rfl
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    change _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl

@[simp]
lemma specFunctor_obj_left (S : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    ((specFunctor R).obj S).left = Spec (.of S.unop) := rfl

@[simp]
lemma specFunctor_obj_hom (S : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    ((specFunctor R).obj S).hom = Spec.map (CommRingCat.ofHom (algebraMap R S.unop)) := rfl

@[simp]
lemma specFunctor_map_left {S T : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ} (f : S ⟶ T) :
    ((specFunctor R).map f).left = Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) := rfl

/-- The `R`-algebra map `T → S` underlying a morphism `Spec S ⟶ Spec T` over `Spec R`. -/
noncomputable def specPreimage {S T : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ}
    (φ : (specFunctor R).obj S ⟶ (specFunctor R).obj T) : T.unop.obj →ₐ[R] S.unop.obj :=
  { (Spec.preimage φ.left).hom with
    commutes' r := by
      have h : φ.left ≫ Spec.map (CommRingCat.ofHom (algebraMap R T.unop)) =
          Spec.map (CommRingCat.ofHom (algebraMap R S.unop)) := φ.w.trans (Category.comp_id _)
      have h2 : Spec.map (CommRingCat.ofHom (algebraMap R T.unop) ≫ Spec.preimage φ.left) =
          Spec.map (CommRingCat.ofHom (algebraMap R S.unop)) := by
        rw [Spec.map_comp, Spec.map_preimage]
        exact h
      exact congr($(Spec.map_injective h2) r) }

lemma spec_map_specPreimage {S T : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ}
    (φ : (specFunctor R).obj S ⟶ (specFunctor R).obj T) :
    Spec.map (CommRingCat.ofHom (specPreimage R φ).toRingHom) = φ.left := by
  conv_rhs => rw [← Spec.map_preimage φ.left]
  rfl

/-- `Spec` is fully faithful on finite étale algebras. -/
noncomputable def specFunctorFullyFaithful : (specFunctor R).FullyFaithful where
  preimage {S T} φ := (CommAlgCat.FiniteEtale.ofHom (specPreimage R φ) :
    CommAlgCat.FiniteEtale.of R T.unop ⟶ CommAlgCat.FiniteEtale.of R S.unop).op
  map_preimage φ := by
    apply MorphismProperty.Over.Hom.ext
    exact spec_map_specPreimage R φ
  preimage_map f := by
    apply Quiver.Hom.unop_inj
    ext x
    have h := spec_map_specPreimage R ((specFunctor R).map f)
    rw [specFunctor_map_left] at h
    exact congr($(Spec.map_injective h) x)

instance : (specFunctor R).Full := (specFunctorFullyFaithful R).full
instance : (specFunctor R).Faithful := (specFunctorFullyFaithful R).faithful

instance : (specFunctor R).EssSurj where
  mem_essImage A := by
    letI : Algebra R Γ(A.left, ⊤) := (ringHomΓ A).hom.toAlgebra
    haveI : Algebra.FiniteEtale R Γ(A.left, ⊤) :=
      (RingHom.finiteEtale_algebraMap_iff).mp (finiteEtale_ringHomΓ A)
    refine ⟨.op (CommAlgCat.FiniteEtale.of R Γ(A.left, ⊤)), ⟨?_⟩⟩
    refine MorphismProperty.Over.isoMk A.left.isoSpec.symm ?_
    change A.left.isoSpec.inv ≫ A.hom = Spec.map (ringHomΓ A)
    exact (Iso.inv_comp_eq _).mpr (hom_eq_isoSpec_hom_comp A)

instance : (specFunctor R).IsEquivalence where

variable (Ω : Type u) [Field Ω] [Algebra R Ω] [IsSepClosed Ω]

/-- The geometric point `Spec Ω ⟶ Spec R`. -/
noncomputable abbrev specPoint : Spec (.of Ω) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R Ω))

/-- Points of `Spec S` over `Spec Ω ⟶ Spec R` are `R`-algebra maps `S → Ω`. -/
noncomputable def homSpecEquivAlgHom (S : CommAlgCat.FiniteEtale.{u} R) :
    (Over.mk (specPoint R Ω) ⟶ ((specFunctor R).obj (.op S)).toComma) ≃ (S →ₐ[R] Ω) where
  toFun x :=
    { (Spec.preimage x.left).hom with
      commutes' r := by
        have h : x.left ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
            Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := Over.w x
        have h2 : Spec.map (CommRingCat.ofHom (algebraMap R S) ≫ Spec.preimage x.left) =
            Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
          rw [Spec.map_comp, Spec.map_preimage]
          exact h
        exact congr($(Spec.map_injective h2) r) }
  invFun f := Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact f.commutes r)
  left_inv x := by
    ext1
    change Spec.map (CommRingCat.ofHom (Spec.preimage x.left).hom) = x.left
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  right_inv f := by
    ext s
    change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom))).hom s = f s
    rw [Spec.preimage_map]
    rfl

omit [IsSepClosed Ω] in
lemma homSpecEquivAlgHom_symm_comp {S T : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ} (f : S ⟶ T)
    (g : S.unop →ₐ[R] Ω) :
    (homSpecEquivAlgHom R Ω T.unop).symm (g.comp f.unop.hom.hom) =
      (homSpecEquivAlgHom R Ω S.unop).symm g ≫ ((specFunctor R).map f).toCommaMorphism := by
  ext1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The fibre functor of `FiniteEtale (Spec R)` at `Spec Ω ⟶ Spec R`, restricted along
`specFunctor`, is Mathlib's fibre functor `S ↦ (S →ₐ[R] Ω)`. -/
noncomputable def specFunctorFiberIso :
    specFunctor R ⋙ fiber (specPoint R Ω) ⋙ FintypeCat.incl ≅
      CommAlgCat.FiniteEtale.fiber.{u} R Ω ⋙ FintypeCat.incl :=
  NatIso.ofComponents
    (fun S ↦ equivEquivIso ((fiberObjEquivHom (specPoint R Ω) _).trans
      (homSpecEquivAlgHom R Ω S.unop)))
    fun {S T} f ↦ by
      ext x
      change (homSpecEquivAlgHom R Ω T.unop) (fiberObjEquivHom _ _
        ((fiber (specPoint R Ω)).map ((specFunctor R).map f) x)) =
        ((homSpecEquivAlgHom R Ω S.unop) (fiberObjEquivHom _ _ x)).comp f.unop.hom.hom
      rw [← fiberObjEquivHom_naturality, Equiv.apply_eq_iff_eq_symm_apply,
        homSpecEquivAlgHom_symm_comp, Equiv.symm_apply_apply]

/-- **The étale fundamental group of `Spec R` is the automorphism group of Mathlib's fibre
functor on finite étale `R`-algebras.** -/
noncomputable def autFiberSpecEquiv :
    π₁ᵉᵗ(specPoint R Ω) ≃ₜ* Aut (CommAlgCat.FiniteEtale.fiber.{u} R Ω) :=
  haveI : CompactSpace (Pi1.Orbifold.FibreAut (fiber (specPoint R Ω) ⋙ FintypeCat.incl)) :=
    Pi1.Orbifold.FibreAut.compactSpace_of_finite _
  (Pi1.Orbifold.FibreAut.equivAut _).symm.trans
    ((Pi1.Orbifold.FibreAut.equivOfIsEquivalence (specFunctor R)
      (specFunctorFiberIso R Ω)).trans (Pi1.Orbifold.FibreAut.equivAut _))

open scoped Pi1.Orbifold.TrivialAction in
/-- **The étale fundamental group of `Spec R`** at `Spec Ω ⟶ Spec R` is pi1's algebraic model
`etalePi1 R PUnit Ω`. -/
noncomputable def etalePi1SpecEquiv :
    π₁ᵉᵗ(specPoint R Ω) ≃ₜ* Pi1.Orbifold.etalePi1 R PUnit.{u + 1} Ω :=
  (autFiberSpecEquiv R Ω).trans (Pi1.Orbifold.etalePi1EquivAutFiber R Ω).symm

end AlgebraicGeometry.FiniteEtale
