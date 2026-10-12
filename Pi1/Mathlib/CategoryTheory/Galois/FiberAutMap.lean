/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.CategoryTheory.Conj

/-!
# Maps of automorphism groups of fibre functors

Let `F : C ⥤ FintypeCat` and `G : D ⥤ FintypeCat` be functors, `H : D ⥤ C` a functor and
`e : H ⋙ F ≅ G` a natural isomorphism. Then `σ ↦ e⁻¹ ∘ (σ ◫ H) ∘ e` is a group homomorphism
`fiberAutMap e : Aut F →* Aut G`. This is the abstract form of the map of étale fundamental groups
induced by a morphism of schemes (`H` is the pullback functor, see
`Pi1.FundamentalGroup.Functoriality`).

## Main results

* `PreGaloisCategory.fiberAutMap`: the homomorphism `Aut F →* Aut G`, with `fiberAutMap_hom_app`.
* `PreGaloisCategory.continuous_fiberAutMap`: it is continuous.
* `PreGaloisCategory.fiberAutMap_congr`, `fiberAutMap_id`, `fiberAutMap_comp`: functoriality.
* `PreGaloisCategory.FiberFunctor.ofIso`: fibre functors are stable under natural isomorphism.
* `PreGaloisCategory.toAut_comp_surjective` (SGA 1 V.6.9, Galois-theoretic part): if `H` sends
  connected objects to connected objects, `Aut F → Aut (H ⋙ F)` is surjective; consequently
  `fiberAutMap e` is surjective (`fiberAutMap_surjective`).
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅ u₆ w

namespace CategoryTheory.PreGaloisCategory

open Limits Functor

section AutMap

variable {C : Type u₁} [Category.{u₂} C] {D : Type u₃} [Category.{u₄} D]
  {E : Type u₅} [Category.{u₆} E]
  {F : C ⥤ FintypeCat.{w}} {G : D ⥤ FintypeCat.{w}} {K : E ⥤ FintypeCat.{w}}

/-- The homomorphism `Aut F →* Aut G` induced by `H : D ⥤ C` and `e : H ⋙ F ≅ G`:
whiskering with `H`, followed by conjugation with `e`. -/
noncomputable def fiberAutMap {H : D ⥤ C} (e : H ⋙ F ≅ G) : Aut F →* Aut G :=
  e.conjAut.toMonoidHom.comp (((whiskeringLeft _ _ _).obj H).mapAut F)

lemma fiberAutMap_hom_app {H : D ⥤ C} (e : H ⋙ F ≅ G) (σ : Aut F) (A : D) :
    (fiberAutMap e σ).hom.app A = e.inv.app A ≫ σ.hom.app (H.obj A) ≫ e.hom.app A := by
  simp [fiberAutMap, Iso.conj_apply]
  rfl

lemma fiberAutMap_hom_app_apply {H : D ⥤ C} (e : H ⋙ F ≅ G) (σ : Aut F) (A : D) (x : G.obj A) :
    (fiberAutMap e σ).hom.app A x = e.hom.app A (σ.hom.app (H.obj A) (e.inv.app A x)) := by
  rw [fiberAutMap_hom_app]
  rfl

/-- `fiberAutMap e` only depends on `e` up to a natural isomorphism of the functors `H`. -/
lemma fiberAutMap_congr {H H' : D ⥤ C} (u : H ≅ H') (e : H ⋙ F ≅ G) (e' : H' ⋙ F ≅ G)
    (h : ∀ A, F.map (u.hom.app A) ≫ e'.hom.app A = e.hom.app A) :
    fiberAutMap e = fiberAutMap e' := by
  refine MonoidHom.ext fun σ ↦ Iso.ext (NatTrans.ext (funext fun A ↦ ?_))
  refine FintypeCat.hom_ext _ _ fun x ↦ ?_
  have hA (y : F.obj (H.obj A)) : e.hom.app A y = e'.hom.app A (F.map (u.hom.app A) y) := by
    rw [← h A]
    rfl
  obtain ⟨y, rfl⟩ : ∃ y, e.hom.app A y = x :=
    ⟨e.inv.app A x, FintypeCat.inv_hom_id_apply (e.app A) x⟩
  have hy : e'.inv.app A (e.hom.app A y) = F.map (u.hom.app A) y := by
    rw [hA]
    exact FintypeCat.hom_inv_id_apply (e'.app A) _
  have he : e.inv.app A (e.hom.app A y) = y := FintypeCat.hom_inv_id_apply (e.app A) y
  rw [fiberAutMap_hom_app_apply, fiberAutMap_hom_app_apply, hy, he, hA,
    FunctorToFintypeCat.naturality]

/-- Functoriality: the identity. -/
lemma fiberAutMap_id : fiberAutMap (Functor.leftUnitor F) = MonoidHom.id (Aut F) := by
  refine MonoidHom.ext fun σ ↦ Iso.ext (NatTrans.ext (funext fun A ↦ ?_))
  refine FintypeCat.hom_ext _ _ fun x ↦ ?_
  rw [fiberAutMap_hom_app_apply]
  rfl

/-- Functoriality: composition. -/
lemma fiberAutMap_comp {H₁ : D ⥤ C} {H₂ : E ⥤ D} (e₁ : H₁ ⋙ F ≅ G) (e₂ : H₂ ⋙ G ≅ K) :
    fiberAutMap (Functor.associator H₂ H₁ F ≪≫ isoWhiskerLeft H₂ e₁ ≪≫ e₂) =
      (fiberAutMap e₂).comp (fiberAutMap e₁) := by
  refine MonoidHom.ext fun σ ↦ Iso.ext (NatTrans.ext (funext fun A ↦ ?_))
  refine FintypeCat.hom_ext _ _ fun x ↦ ?_
  rw [MonoidHom.comp_apply, fiberAutMap_hom_app_apply, fiberAutMap_hom_app_apply,
    fiberAutMap_hom_app_apply]
  rfl

open scoped Topology in
/-- `fiberAutMap e` is continuous. -/
lemma continuous_fiberAutMap {H : D ⥤ C} (e : H ⋙ F ≅ G) : Continuous (fiberAutMap e) := by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing,
    continuous_pi_iff]
  intro A
  change Continuous (fun σ ↦ autEmbedding G (fiberAutMap e σ) A)
  have : (fun σ ↦ autEmbedding G (fiberAutMap e σ) A) =
      (fun τ : Aut (F.obj (H.obj A)) ↦ (e.app A).conjAut τ) ∘
        (fun p ↦ p (H.obj A)) ∘ autEmbedding F := by
    ext σ : 1
    refine Iso.ext (FintypeCat.hom_ext _ _ fun x ↦ ?_)
    simp only [Function.comp_apply, autEmbedding_apply, Iso.conjAut_hom, Iso.app_hom,
      Iso.conj_apply]
    exact fiberAutMap_hom_app_apply e σ A x
  rw [this]
  exact continuous_of_discreteTopology.comp ((continuous_apply _).comp
    (autEmbedding_isClosedEmbedding F).continuous)

end AutMap

section Surjective

variable {C : Type u₁} [Category.{u₂} C] {D : Type u₃} [Category.{u₄} D]

/-- Fibre functors are stable under natural isomorphisms. -/
lemma FiberFunctor.ofIso [PreGaloisCategory C] {F G : C ⥤ FintypeCat.{w}} [FiberFunctor F]
    (e : F ≅ G) : FiberFunctor G where
  preservesTerminalObjects := preservesLimitsOfShape_of_natIso e
  preservesPullbacks := preservesLimitsOfShape_of_natIso e
  preservesFiniteCoproducts := ⟨fun _ ↦ preservesColimitsOfShape_of_natIso e⟩
  preservesEpis := Functor.preservesEpimorphisms.of_iso e
  preservesQuotientsByFiniteGroups _ _ _ := preservesColimitsOfShape_of_natIso e
  reflectsIsos := reflectsIsomorphisms_of_iso e

variable (F : C ⥤ FintypeCat.{u₂}) (H : D ⥤ C)

/-- `Aut F` acts on the fibres of `H ⋙ F` (local instance, to avoid diamonds with the action
of `Aut (H ⋙ F)`). -/
abbrev mulActionComp (Y : D) : MulAction (Aut F) ((H ⋙ F).obj Y) :=
  inferInstanceAs (MulAction (Aut F) (F.obj (H.obj Y)))

attribute [local instance] mulActionComp in
lemma isNaturalSMul_comp : IsNaturalSMul (H ⋙ F) (Aut F) where
  naturality σ _ _ f x := (mulAction_naturality F σ (H.map f) x).symm

attribute [local instance] mulActionComp isNaturalSMul_comp in
/-- The homomorphism `Aut F →* Aut (H ⋙ F)` is whiskering with `H`. -/
theorem toAut_comp_hom_app (σ : Aut F) (Y : D) :
    (toAut (H ⋙ F) (Aut F) σ).hom.app Y = σ.hom.app (H.obj Y) := by
  ext x
  exact toAut_hom_app_apply (H ⋙ F) σ x

attribute [local instance] mulActionComp isNaturalSMul_comp in
/-- **SGA 1 V.6.9 (Galois-theoretic part).** If `H : D ⥤ C` sends connected objects to connected
objects and `H ⋙ F` is a fibre functor, then `Aut F → Aut (H ⋙ F)` is surjective. -/
theorem toAut_comp_surjective [GaloisCategory C] [FiberFunctor F] [GaloisCategory D]
    [FiberFunctor (H ⋙ F)] (hH : ∀ Y : D, IsConnected Y → IsConnected (H.obj Y)) :
    Function.Surjective (toAut (H ⋙ F) (Aut F)) := by
  haveI (Y : D) : ContinuousSMul (Aut F) ((H ⋙ F).obj Y) := continuousSMul_aut_fiber F (H.obj Y)
  refine toAut_surjective_of_isPretransitive (H ⋙ F) (Aut F) fun Y _ ↦ ?_
  haveI := hH Y inferInstance
  exact FiberFunctor.isPretransitive_of_isConnected F (H.obj Y)

/-- **SGA 1 V.6.9 (Galois-theoretic part).** If `G` is a fibre functor on `D`, `e : H ⋙ F ≅ G`
and `H` sends connected objects to connected objects, then `fiberAutMap e : Aut F →* Aut G` is
surjective. -/
theorem fiberAutMap_surjective [GaloisCategory C] [FiberFunctor F] [GaloisCategory D]
    {G : D ⥤ FintypeCat.{u₂}} [FiberFunctor G] (e : H ⋙ F ≅ G)
    (hH : ∀ Y : D, IsConnected Y → IsConnected (H.obj Y)) :
    Function.Surjective (fiberAutMap e) := by
  haveI : FiberFunctor (H ⋙ F) := FiberFunctor.ofIso e.symm
  letI := mulActionComp F H
  haveI := isNaturalSMul_comp F H
  have h : ⇑(fiberAutMap e) = e.conjAut ∘ toAut (H ⋙ F) (Aut F) := by
    ext σ : 1
    have : ((whiskeringLeft _ _ _).obj H).mapAut F σ = toAut (H ⋙ F) (Aut F) σ :=
      Iso.ext (NatTrans.ext (funext fun A ↦ (toAut_comp_hom_app F H σ A).symm))
    simp only [fiberAutMap, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    exact congrArg e.conjAut this
  rw [h]
  exact e.conjAut.surjective.comp (toAut_comp_surjective F H hH)

end Surjective

end CategoryTheory.PreGaloisCategory
