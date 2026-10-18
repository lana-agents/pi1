/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Pi1.FundamentalGroup.Galois
public import Pi1.Mathlib.CategoryTheory.Galois.FiberAutMap

/-!
# Any two fibre functors of a Galois category are isomorphic

Let `C` be a Galois category and `F, G : C ⥤ FintypeCat` fibre functors. Then `F ≅ G`
(SGA 1 V.5.6; Grothendieck's Galois theory, cf. Stacks 0BN0 / Lenstra, *Galois theory for
schemes*, 3.18). Consequently `Aut F ≃ₜ* Aut G`, and the étale fundamental group of a connected
scheme does not depend on the geometric base point up to (non-canonical) isomorphism of
topological groups:

* `CategoryTheory.PreGaloisCategory.homEquivSectionsFibers`: `(F ⟶ G) ≃` the sections of
  `A ↦ G(A)` over the pointed Galois objects of `F` (pro-representability of `F`, Mathlib's
  `endEquivSectionsFibers` for `G = F`);
* `CategoryTheory.PreGaloisCategory.nonempty_iso_of_fiberFunctor`: `Nonempty (F ≅ G)` — the
  sections of a cofiltered system of nonempty finite sets are nonempty, and every endomorphism of a
  fibre functor is an isomorphism (`FibreFunctor.end_isIso`);
* `CategoryTheory.PreGaloisCategory.autContinuousMulEquivOfIso`: `Aut F ≃ₜ* Aut G` for `F ≅ G`;
* `AlgebraicGeometry.FiniteEtale.nonempty_fundamentalGroup_continuousMulEquiv`:
  `π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(ξ')` for any two geometric points `ξ, ξ'` of a connected scheme.
-/

@[expose] public section

universe u₁ u₂ u

open CategoryTheory Limits Functor

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] (F G : C ⥤ FintypeCat.{u₂})

-- Local notation for a functor to finite types considered as a functor to types.
local notation "F'" => F ⋙ FintypeCat.incl
local notation "G'" => G ⋙ FintypeCat.incl

/-- The natural transformations `F ⟶ G` are the sections of `A ↦ G(A)` over the pointed Galois
objects `A` of `F` (pro-representability of `F`). -/
noncomputable def homEquivSectionsFibers [FiberFunctor F] :
    (F ⟶ G) ≃ (PointedGaloisObject.incl F ⋙ G').sections :=
  let i1 : (F ⟶ G) ≃ (F' ⟶ G') :=
    (FullyFaithful.whiskeringRight (FullyFaithful.ofFullyFaithful FintypeCat.incl) C).homEquiv
  let i2 : (F' ⟶ G') ≅ (colimit ((PointedGaloisObject.incl F).op ⋙ coyoneda) ⟶ G') :=
    (yoneda.obj G').mapIso (colimit.isoColimitCocone
      ⟨PointedGaloisObject.cocone F, PointedGaloisObject.isColimit F⟩).op
  let i3 : (colimit ((PointedGaloisObject.incl F).op ⋙ coyoneda) ⟶ G') ≅
      limit ((PointedGaloisObject.incl F ⋙ G') ⋙ uliftFunctor.{u₁}) :=
    colimitCoyonedaHomIsoLimit' (PointedGaloisObject.incl F) G'
  let i4 : limit (PointedGaloisObject.incl F ⋙ G' ⋙ uliftFunctor.{u₁}) ≃
      ((PointedGaloisObject.incl F ⋙ G') ⋙ uliftFunctor.{u₁}).sections :=
    Types.limitEquivSections (PointedGaloisObject.incl F ⋙ (G ⋙ FintypeCat.incl) ⋙
      uliftFunctor.{u₁, u₂})
  let i5 : ((PointedGaloisObject.incl F ⋙ G') ⋙ uliftFunctor.{u₁}).sections ≃
      (PointedGaloisObject.incl F ⋙ G').sections :=
    (Types.sectionsEquiv (PointedGaloisObject.incl F ⋙ G')).symm
  i1.trans <| i2.toEquiv.trans <| i3.toEquiv.trans <| i4.trans i5

/-- There is a natural transformation between any two fibre functors. -/
theorem nonempty_hom_of_fiberFunctor [FiberFunctor F] [FiberFunctor G] : Nonempty (F ⟶ G) := by
  haveI : ∀ A : PointedGaloisObject F, Finite ((PointedGaloisObject.incl F ⋙ G').obj A) :=
    fun A ↦ inferInstanceAs (Finite (G.obj A.obj))
  haveI : ∀ A : PointedGaloisObject F, Nonempty ((PointedGaloisObject.incl F ⋙ G').obj A) :=
    fun A ↦ nonempty_fiber_of_isConnected G A.obj
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system
    (PointedGaloisObject.incl F ⋙ G')
  exact ⟨(homEquivSectionsFibers F G).symm ⟨s, hs⟩⟩

/-- **Any two fibre functors of a Galois category are isomorphic.** -/
theorem nonempty_iso_of_fiberFunctor [FiberFunctor F] [FiberFunctor G] : Nonempty (F ≅ G) := by
  obtain ⟨f⟩ := nonempty_hom_of_fiberFunctor F G
  obtain ⟨g⟩ := nonempty_hom_of_fiberFunctor G F
  haveI : IsIso (f ≫ g) := FibreFunctor.end_isIso F (f ≫ g)
  haveI : IsIso (g ≫ f) := FibreFunctor.end_isIso G (g ≫ f)
  have hr : f ≫ (g ≫ inv (f ≫ g)) = 𝟙 F := by
    rw [← Category.assoc, IsIso.hom_inv_id]
  have hl : (inv (g ≫ f) ≫ g) ≫ f = 𝟙 G := by
    rw [Category.assoc, IsIso.inv_hom_id]
  have heq : inv (g ≫ f) ≫ g = g ≫ inv (f ≫ g) := by
    calc inv (g ≫ f) ≫ g = (inv (g ≫ f) ≫ g) ≫ f ≫ (g ≫ inv (f ≫ g)) := by
          rw [hr, Category.comp_id]
      _ = g ≫ inv (f ≫ g) := by rw [← Category.assoc, hl, Category.id_comp]
  exact ⟨⟨f, g ≫ inv (f ≫ g), hr, heq ▸ hl⟩⟩

variable {F G}

/-- Conjugation by an isomorphism `F ≅ G` of functors to finite types is an isomorphism of
topological groups `Aut F ≃ₜ* Aut G`. -/
noncomputable def autContinuousMulEquivOfIso (e : F ≅ G) : Aut F ≃ₜ* Aut G where
  toMulEquiv := e.conjAut
  continuous_toFun := by
    rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing,
      continuous_pi_iff]
    intro A
    have : (fun σ ↦ autEmbedding G (e.conjAut σ) A) =
        (fun τ : Aut (F.obj A) ↦ (e.app A).conjAut τ) ∘ (fun p ↦ p A) ∘ autEmbedding F := by
      ext σ : 1
      refine Iso.ext (FintypeCat.hom_ext _ _ fun x ↦ ?_)
      simp [autEmbedding_apply, Iso.conjAut_hom, Iso.conj_apply]
    change Continuous (fun σ ↦ autEmbedding G (e.conjAut σ) A)
    rw [this]
    exact continuous_of_discreteTopology.comp ((continuous_apply _).comp
      (autEmbedding_isClosedEmbedding F).continuous)
  continuous_invFun := by
    rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing,
      continuous_pi_iff]
    intro A
    have : (fun σ ↦ autEmbedding F (e.conjAut.symm σ) A) =
        (fun τ : Aut (G.obj A) ↦ (e.app A).symm.conjAut τ) ∘ (fun p ↦ p A) ∘ autEmbedding G := by
      ext σ : 1
      have h : e.conjAut.symm σ = e.symm.conjAut σ := by
        apply e.conjAut.injective
        rw [MulEquiv.apply_symm_apply, Iso.conjAut_apply, Iso.conjAut_apply]
        ext : 1
        simp
      change autEmbedding F (e.conjAut.symm σ) A = _
      rw [h]
      refine Iso.ext (FintypeCat.hom_ext _ _ fun x ↦ ?_)
      simp [autEmbedding_apply, Iso.conjAut_hom, Iso.conj_apply]
    change Continuous (fun σ ↦ autEmbedding F (e.conjAut.symm σ) A)
    rw [this]
    exact continuous_of_discreteTopology.comp ((continuous_apply _).comp
      (autEmbedding_isClosedEmbedding G).continuous)

variable (F G) in
/-- The automorphism groups of any two fibre functors of a Galois category are isomorphic as
topological groups. -/
theorem nonempty_aut_continuousMulEquiv [FiberFunctor F] [FiberFunctor G] :
    Nonempty (Aut F ≃ₜ* Aut G) :=
  (nonempty_iso_of_fiberFunctor F G).map autContinuousMulEquivOfIso

end CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

/-- **Independence of the base point**: the étale fundamental groups of a connected scheme at any
two geometric points are isomorphic as topological groups. -/
theorem nonempty_fundamentalGroup_continuousMulEquiv {X : Scheme.{u}} [ConnectedSpace X]
    {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    (ξ : Spec (.of Ω) ⟶ X) (ξ' : Spec (.of Ω') ⟶ X) :
    Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(ξ')) :=
  PreGaloisCategory.nonempty_aut_continuousMulEquiv (fiber ξ) (fiber ξ')

end AlgebraicGeometry.FiniteEtale
