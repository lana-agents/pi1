/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.FundamentalGroup.Functoriality
public import Pi1.Mathlib.AlgebraicGeometry.Normalization

/-!
# Finite étale covers and dense opens with trivial normalization

Let `j : U ⟶ X` be a quasi-compact quasi-separated morphism whose relative normalization is
trivial (`IsIso j.fromNormalization`), e.g. the inclusion of a dense open subscheme of a normal
scheme. Then a finite étale `X`-scheme `Y` is the normalization of `X` in `U ×_X Y`
(`Scheme.Hom.isIso_fromNormalization_pullback_snd`, normalization commutes with étale base
change), and consequently:

* `AlgebraicGeometry.Scheme.Hom.preconnectedSpace_of_isIso_fromNormalization`: if the normalization
  of `T` in `W` is trivial and `T` is connected, then `W` is connected: a decomposition of `W`
  into two disjoint nonempty open subschemes induces one of its normalization
  (`Scheme.Hom.normalizationCoprodIso`);
* `AlgebraicGeometry.FiniteEtale.connectedSpace_pullback_of_isIso_fromNormalization`: base change
  along `j` preserves connected finite étale covers (with nonempty restriction), so that
  `π₁ᵉᵗ(U) → π₁ᵉᵗ(X)` is surjective (`FiniteEtale.fundamentalGroupMap_surjective`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {W T : Scheme.{u}} (a : W ⟶ T) [QuasiCompact a] [QuasiSeparated a]

/-- If the relative normalization of `a : W ⟶ T` is trivial and `T` is connected, then `W` is
preconnected. -/
theorem preconnectedSpace_of_isIso_fromNormalization [IsIso a.fromNormalization]
    [ConnectedSpace T] : PreconnectedSpace W := by
  refine preconnectedSpace_iff_clopen.mpr fun s hs ↦ ?_
  by_contra hne
  push Not at hne
  obtain ⟨hs₀, hs₁⟩ := hne
  let V₁ : W.Opens := ⟨s, hs.isOpen⟩
  let V₂ : W.Opens := ⟨sᶜ, hs.compl.isOpen⟩
  have : IsClosedImmersion V₁.ι := by
    apply isClosedImmersion_of_isPreimmersion_of_isClosed
    simpa [V₁] using hs.isClosed
  have : IsClosedImmersion V₂.ι := by
    apply isClosedImmersion_of_isPreimmersion_of_isClosed
    simpa [V₂] using hs.compl.isClosed
  have hcompl : IsCompl V₁.ι.opensRange V₂.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]
      ext x
      simp [V₁, V₂]
    · rw [codisjoint_iff]
      ext x
      simp only [TopologicalSpace.Opens.coe_sup, Set.mem_union, SetLike.mem_coe,
        TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      exact em (x ∈ s)
  obtain ⟨e⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl V₁.ι V₂.ι hcompl
  let E := a.normalizationCoprodIso e
  -- both summands of the normalization are nonempty
  obtain ⟨x₁, hx₁⟩ := hs₀
  obtain ⟨x₂, hx₂⟩ : sᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    exact hs₁
  let y₁ : (V₁.ι ≫ a).normalization := (V₁.ι ≫ a).toNormalization ⟨x₁, hx₁⟩
  let y₂ : (V₂.ι ≫ a).normalization := (V₂.ι ≫ a).toNormalization ⟨x₂, hx₂⟩
  -- the normalization of `W`, hence `T`, is the disjoint union of two nonempty open subsets
  let φ : (V₁.ι ≫ a).normalization ⊕ (V₂.ι ≫ a).normalization ≃ₜ T :=
    (coprodMk _ _).trans (E.hom ≫ a.fromNormalization).homeomorph
  have hT : _root_.IsPreconnected (Set.univ : Set T) := isPreconnected_univ
  have hopen₁ : IsOpen (φ '' Set.range Sum.inl) :=
    φ.isOpenMap _ isOpen_range_inl
  have hopen₂ : IsOpen (φ '' Set.range Sum.inr) :=
    φ.isOpenMap _ isOpen_range_inr
  have hcover : Set.univ ⊆ φ '' Set.range Sum.inl ∪ φ '' Set.range Sum.inr := by
    rw [← Set.image_union, Set.range_inl_union_range_inr, Set.image_univ,
      φ.surjective.range_eq]
  obtain ⟨z, -, hz₁, hz₂⟩ := hT _ _ hopen₁ hopen₂ hcover
    ⟨φ (Sum.inl y₁), trivial, Set.mem_image_of_mem _ ⟨y₁, rfl⟩⟩
    ⟨φ (Sum.inr y₂), trivial, Set.mem_image_of_mem _ ⟨y₂, rfl⟩⟩
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ := hz₁
  obtain ⟨_, ⟨v, rfl⟩, hv⟩ := hz₂
  exact Sum.inl_ne_inr (φ.injective (hu.trans hv.symm))

/-- If the relative normalization of `a : W ⟶ T` is trivial and `T` is connected, then `W` is
connected (it is nonempty since `W ⟶ a.normalization` is dominant). -/
theorem connectedSpace_of_isIso_fromNormalization [IsIso a.fromNormalization]
    [ConnectedSpace T] : ConnectedSpace W := by
  have := a.preconnectedSpace_of_isIso_fromNormalization
  refine ⟨?_⟩
  by_contra hW
  rw [not_nonempty_iff] at hW
  have hd : DenseRange a.toNormalization := a.toNormalization.denseRange
  have : IsEmpty a.normalization := by
    refine ⟨fun y ↦ ?_⟩
    have hy : y ∈ closure (Set.range a.toNormalization) := hd.closure_range ▸ Set.mem_univ y
    simp [Set.range_eq_empty] at hy
  obtain ⟨t⟩ := (inferInstance : Nonempty T)
  exact IsEmpty.false (inv a.fromNormalization t)

end Scheme.Hom

namespace FiniteEtale

variable {U X : Scheme.{u}} (j : U ⟶ X) [QuasiCompact j] [QuasiSeparated j]
  [IsIso j.fromNormalization]

/-- Base change along a morphism with trivial relative normalization (e.g. a dense open
immersion into a normal scheme) preserves connected finite étale covers. -/
theorem connectedSpace_pullback_of_isIso_fromNormalization (A : FiniteEtale X)
    [ConnectedSpace A.left] : ConnectedSpace ↥(Limits.pullback A.hom j : Scheme.{u}) := by
  have := Scheme.Hom.isIso_fromNormalization_pullback_fst j A.hom
  have : ConnectedSpace ↥((𝟭 Scheme).obj A.left) := ‹_›
  exact (pullback.fst A.hom j).connectedSpace_of_isIso_fromNormalization

/-- **`π₁ᵉᵗ(U) ↠ π₁ᵉᵗ(X)`** for a morphism `j : U ⟶ X` of connected schemes with trivial
relative normalization, e.g. the inclusion of a dense open subscheme of a normal scheme. -/
theorem fundamentalGroupMap_surjective_of_isIso_fromNormalization [ConnectedSpace X]
    [ConnectedSpace U] {Ω : Type u} [Field Ω] [IsSepClosed Ω] {ξ : Spec (.of Ω) ⟶ U}
    {η : Spec (.of Ω) ⟶ X} (h : ξ ≫ j = η) :
    Function.Surjective (fundamentalGroupMap j h) :=
  fundamentalGroupMap_surjective_of_connectedSpace j h fun A _ ↦
    connectedSpace_pullback_of_isIso_fromNormalization j A

end FiniteEtale

end AlgebraicGeometry
