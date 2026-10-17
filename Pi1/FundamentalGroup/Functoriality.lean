/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Pi1.FundamentalGroup.Galois
public import Pi1.Mathlib.CategoryTheory.Galois.FiberAutMap

/-!
# Functoriality of the étale fundamental group

Let `f : Y ⟶ X` be a morphism of schemes, `ξ : Spec Ω ⟶ Y` a geometric point of `Y` and
`η : Spec Ω ⟶ X` with `ξ ≫ f = η`. Base change along `f` is a functor
`pullback f : FiniteEtale X ⥤ FiniteEtale Y`, and

* `FiniteEtale.pullbackFiberIso f h : pullback f ⋙ fiber ξ ≅ fiber η` identifies the fibre of
  `f^* A` over `ξ` with the fibre of `A` over `η`;
* `FiniteEtale.fundamentalGroupMap f h : π₁ᵉᵗ(ξ) →ₜ* π₁ᵉᵗ(η)` is the induced continuous
  homomorphism (whiskering with `f^*`, conjugated by `pullbackFiberIso`);
* `fundamentalGroupMap_id`, `fundamentalGroupMap_comp`: functoriality.

We also characterise the connected objects of `FiniteEtale X`
(`FiniteEtale.isConnected_iff_connectedSpace`): they are the finite étale `X`-schemes whose total
space is connected. Finally (`FiniteEtale.fundamentalGroupMap_surjective`, SGA 1 V.6.9), if
`X` and `Y` are connected and `f^*` preserves connected objects, then `π₁ᵉᵗ(ξ) → π₁ᵉᵗ(η)` is
surjective. The hypothesis holds when `f` is universally open with geometrically connected
fibres (`FiniteEtale.fundamentalGroupMap_surjective_of_geometricallyConnected`, using Mathlib's
`GeometricallyConnected`).
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

variable {X Y W : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

section Functoriality

/-- For `f : Y ⟶ X` and geometric points `ξ` of `Y` and `η = ξ ≫ f` of `X`, the fibre over `ξ`
of the base change `f^* A` is the fibre of `A` over `η`. -/
def pullbackFiberIso (f : Y ⟶ X) {ξ : Spec (.of Ω) ⟶ Y} {η : Spec (.of Ω) ⟶ X}
    (h : ξ ≫ f = η) : pullback f ⋙ fiber ξ ≅ fiber η :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (MorphismProperty.Over.pullbackComp ξ f η h.symm).symm
      (forgetScheme Ω)

omit [IsSepClosed Ω] in
lemma pullbackFiberIso_hom_app (f : Y ⟶ X) {ξ : Spec (.of Ω) ⟶ Y} {η : Spec (.of Ω) ⟶ X}
    (h : ξ ≫ f = η) (A : FiniteEtale X) :
    (pullbackFiberIso f h).hom.app A =
      (forgetScheme Ω).map ((MorphismProperty.Over.pullbackComp ξ f η h.symm).inv.app A) := by
  simp [pullbackFiberIso]
  rfl

/-- The continuous homomorphism `π₁ᵉᵗ(Y, ξ) → π₁ᵉᵗ(X, η)` induced by `f : Y ⟶ X` with
`ξ ≫ f = η`. -/
def fundamentalGroupMap (f : Y ⟶ X) {ξ : Spec (.of Ω) ⟶ Y} {η : Spec (.of Ω) ⟶ X}
    (h : ξ ≫ f = η) : π₁ᵉᵗ(ξ) →ₜ* π₁ᵉᵗ(η) where
  __ := fiberAutMap (pullbackFiberIso f h)
  continuous_toFun := continuous_fiberAutMap _

omit [IsSepClosed Ω] in
lemma fundamentalGroupMap_apply (f : Y ⟶ X) {ξ : Spec (.of Ω) ⟶ Y} {η : Spec (.of Ω) ⟶ X}
    (h : ξ ≫ f = η) (σ : π₁ᵉᵗ(ξ)) :
    fundamentalGroupMap f h σ = fiberAutMap (pullbackFiberIso f h) σ := rfl

/-- `f^* A ≅ A` for `f = 𝟙 X`. -/
def pullbackIdIso (X : Scheme.{u}) : pullback (𝟙 X) ≅ 𝟭 (FiniteEtale X) :=
  NatIso.ofComponents (fun A ↦ MorphismProperty.Over.isoMk
    { hom := Limits.pullback.fst A.hom (𝟙 X)
      inv := Limits.pullback.lift (𝟙 _) A.hom (by simp)
      hom_inv_id := by apply pullback.hom_ext <;> simp [pullback.condition]
      inv_hom_id := by simp } (by simp [pullback.condition])) (by
      intro A B g
      apply MorphismProperty.Over.Hom.ext
      simp [FiniteEtale])

omit [IsSepClosed Ω] in
/-- Functoriality of `π₁ᵉᵗ`: identities. -/
lemma fundamentalGroupMap_id {ξ : Spec (.of Ω) ⟶ X} (h : ξ ≫ 𝟙 X = ξ) :
    fundamentalGroupMap (𝟙 X) h = ContinuousMonoidHom.id _ := by
  ext1 σ
  rw [fundamentalGroupMap_apply, fiberAutMap_congr (pullbackIdIso X) _
    (Functor.leftUnitor (fiber ξ)), fiberAutMap_id]
  · rfl
  intro A
  have : (pullback ξ).map ((pullbackIdIso X).hom.app A) =
      (MorphismProperty.Over.pullbackComp ξ (𝟙 X) ξ h.symm).inv.app A := by
    apply MorphismProperty.Over.Hom.ext
    simp [FiniteEtale, pullbackIdIso]
    apply pullback.hom_ext <;> simp
  rw [pullbackFiberIso_hom_app, ← this]
  exact Category.comp_id _

omit [IsSepClosed Ω] in
/-- Functoriality of `π₁ᵉᵗ`: composition. -/
lemma fundamentalGroupMap_comp (f : Y ⟶ X) (g : X ⟶ W) {ξ : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} {ζ : Spec (.of Ω) ⟶ W} (h₁ : ξ ≫ f = η) (h₂ : η ≫ g = ζ)
    (h : ξ ≫ f ≫ g = ζ) :
    fundamentalGroupMap (f ≫ g) h =
      (fundamentalGroupMap g h₂).comp (fundamentalGroupMap f h₁) := by
  have key (A : FiniteEtale W) :
      (pullback ξ).map ((MorphismProperty.Over.pullbackComp f g).hom.app A) ≫
        (MorphismProperty.Over.pullbackComp ξ f η h₁.symm).inv.app ((pullback g).obj A) ≫
        (MorphismProperty.Over.pullbackComp η g ζ h₂.symm).inv.app A =
      (MorphismProperty.Over.pullbackComp ξ (f ≫ g) ζ h.symm).inv.app A := by
    apply MorphismProperty.Over.Hom.ext
    simp [FiniteEtale]
    apply pullback.hom_ext
    · simp
    · simp
  have hcond (A : FiniteEtale W) :
      (fiber ξ).map ((MorphismProperty.Over.pullbackComp f g).hom.app A) ≫
        (Functor.associator (pullback g) (pullback f) (fiber ξ) ≪≫
          Functor.isoWhiskerLeft (pullback g) (pullbackFiberIso f h₁) ≪≫
          pullbackFiberIso g h₂).hom.app A =
      (pullbackFiberIso (f ≫ g) h).hom.app A := by
    rw [pullbackFiberIso_hom_app, ← key]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, pullbackFiberIso_hom_app, fiber, Functor.comp_map,
      Functor.map_comp, Functor.associator_hom_app]
    erw [Category.id_comp]
  refine ContinuousMonoidHom.ext fun σ ↦ ?_
  change fiberAutMap (pullbackFiberIso (f ≫ g) h) σ =
    fiberAutMap (pullbackFiberIso g h₂) (fiberAutMap (pullbackFiberIso f h₁) σ)
  rw [fiberAutMap_congr (MorphismProperty.Over.pullbackComp f g)
    (pullbackFiberIso (f ≫ g) h) _ hcond, fiberAutMap_comp]
  rfl

omit [IsSepClosed Ω] in
lemma fundamentalGroupMap_congr {f f' : Y ⟶ X} (hf : f = f') {ξ : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} (h : ξ ≫ f = η) (h' : ξ ≫ f' = η) :
    fundamentalGroupMap f h = fundamentalGroupMap f' h' := by
  subst hf
  rfl

omit [IsSepClosed Ω] in
/-- `π₁ᵉᵗ` of an isomorphism is bijective. -/
lemma fundamentalGroupMap_bijective_of_isIso (f : Y ⟶ X) [IsIso f] {ξ : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} (h : ξ ≫ f = η) : Function.Bijective (fundamentalGroupMap f h) := by
  have h2 : η ≫ inv f = ξ := by rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have h3 : ξ ≫ f ≫ inv f = ξ := by rw [IsIso.hom_inv_id, Category.comp_id]
  have h4 : η ≫ inv f ≫ f = η := by rw [IsIso.inv_hom_id, Category.comp_id]
  have e1 (c : π₁ᵉᵗ(ξ)) : fundamentalGroupMap (inv f) h2 (fundamentalGroupMap f h c) = c := by
    have := DFunLike.congr_fun (fundamentalGroupMap_comp f (inv f) h h2 h3) c
    rw [fundamentalGroupMap_congr (IsIso.hom_inv_id f) h3 (Category.comp_id ξ),
      fundamentalGroupMap_id] at this
    exact this.symm
  have e2 (c : π₁ᵉᵗ(η)) : fundamentalGroupMap f h (fundamentalGroupMap (inv f) h2 c) = c := by
    have := DFunLike.congr_fun (fundamentalGroupMap_comp (inv f) f h2 h h4) c
    rw [fundamentalGroupMap_congr (IsIso.inv_hom_id f) h4 (Category.comp_id η),
      fundamentalGroupMap_id] at this
    exact this.symm
  exact ⟨Function.LeftInverse.injective e1, Function.RightInverse.surjective e2⟩

end Functoriality

section Connected

variable (A : FiniteEtale X)

/-- A finite étale `X`-scheme with empty total space is initial. -/
def isInitialOfIsEmptyLeft [IsEmpty A.left] : IsInitial A :=
  IsInitial.ofUniqueHom
    (fun B ↦ MorphismProperty.Over.homMk (AlgebraicGeometry.isInitialOfIsEmpty.to B.left)
      (AlgebraicGeometry.isInitialOfIsEmpty.hom_ext _ _))
    (fun B g ↦ MorphismProperty.Over.Hom.ext
      (AlgebraicGeometry.isInitialOfIsEmpty.hom_ext _ _))

/-- The open and closed subscheme of a finite étale `X`-scheme on a clopen subset. -/
def clopen (s : Set A.left) (hs : IsClopen s) : FiniteEtale X :=
  have : IsClosedImmersion (Scheme.Opens.ι (X := A.left) ⟨s, hs.isOpen⟩) := by
    apply isClosedImmersion_of_isPreimmersion_of_isClosed
    simpa using hs.isClosed
  have : IsFiniteEtale (Scheme.Opens.ι (X := A.left) ⟨s, hs.isOpen⟩) := ⟨⟩
  mk ((Scheme.Opens.ι (X := A.left) ⟨s, hs.isOpen⟩) ≫ A.hom)

/-- The inclusion of `clopen A s hs` into `A`. -/
def clopenι (s : Set A.left) (hs : IsClopen s) : clopen A s hs ⟶ A :=
  MorphismProperty.Over.homMk (Scheme.Opens.ι (X := A.left) ⟨s, hs.isOpen⟩)

instance (s : Set A.left) (hs : IsClopen s) : Mono (clopenι A s hs) := by
  have : IsClosedImmersion (Scheme.Opens.ι (X := A.left) ⟨s, hs.isOpen⟩) := by
    apply isClosedImmersion_of_isPreimmersion_of_isClosed
    simpa using hs.isClosed
  exact (mono_iff _ _ _ _).mpr ⟨inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _)),
    inferInstanceAs (IsClosedImmersion (Scheme.Opens.ι _))⟩

/-- The total space of an initial finite étale `X`-scheme is empty. -/
lemma isEmpty_of_isInitial (hA : IsInitial A) : IsEmpty A.left := by
  refine ⟨fun x ↦ ?_⟩
  let g := hA.to (clopen A ∅ isClopen_empty)
  obtain ⟨⟨y, hy⟩⟩ : Nonempty (clopen A ∅ isClopen_empty).left := ⟨g.left x⟩
  exact hy

/-- **Connected objects of `FEt X`.** A finite étale `X`-scheme is a connected object of
`FiniteEtale X` if and only if its total space is connected. -/
theorem isConnected_iff_connectedSpace : IsConnected A ↔ ConnectedSpace A.left := by
  constructor
  · intro hA
    have hne : Nonempty A.left := by
      by_contra hc
      rw [not_nonempty_iff] at hc
      exact hA.notInitial (isInitialOfIsEmptyLeft A)
    refine @ConnectedSpace.mk _ _ (preconnectedSpace_iff_clopen.mpr fun s hs ↦ ?_) hne
    by_cases he : s = ∅
    · exact .inl he
    refine .inr ?_
    have : IsIso (clopenι A s hs) := by
      refine hA.noTrivialComponent _ _ fun hi ↦ he ?_
      have := isEmpty_of_isInitial _ hi
      exact Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ IsEmpty.false (α :=
        (clopen A s hs).left) ⟨x, hx⟩
    have : IsIso (clopenι A s hs).left :=
      inferInstanceAs (IsIso ((forget _ ⋙ Over.forget _).map (clopenι A s hs)))
    refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨⟨y, hy⟩, rfl⟩ := (clopenι A s hs).left.homeomorph.surjective x
    exact hy
  · intro hA
    refine ⟨fun hi ↦ ?_, fun B i _ hB ↦ ?_⟩
    · have := isEmpty_of_isInitial _ hi
      exact IsEmpty.false (α := A.left) (Classical.arbitrary _)
    · obtain ⟨ho, hc⟩ := (mono_iff _ _ _ i).mp inferInstance
      have hne : Nonempty B.left := by
        by_contra hc
        rw [not_nonempty_iff] at hc
        exact hB (isInitialOfIsEmptyLeft B)
      have hcl : IsClopen (Set.range i.left) :=
        ⟨i.left.isClosedEmbedding.isClosed_range, i.left.isOpenEmbedding.isOpen_range⟩
      have hr : Set.range i.left = Set.univ :=
        (isClopen_iff.mp hcl).resolve_left (Set.Nonempty.ne_empty (Set.range_nonempty _))
      have : Surjective i.left := ⟨Set.range_eq_univ.mp hr⟩
      have : IsIso i.left :=
        (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
      exact isIso_of_isIso_left i

end Connected

section Surjective

/-- **SGA 1 V.6.9.** Let `f : Y ⟶ X` be a morphism of connected schemes such that base change
along `f` preserves connected finite étale covers. Then `π₁ᵉᵗ(Y, ξ) → π₁ᵉᵗ(X, ξ ≫ f)` is
surjective. -/
theorem fundamentalGroupMap_surjective [ConnectedSpace X] [ConnectedSpace Y] (f : Y ⟶ X)
    {ξ : Spec (.of Ω) ⟶ Y} {η : Spec (.of Ω) ⟶ X} (h : ξ ≫ f = η)
    (hf : ∀ A : FiniteEtale X, IsConnected A → IsConnected ((pullback f).obj A)) :
    Function.Surjective (fundamentalGroupMap f h) :=
  fiberAutMap_surjective (fiber ξ) (pullback f) (pullbackFiberIso f h) hf

/-- **SGA 1 V.6.9**, stated with total spaces: if `X`, `Y` are connected and for every finite
étale `A ⟶ X` with connected total space, `A ×_X Y` is connected, then
`π₁ᵉᵗ(Y, ξ) → π₁ᵉᵗ(X, ξ ≫ f)` is surjective. -/
theorem fundamentalGroupMap_surjective_of_connectedSpace [ConnectedSpace X] [ConnectedSpace Y]
    (f : Y ⟶ X) {ξ : Spec (.of Ω) ⟶ Y} {η : Spec (.of Ω) ⟶ X} (h : ξ ≫ f = η)
    (hf : ∀ A : FiniteEtale X, ConnectedSpace A.left →
      ConnectedSpace ↥(Limits.pullback A.hom f : Scheme.{u})) :
    Function.Surjective (fundamentalGroupMap f h) := by
  refine fundamentalGroupMap_surjective f h fun A hA ↦ ?_
  rw [isConnected_iff_connectedSpace] at hA ⊢
  exact hf A hA

/-- If `f` is universally open with geometrically connected fibres, base change along `f`
preserves connected finite étale covers. -/
lemma isConnected_pullback_obj (f : Y ⟶ X) [GeometricallyConnected f] [UniversallyOpen f]
    (A : FiniteEtale X) (hA : IsConnected A) : IsConnected ((pullback f).obj A) := by
  rw [isConnected_iff_connectedSpace] at hA ⊢
  have : ConnectedSpace ↥((𝟭 Scheme).obj A.left) := hA
  exact GeometricallyConnected.connectedSpace (Limits.pullback.fst A.hom f)
    (Limits.pullback.fst A.hom f).isOpenMap

/-- **SGA 1 V.6.9**, geometric form: if `f : Y ⟶ X` is a universally open morphism of connected
schemes with geometrically connected fibres, then `π₁ᵉᵗ(Y, ξ) → π₁ᵉᵗ(X, ξ ≫ f)` is
surjective. -/
theorem fundamentalGroupMap_surjective_of_geometricallyConnected [ConnectedSpace X]
    [ConnectedSpace Y] (f : Y ⟶ X) [GeometricallyConnected f] [UniversallyOpen f]
    {ξ : Spec (.of Ω) ⟶ Y} {η : Spec (.of Ω) ⟶ X} (h : ξ ≫ f = η) :
    Function.Surjective (fundamentalGroupMap f h) :=
  fundamentalGroupMap_surjective f h (isConnected_pullback_obj f)

end Surjective

end AlgebraicGeometry.FiniteEtale
