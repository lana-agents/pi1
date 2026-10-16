/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Pi1.FundamentalGroup.HomotopyExact

/-!
# Exactness in the middle of `π₁ᵉᵗ(X_Ω) → π₁ᵉᵗ(X) → G_k` for quasi-compact quasi-separated `X`

Let `k` be a field, `Ω` a separable closure of `k` and `X` a connected, quasi-compact and
quasi-separated `k`-scheme with `X_Ω = Spec Ω ×_k X` connected. We prove exactness in the middle of

  `π₁ᵉᵗ(X_Ω, x) → π₁ᵉᵗ(X, x) → π₁ᵉᵗ(Spec k, x)`

(`AlgebraicGeometry.FiniteEtale.exists_fundamentalGroupMap_baseChange_eq_of_qcqs`) and, for an
`Ω`-rational geometric point `x`, `ker (Π_X → G_k) = im (Δ_X → Π_X)`
(`AlgebraicGeometry.FiniteEtale.ker_toGaloisGroup_eq_range_of_qcqs`), extending the affine case
of `Pi1.FundamentalGroup.HomotopyExact` (SGA 1 IX.6.1).

The descent of sections `X_Ω ⟶ Y` of a finite étale `X`-scheme to some `X_K`, `K / k` finite, is
deduced from the limit formalism of EGA IV 8 in Mathlib
(`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`):

* `IntermediateField.finSubFunctor`: the filtered diagram of finite subextensions `K ⊆ Ω`, with
  colimit `Ω` (`IntermediateField.isColimitFinSubCocone`) when `Ω / k` is algebraic;
* `AlgebraicGeometry.FiniteEtale.baseChangeDiagram`: the cofiltered diagram `K ↦ X_K` of
  schemes over `X`, with limit `X_Ω` (`AlgebraicGeometry.FiniteEtale.isLimitBaseChangeCone`).
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits

namespace IntermediateField

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]

/-- The finite subextensions of `Ω / k`, ordered by inclusion. -/
def FinSub : Type u := {K : IntermediateField k Ω // FiniteDimensional k K}

instance : PartialOrder (FinSub k Ω) := Subtype.partialOrder _

instance : Nonempty (FinSub k Ω) :=
  ⟨⟨⊥, inferInstanceAs (FiniteDimensional k (⊥ : IntermediateField k Ω))⟩⟩

instance : IsDirectedOrder (FinSub k Ω) where
  directed K L := by
    haveI := K.2
    haveI := L.2
    exact ⟨⟨K.1 ⊔ L.1, IntermediateField.finiteDimensional_sup K.1 L.1⟩,
      (le_sup_left : K.1 ≤ K.1 ⊔ L.1), (le_sup_right : L.1 ≤ K.1 ⊔ L.1)⟩

/-- The diagram `K ↦ K` of finite subextensions of `Ω / k`. -/
@[simps]
def finSubFunctor : FinSub k Ω ⥤ CommRingCat.{u} where
  obj K := .of K.1
  map h := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom h)).toRingHom

/-- The cocone `K ⟶ Ω` over `finSubFunctor`. -/
@[simps]
def finSubCocone : Cocone (finSubFunctor k Ω) where
  pt := .of Ω
  ι := { app K := CommRingCat.ofHom K.1.val.toRingHom }

/-- `Ω` is the filtered colimit of its finite subextensions, for `Ω / k` algebraic. -/
def isColimitFinSubCocone [Algebra.IsAlgebraic k Ω] : IsColimit (finSubCocone k Ω) :=
  haveI : ReflectsColimitsOfShape (FinSub k Ω) (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  isColimitOfReflects (forget CommRingCat.{u})
    (Types.FilteredColimit.isColimitOf' _ _
      (fun (x : Ω) ↦ ⟨⟨k⟮x⟯, IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral x)⟩, ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩,
        rfl⟩)
      (fun K a b hab ↦ ⟨K, 𝟙 K, by
        have : a = b := Subtype.ext hab
        rw [this]⟩))

end IntermediateField

namespace AlgebraicGeometry.FiniteEtale

open IntermediateField

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

variable (k Ω) in
/-- The diagram `K ↦ Spec K` over `Spec k`. -/
def specFinSubOver : (FinSub k Ω)ᵒᵖ ⥤ Over (Spec (.of k)) :=
  ((finSubFunctor k Ω).op ⋙ Scheme.Spec).toOver (Spec (.of k))
    (fun K ↦ Spec.map (CommRingCat.ofHom (algebraMap k K.unop.1)))
    (fun h ↦ by
      change Spec.map _ ≫ Spec.map _ = _
      rw [← Spec.map_comp]
      rfl)

variable (k Ω) in
/-- The cone `Spec Ω ⟶ Spec K` over `specFinSubOver`. -/
def specFinSubOverCone : Cone (specFinSubOver k Ω) where
  pt := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
  π := { app K := Over.homMk (Spec.map (CommRingCat.ofHom K.unop.1.val.toRingHom)) (by
          change Spec.map _ ≫ Spec.map _ = _
          rw [← Spec.map_comp]
          rfl)
         naturality K L h := by
          ext1
          change 𝟙 _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
          rw [Category.id_comp, ← Spec.map_comp]
          rfl }

/-- `Spec Ω` is the limit of `Spec K` over the finite subextensions `K` of `Ω / k`. -/
def isLimitSpecFinSubOverCone [Algebra.IsAlgebraic k Ω] :
    IsLimit (specFinSubOverCone k Ω) := by
  haveI : IsCofiltered (FinSub k Ω)ᵒᵖ := inferInstance
  haveI : IsConnected (FinSub k Ω)ᵒᵖ := IsCofiltered.isConnected _
  refine isLimitOfReflects (Over.forget _) ?_
  exact isLimitOfPreserves Scheme.Spec (isColimitFinSubCocone k Ω).op

/-- The diagram `K ↦ X_K = Spec K ×_k X` of schemes. -/
def baseChangeDiagram : (FinSub k Ω)ᵒᵖ ⥤ Scheme.{u} :=
  specFinSubOver k Ω ⋙ Over.pullback f ⋙ Over.forget X

/-- The cone `X_Ω ⟶ X_K` over `baseChangeDiagram`. -/
def baseChangeCone : Cone (baseChangeDiagram (Ω := Ω) f) :=
  (Over.pullback f ⋙ Over.forget X).mapCone (specFinSubOverCone k Ω)

/-- `X_Ω` is the limit of the `X_K` over the finite subextensions `K` of `Ω / k`. -/
def isLimitBaseChangeCone [Algebra.IsAlgebraic k Ω] :
    IsLimit (baseChangeCone (Ω := Ω) f) := by
  haveI : IsConnected (FinSub k Ω)ᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfPreserves (Over.pullback f ⋙ Over.forget X) (isLimitSpecFinSubOverCone)

/-- The projections `X_K ⟶ X`. -/
def baseChangeDiagramπ : baseChangeDiagram (Ω := Ω) f ⟶ (Functor.const _).obj X where
  app K := pullback.snd _ f
  naturality K L h := by
    change ((Over.pullback f).map _).left ≫ _ = _ ≫ 𝟙 X
    rw [Category.comp_id]
    exact Over.w ((Over.pullback f).map ((specFinSubOver k Ω).map h))

lemma baseChangeCone_π_app_snd (K : (FinSub k Ω)ᵒᵖ) :
    (baseChangeCone (Ω := Ω) f).π.app K ≫ pullback.snd _ f = pullback.snd _ f :=
  Over.w ((Over.pullback f).map ((specFinSubOverCone k Ω).π.app K))

/-- **Descent of sections along `X_Ω = lim X_K`.** For a quasi-compact quasi-separated `k`-scheme
`X`, an algebraic extension `Ω / k` and `Y ⟶ X` locally of finite presentation, every morphism
`X_Ω ⟶ Y` over `X` factors through `X_Ω ⟶ X_K` for a finite subextension `K`. -/
lemma exists_section_descent_of_qcqs [Algebra.IsAlgebraic k Ω] [CompactSpace X]
    [QuasiSeparatedSpace X] {Y : Scheme.{u}} (q : Y ⟶ X) [LocallyOfFinitePresentation q]
    (σ : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f ⟶ Y)
    (hσ : σ ≫ q = pullback.snd _ f) :
    ∃ (K : (FinSub k Ω)ᵒᵖ) (ψ : (baseChangeDiagram (Ω := Ω) f).obj K ⟶ Y),
      ψ ≫ q = pullback.snd _ f ∧ (baseChangeCone (Ω := Ω) f).π.app K ≫ ψ = σ := by
  haveI : IsCofiltered (FinSub k Ω)ᵒᵖ := inferInstance
  have hA (K : (FinSub k Ω)ᵒᵖ) : IsAffineHom ((baseChangeDiagramπ (Ω := Ω) f).app K) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) _ _
      (by change IsAffineHom (Spec.map _); infer_instance)
  haveI {K L : (FinSub k Ω)ᵒᵖ} (h : K ⟶ L) :
      IsAffineHom ((baseChangeDiagram (Ω := Ω) f).map h) := by
    have hw : (baseChangeDiagram (Ω := Ω) f).map h ≫ (baseChangeDiagramπ (Ω := Ω) f).app L =
        (baseChangeDiagramπ (Ω := Ω) f).app K := by
      rw [(baseChangeDiagramπ (Ω := Ω) f).naturality h]
      exact Category.comp_id _
    haveI := hA L
    have : IsAffineHom ((baseChangeDiagram (Ω := Ω) f).map h ≫
        (baseChangeDiagramπ (Ω := Ω) f).app L) := by
      rw [hw]
      exact hA K
    exact (IsAffineHom.comp_iff (g := (baseChangeDiagramπ (Ω := Ω) f).app L)).mp this
  haveI (K : (FinSub k Ω)ᵒᵖ) : CompactSpace ((baseChangeDiagram (Ω := Ω) f).obj K) := by
    haveI := hA K
    haveI : CompactSpace (((Functor.const (FinSub k Ω)ᵒᵖ).obj X).obj K) := ‹CompactSpace X›
    exact QuasiCompact.compactSpace_of_compactSpace ((baseChangeDiagramπ (Ω := Ω) f).app K)
  haveI (K : (FinSub k Ω)ᵒᵖ) : QuasiSeparatedSpace ((baseChangeDiagram (Ω := Ω) f).obj K) := by
    haveI := hA K
    haveI : QuasiSeparatedSpace (((Functor.const (FinSub k Ω)ᵒᵖ).obj X).obj K) :=
      ‹QuasiSeparatedSpace X›
    exact quasiSeparatedSpace_of_quasiSeparated ((baseChangeDiagramπ (Ω := Ω) f).app K)
  obtain ⟨K, ψ, hψ1, hψ2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (baseChangeDiagram (Ω := Ω) f) (baseChangeDiagramπ f) q (baseChangeCone f)
    (isLimitBaseChangeCone f) σ (by
      ext K : 2
      change (baseChangeCone (Ω := Ω) f).π.app K ≫ pullback.snd _ f = σ ≫ q
      rw [hσ, baseChangeCone_π_app_snd]
      rfl)
  exact ⟨K, ψ, hψ2, hψ1⟩

/-- **Exactness in the middle of `π₁ᵉᵗ(X_Ω) → π₁ᵉᵗ(X) → π₁ᵉᵗ(Spec k)`** (SGA 1 IX.6.1) for a
connected, quasi-compact and quasi-separated `k`-scheme `X` and a separable closure `Ω` of `k`
with `X_Ω = Spec Ω ×_k X` connected: every `γ ∈ π₁ᵉᵗ(X)` with trivial image in `π₁ᵉᵗ(Spec k)`
comes from `π₁ᵉᵗ(X_Ω)`. -/
theorem exists_fundamentalGroupMap_baseChange_eq_of_qcqs [Algebra.IsSeparable k Ω]
    [IsSepClosed Ω] [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    [ConnectedSpace ↥(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f)]
    (x : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f)
    {η : Spec (.of Ω) ⟶ Spec (.of k)} (h : (x ≫ pullback.snd _ f) ≫ f = η)
    (γ : π₁ᵉᵗ(x ≫ pullback.snd _ f)) (hγ : fundamentalGroupMap f h γ = 1) :
    ∃ δ, fundamentalGroupMap (pullback.snd _ f) rfl δ = γ := by
  let g := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f
  -- `γ` acts trivially on fibres of pullbacks of finite étale `k`-schemes
  have htriv (W : FiniteEtale (Spec (.of k))) (z : (fiber (x ≫ g)).obj ((pullback f).obj W)) :
      γ.hom.app _ z = z :=
    PreGaloisCategory.fiberAutMap_eq_one_apply (pullbackFiberIso f h) hγ W z
  suffices hmem : γ ∈ (PreGaloisCategory.fiberAutMap (pullbackFiberIso g rfl)).range by
    obtain ⟨δ, hδ⟩ := hmem
    exact ⟨δ, hδ⟩
  refine PreGaloisCategory.mem_range_fiberAutMap (pullbackFiberIso g rfl) γ fun Y s p ↦ ?_
  let T₀ := self (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f)
  let i : T₀ ≅ ⊤_ _ := (isTerminalSelf _).uniqueUpToIso terminalIsTerminal
  let s₀ := i.hom ≫ s
  let σ := s₀.left ≫ pullback.fst Y.hom g
  have hs₀ : s₀.left ≫ pullback.snd Y.hom g = 𝟙 _ := MorphismProperty.Over.w s₀
  let q : Y.left ⟶ X := Y.hom
  haveI : IsFiniteEtale q := Y.prop
  have hσ : σ ≫ q = g := by
    have h1 : s₀.left ≫ pullback.snd Y.hom g ≫ g = g := by
      erw [← Category.assoc, hs₀, Category.id_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (s₀.left ≫ ·) pullback.condition).trans h1)
  obtain ⟨K, ψ, hψ1, hψ2⟩ := exists_section_descent_of_qcqs f q σ hσ
  haveI := K.unop.2
  haveI := isFiniteEtale_Spec_intermediateField (k := k) (Ω := Ω) K.unop.1
  let W : FiniteEtale (Spec (.of k)) :=
    mk (Spec.map (CommRingCat.ofHom (algebraMap k K.unop.1)))
  let Z := (pullback f).obj W
  let φ : Z ⟶ Y := MorphismProperty.Over.homMk ψ hψ1 trivial
  let t₀ : T₀ ⟶ (pullback g).obj Z := MorphismProperty.Over.homMk
    (pullback.lift ((baseChangeCone (Ω := Ω) f).π.app K) (𝟙 _)
      (by
        change _ ≫ pullback.snd _ f = 𝟙 _ ≫ g
        exact (baseChangeCone_π_app_snd f K).trans (Category.id_comp _).symm))
    (by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ = 𝟙 _
      rw [pullback.lift_snd]) trivial
  have ht : t₀ ≫ (pullback g).map φ = s₀ := by
    apply MorphismProperty.Over.Hom.ext
    change t₀.left ≫ ((pullback g).map φ).left = s₀.left
    rw [MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · erw [Category.assoc, pullback.lift_fst]
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ ψ = σ
      erw [pullback.lift_fst_assoc, hψ2]
    · erw [Category.assoc, pullback.lift_snd, hs₀]
      exact pullback.lift_snd _ _ _
  let e := pullbackFiberIso (Ω := Ω) g (rfl : x ≫ g = x ≫ g)
  have hsp : s = i.inv ≫ s₀ := by simp [s₀]
  have key : (pullback g ⋙ fiber x).map φ ≫ e.hom.app Y = e.hom.app Z ≫ (fiber (x ≫ g)).map φ :=
    e.hom.naturality φ
  rw [hsp, ← ht, Functor.map_comp, Functor.map_comp, FintypeCat.comp_apply,
    FintypeCat.comp_apply]
  set w := (fiber x).map t₀ ((fiber x).map i.inv p)
  have hw : e.hom.app Y ((fiber x).map ((pullback g).map φ) w) =
      (fiber (x ≫ g)).map φ (e.hom.app Z w) := congr($key w)
  rw [hw, ← FintypeCat.comp_apply, γ.hom.naturality, FintypeCat.comp_apply, htriv W]

/-- **The homotopy exact sequence `1 → Δ_X → Π_X → G_k → 1`, exactness in the middle**
(SGA 1 IX.6.1), for a connected, quasi-compact and quasi-separated `k`-scheme `X` with `X_Ω`
connected, `Ω` a separable closure of `k` and `x` an `Ω`-rational point of `X_Ω`: the kernel of
`Π_X → G_k` is the image of `Δ_X = π₁ᵉᵗ(X_Ω) → Π_X`. -/
theorem ker_toGaloisGroup_eq_range_of_qcqs [IsGalois k Ω] [IsSepClosed Ω] [CompactSpace X]
    [QuasiSeparatedSpace X] [ConnectedSpace X]
    [ConnectedSpace ↥(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f)]
    (x : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f)
    (hx : x ≫ pullback.fst _ f = Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)))
    (h : (x ≫ pullback.snd _ f) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    (toGaloisGroup f h).ker = (fundamentalGroupMap (pullback.snd _ f) rfl).toMonoidHom.range := by
  refine le_antisymm (fun γ hγ ↦ ?_) ?_
  · rw [MonoidHom.mem_ker] at hγ
    have hγ' : fundamentalGroupMap f h γ = 1 :=
      (mulEquivAutFiber k Ω).symm.injective (hγ.trans (map_one _).symm)
    obtain ⟨δ, hδ⟩ := exists_fundamentalGroupMap_baseChange_eq_of_qcqs f x h γ hγ'
    exact ⟨δ, hδ⟩
  · rintro _ ⟨δ, rfl⟩
    exact congr($(toGaloisGroup_comp_fundamentalGroupMap f (pullback.snd _ f) (pullback.fst _ f)
      pullback.condition.symm hx h) δ)

end AlgebraicGeometry.FiniteEtale
