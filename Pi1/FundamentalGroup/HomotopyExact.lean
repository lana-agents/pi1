/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.FundamentalGroup.BaseChangeInjective
public import Pi1.FundamentalGroup.GaloisQuotient
public import Pi1.Mathlib.CategoryTheory.Galois.FiberAutMapExact

/-!
# The homotopy exact sequence `1 → Δ_X → Π_X → G_k → 1` for affine `X`

Let `k` be a field, `Ω` a separable closure of `k` (a separably closed, algebraic separable
extension), `X = Spec R` an affine `k`-scheme with `X_Ω = Spec (Ω ⊗[k] R)` connected, and `x` a
geometric point of `X_Ω`. Writing `g : X_Ω ⟶ X` and `f : X ⟶ Spec k`, we prove exactness in the
middle of

  `π₁ᵉᵗ(X_Ω, x) → π₁ᵉᵗ(X, x) → π₁ᵉᵗ(Spec k, x)`

(`AlgebraicGeometry.FiniteEtale.exists_fundamentalGroupMap_baseChange_eq`): the kernel of the right
map is the image of the left map (SGA 1 IX.6.1). Together with the injectivity of the left map
(`fundamentalGroupMap_baseChange_injective`), the surjectivity of `π₁ᵉᵗ(X) → G_k` for
geometrically connected `X` (`toGaloisGroup_surjective`) and `π₁ᵉᵗ(Spec k) ≅ Gal(Ω/k)`, this is the
homotopy exact sequence `1 → Δ_X → Π_X → G_k → 1` for affine `X`; see
`AlgebraicGeometry.FiniteEtale.ker_toGaloisGroup_eq_range` for the statement with `G_k`.

Proof: by the Galois-theoretic criterion `PreGaloisCategory.mem_range_fiberAutMap` it suffices to
show that an element `γ` of the kernel fixes every point of the fibre of a finite étale
`X`-scheme `Y` that comes from a section `X_Ω ⟶ Y_Ω`. Such a section is given by a ring map
`Γ(Y) → Ω ⊗[k] R`; as `Γ(Y)` is finite over `R`, it factors through `K ⊗[k] R` for a finite
subextension `K` (`exists_section_descent`). Hence the point comes from the fibre of
`X_K = X ×_k Spec K`, the pullback of a finite étale `k`-scheme, on which `γ` acts trivially.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry.FiniteEtale

variable {k Ω R : Type u} [Field k] [Field Ω] [Algebra k Ω] [CommRing R] [Algebra k R]

open Algebra.FiniteEtale in
/-- A ring map `B → Ω ⊗[k] R` over `R` out of a finite `R`-algebra factors through `K ⊗[k] R` for
a finite subextension `K` of the algebraic extension `Ω / k`. -/
lemma exists_factor_inclTensor [Algebra.IsAlgebraic k Ω] {B : Type u} [CommRing B] [Algebra R B]
    [Module.Finite R B] (χ : B →+* Ω ⊗[k] R)
    (hχ : χ.comp (algebraMap R B) =
      (Algebra.TensorProduct.includeRight : R →ₐ[k] Ω ⊗[k] R).toRingHom) :
    ∃ (K : IntermediateField k Ω) (_ : FiniteDimensional k K) (χK : B →+* K ⊗[k] R),
      (inclTensor R K).toRingHom.comp χK = χ := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := B)
  obtain ⟨K, hK, hSK⟩ := exists_finiteDimensional_subset_range (A := R)
    (χ '' (S : Set B)) (S.finite_toSet.image _)
  let ι : K ⊗[k] R →ₐ[k] Ω ⊗[k] R := (inclTensor R K).restrictScalars k
  have hmem (b : B) : χ b ∈ ι.range := by
    have hb : b ∈ Submodule.span R (S : Set B) := hS ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem b hb => exact hSK ⟨b, hb, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ⟨1 ⊗ₜ r, ?_⟩ hx
      have := congr($hχ r)
      simp only [RingHom.coe_comp, Function.comp_apply] at this
      rw [this]
      rfl
  let e := AlgEquiv.ofInjective ι (inclTensor_injective K)
  refine ⟨K, hK, e.symm.toAlgHom.toRingHom.comp (χ.codRestrict ι.range hmem), ?_⟩
  ext b
  exact congr($(e.apply_symm_apply ⟨χ b, hmem b⟩))

open Algebra.FiniteEtale in
/-- **Descent of sections.** A morphism `X_Ω ⟶ Y` over `X` into a finite étale `X`-scheme `Y`
(`X = Spec R`) factors through `X_K = Spec (K ⊗[k] R) ⟶ Y` for a finite subextension `K`. -/
lemma exists_section_descent [Algebra.IsAlgebraic k Ω] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))
    [IsFiniteEtale p] (σ : Spec (.of (Ω ⊗[k] R)) ⟶ Y) (hσ : σ ≫ p = baseChangeSpec k Ω R) :
    ∃ (K : IntermediateField k Ω) (_ : FiniteDimensional k K)
      (ψ : Spec (.of (K ⊗[k] R)) ⟶ Y),
      ψ ≫ p = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).toRingHom) ∧
      Spec.map (CommRingCat.ofHom (inclTensor R K).toRingHom) ≫ ψ = σ := by
  let B : CommRingCat.{u} := Γ(Y, ⊤)
  let ρ : CommRingCat.of R ⟶ B := ringHomΓ (mk p)
  letI : Algebra R B := ρ.hom.toAlgebra
  haveI : Algebra.FiniteEtale R B := finiteEtale_ringHomΓ (mk p)
  haveI : IsAffine Y := isAffine_of_isAffineHom p
  have hp : p = Y.isoSpec.hom ≫ Spec.map ρ := hom_eq_isoSpec_hom_comp (mk p)
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (σ ≫ Y.isoSpec.hom)
  have hχR : ρ ≫ χ = CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : R →ₐ[k] Ω ⊗[k] R).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hχ, Category.assoc, ← hp, hσ]
    rfl
  obtain ⟨K, hK, χK, hχK⟩ := exists_factor_inclTensor (k := k) (Ω := Ω) (B := B) χ.hom
    (congr_arg CommRingCat.Hom.hom hχR)
  refine ⟨K, hK, Spec.map (CommRingCat.ofHom χK) ≫ Y.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, hp, Iso.inv_hom_id_assoc, ← Spec.map_comp]
    congr 1
    ext r
    apply inclTensor_injective K
    change (inclTensor R K).toRingHom.comp χK (ρ r) = _
    rw [hχK]
    exact congr($hχR r)
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hχK]
    change Spec.map χ ≫ _ = _
    rw [hχ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The terminal finite étale `X`-scheme `X ⟶ X`. -/
def self (X : Scheme.{u}) : FiniteEtale X :=
  haveI : IsFiniteEtale (𝟙 X) := {}
  mk (𝟙 X)

/-- `X ⟶ X` is terminal in `FiniteEtale X`. -/
def isTerminalSelf (X : Scheme.{u}) : IsTerminal (self X) :=
  IsTerminal.ofUniqueHom
    (fun A ↦ MorphismProperty.Over.homMk A.hom (Category.comp_id A.hom) trivial)
    (fun _ m ↦ MorphismProperty.Over.Hom.ext
      ((Category.comp_id m.left).symm.trans (MorphismProperty.Over.w m)))

/-- `X_K = Spec (K ⊗[k] R)` for a finite separable `K / k` is the pullback of a finite étale
`k`-scheme. -/
lemma isFiniteEtale_Spec_intermediateField [Algebra.IsSeparable k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] :
    IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  haveI : Algebra.IsSeparable k K := Algebra.isSeparable_tower_bot_of_isSeparable k K Ω
  haveI : Algebra.FormallyEtale k K := Algebra.FormallyEtale.of_isSeparable k K
  haveI : Algebra.FinitePresentation k K :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := K)).mp inferInstance
  haveI : Algebra.Etale k K := ⟨inferInstance, inferInstance⟩
  rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finiteEtale_algebraMap_iff]
  exact ⟨⟩

/-- **Exactness in the middle of `π₁ᵉᵗ(X_Ω) → π₁ᵉᵗ(X) → π₁ᵉᵗ(Spec k)`** (SGA 1 IX.6.1) for an
affine `k`-scheme `X = Spec R` and a separable closure `Ω` of `k` with `X_Ω` connected: every
`γ ∈ π₁ᵉᵗ(X)` with trivial image in `π₁ᵉᵗ(Spec k)` comes from `π₁ᵉᵗ(X_Ω)`. -/
theorem exists_fundamentalGroupMap_baseChange_eq [Algebra.IsSeparable k Ω] [IsSepClosed Ω]
    [ConnectedSpace (Spec (.of R))] [ConnectedSpace (Spec (.of (Ω ⊗[k] R)))]
    (x : Spec (.of Ω) ⟶ Spec (.of (Ω ⊗[k] R))) {η : Spec (.of Ω) ⟶ Spec (.of k)}
    (h : (x ≫ baseChangeSpec k Ω R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = η)
    (γ : π₁ᵉᵗ(x ≫ baseChangeSpec k Ω R))
    (hγ : fundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap k R))) h γ = 1) :
    ∃ δ, fundamentalGroupMap (baseChangeSpec k Ω R) rfl δ = γ := by
  open Algebra.FiniteEtale in
  let g := baseChangeSpec k Ω R
  let f := Spec.map (CommRingCat.ofHom (algebraMap k R))
  -- `γ` acts trivially on fibres of pullbacks of finite étale `k`-schemes
  have htriv (W : FiniteEtale (Spec (.of k))) (z : (fiber (x ≫ g)).obj ((pullback f).obj W)) :
      γ.hom.app _ z = z :=
    PreGaloisCategory.fiberAutMap_eq_one_apply (pullbackFiberIso f h) hγ W z
  suffices hmem : γ ∈ (PreGaloisCategory.fiberAutMap (pullbackFiberIso g rfl)).range by
    obtain ⟨δ, hδ⟩ := hmem
    exact ⟨δ, hδ⟩
  refine PreGaloisCategory.mem_range_fiberAutMap (pullbackFiberIso g rfl) γ fun Y s p ↦ ?_
  let T₀ := self (Spec (.of (Ω ⊗[k] R)))
  let i : T₀ ≅ ⊤_ _ := (isTerminalSelf _).uniqueUpToIso terminalIsTerminal
  let s₀ := i.hom ≫ s
  let σ := s₀.left ≫ pullback.fst Y.hom g
  have hs₀ : s₀.left ≫ pullback.snd Y.hom g = 𝟙 _ := MorphismProperty.Over.w s₀
  let q : Y.left ⟶ Spec (.of R) := Y.hom
  haveI : IsFiniteEtale q := Y.prop
  have hσ : σ ≫ q = g := by
    have h1 : s₀.left ≫ pullback.snd Y.hom g ≫ g = g := by
      erw [← Category.assoc, hs₀, Category.id_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (s₀.left ≫ ·) pullback.condition).trans h1)
  obtain ⟨K, hK, ψ, hψ1, hψ2⟩ := exists_section_descent q σ hσ
  haveI := isFiniteEtale_Spec_intermediateField K
  let W : FiniteEtale (Spec (.of k)) := mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let Z := (pullback f).obj W
  let φ : Z ⟶ Y := MorphismProperty.Over.homMk ((pullbackSpecIso k K R).hom ≫ ψ)
    (by
      change ((pullbackSpecIso k K R).hom ≫ ψ) ≫ Y.hom = pullback.snd _ _
      erw [Category.assoc, hψ1, pullbackSpecIso_hom_snd]) trivial
  have hinc : Spec.map (CommRingCat.ofHom (inclTensor R K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).toRingHom) = g := by
    rw [← Spec.map_comp]
    rfl
  let t₀ : T₀ ⟶ (pullback g).obj Z := MorphismProperty.Over.homMk
    (pullback.lift (Spec.map (CommRingCat.ofHom (inclTensor R K).toRingHom) ≫
      (pullbackSpecIso k K R).inv) (𝟙 _)
      (by
        change _ ≫ pullback.snd _ _ = _
        erw [Category.assoc, pullbackSpecIso_inv_snd, hinc, Category.id_comp]))
    (by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ = 𝟙 _
      rw [pullback.lift_snd]) trivial
  have ht : t₀ ≫ (pullback g).map φ = s₀ := by
    apply MorphismProperty.Over.Hom.ext
    change t₀.left ≫ ((pullback g).map φ).left = s₀.left
    rw [MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · erw [Category.assoc, pullback.lift_fst]
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ (pullbackSpecIso k K R).hom ≫ ψ = σ
      erw [pullback.lift_fst_assoc, Category.assoc, Iso.inv_hom_id_assoc, hψ2]
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
(SGA 1 IX.6.1), for an affine `k`-scheme `X = Spec R` with `X_Ω` connected, `Ω` a separable
closure of `k` and `x` an `Ω`-rational point of `X_Ω`: the kernel of `Π_X → G_k` is the image
of `Δ_X = π₁ᵉᵗ(X_Ω) → Π_X`. -/
theorem ker_toGaloisGroup_eq_range [IsGalois k Ω] [IsSepClosed Ω]
    [ConnectedSpace (Spec (.of R))] [ConnectedSpace (Spec (.of (Ω ⊗[k] R)))]
    (x : Spec (.of Ω) ⟶ Spec (.of (Ω ⊗[k] R)))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[k] R))) =
      Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)))
    (h : (x ≫ baseChangeSpec k Ω R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    (toGaloisGroup (Spec.map (CommRingCat.ofHom (algebraMap k R))) h).ker =
      (fundamentalGroupMap (baseChangeSpec k Ω R) rfl).toMonoidHom.range := by
  have hgp : baseChangeSpec k Ω R ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) =
      Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[k] R))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
    rw [baseChangeSpec, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    change (1 : Ω) ⊗ₜ[k] algebraMap k R a = algebraMap k Ω a ⊗ₜ[k] (1 : R)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  refine le_antisymm (fun γ hγ ↦ ?_) ?_
  · rw [MonoidHom.mem_ker] at hγ
    have hγ' : fundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap k R))) h γ = 1 :=
      (mulEquivAutFiber k Ω).symm.injective (hγ.trans (map_one _).symm)
    obtain ⟨δ, hδ⟩ := exists_fundamentalGroupMap_baseChange_eq x h γ hγ'
    exact ⟨δ, hδ⟩
  · rintro _ ⟨δ, rfl⟩
    exact congr($(toGaloisGroup_comp_fundamentalGroupMap _ _ _ hgp hx h) δ)

end AlgebraicGeometry.FiniteEtale
