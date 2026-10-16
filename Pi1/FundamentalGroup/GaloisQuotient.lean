/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.FundamentalGroup.Functoriality
public import Pi1.FundamentalGroup.Point

/-!
# The projection `π₁ᵉᵗ(X) ↠ G_k` for a geometrically connected `k`-scheme

Let `k` be a field, `Ω ⊇ k` a separably closed Galois extension of `k` (i.e. a separable closure),
`f : X ⟶ Spec k` a connected `k`-scheme and `ξ : Spec Ω ⟶ X` a geometric point over
`Spec Ω ⟶ Spec k`. Composing `π₁ᵉᵗ(X, ξ) → π₁ᵉᵗ(Spec k, ξ ≫ f)` with the identification
`π₁ᵉᵗ(Spec k) ≃ Gal(Ω/k)` (`AlgebraicGeometry.FiniteEtale.mulEquivAutFiber`) gives the continuous
homomorphism

  `AlgebraicGeometry.FiniteEtale.toGaloisGroup f h : π₁ᵉᵗ(X, ξ) →* Gal(Ω/k)`,

the map `Π_X → G_k` of the homotopy exact sequence `1 → Δ_X → Π_X → G_k → 1`. It is **surjective
when `X` is geometrically connected over `k`** (`toGaloisGroup_surjective`): every morphism to
the spectrum of a field is universally open (Mathlib), so SGA 1 V.6.9
(`fundamentalGroupMap_surjective_of_geometricallyConnected`) applies.

This is the right half of the homotopy exact sequence; exactness in the middle and injectivity of
`Δ_X = π₁ᵉᵗ(X_Ω) → Π_X` are proved for affine `X` in
`Pi1.FundamentalGroup.HomotopyExact` and `Pi1.FundamentalGroup.BaseChangeInjective`.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

variable {X : Scheme.{u}} {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
  [IsGalois k Ω]

/-- **The projection `Π_X → G_k`**: for `f : X ⟶ Spec k` and a geometric point `ξ` of `X` over
`Spec Ω ⟶ Spec k`, the composite of `π₁ᵉᵗ(X, ξ) → π₁ᵉᵗ(Spec k)` with
`π₁ᵉᵗ(Spec k) ≃ Gal(Ω/k)`. -/
def toGaloisGroup (f : X ⟶ Spec (.of k)) {x : Spec (.of Ω) ⟶ X}
    (h : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) : π₁ᵉᵗ(x) →* (Ω ≃ₐ[k] Ω) :=
  (mulEquivAutFiber k Ω).symm.toMonoidHom.comp (fundamentalGroupMap f h).toMonoidHom

theorem continuous_toGaloisGroup (f : X ⟶ Spec (.of k)) {x : Spec (.of Ω) ⟶ X}
    (h : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    Continuous (toGaloisGroup f h) :=
  (isHomeomorph_mulEquivAutFiber k Ω).homeomorph.symm.continuous.comp
    (fundamentalGroupMap f h).continuous

/-- **`Π_X → G_k` is surjective** for a connected, geometrically connected `k`-scheme `X`. -/
theorem toGaloisGroup_surjective [ConnectedSpace X] (f : X ⟶ Spec (.of k))
    [GeometricallyConnected f] {x : Spec (.of Ω) ⟶ X}
    (h : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    Function.Surjective (toGaloisGroup f h) :=
  (mulEquivAutFiber k Ω).symm.surjective.comp
    (fundamentalGroupMap_surjective_of_geometricallyConnected f h)

omit [IsGalois k Ω] in
/-- The étale fundamental group of `Spec Ω` (at `Spec.map (algebraMap Ω Ω)`) is trivial, for a
separably closed field `Ω`. -/
lemma subsingleton_fundamentalGroup_self :
    Subsingleton π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap Ω Ω))) := by
  haveI : Subsingleton (Ω ≃ₐ[Ω] Ω) := ⟨fun σ τ ↦ AlgEquiv.ext fun a ↦ by
    rw [← mul_one a, ← smul_eq_mul, map_smul, map_smul, map_one, map_one]⟩
  exact (mulEquivAutFiber Ω Ω).symm.injective.subsingleton

/-- **`Δ_X → Π_X → G_k` is trivial.** Let `g : Y ⟶ X` be a morphism of `k`-schemes where `Y` lies
over `Spec Ω` (e.g. `Y = X_Ω`), and `y` an `Ω`-rational point of `Y`. Then the composite
`π₁ᵉᵗ(Y, y) → π₁ᵉᵗ(X, y ≫ g) → Gal(Ω/k)` is trivial. -/
theorem toGaloisGroup_comp_fundamentalGroupMap {Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (g : Y ⟶ X) (p : Y ⟶ Spec (.of Ω))
    (hgp : g ≫ f = p ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) {y : Spec (.of Ω) ⟶ Y}
    (hy : y ≫ p = Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)))
    (h : (y ≫ g) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    (toGaloisGroup f h).comp (fundamentalGroupMap g rfl).toMonoidHom = 1 := by
  refine MonoidHom.ext fun γ ↦ ?_
  have hs : Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) =
        Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Algebra.algebraMap_self, RingHom.id_comp]
  have h₁ : y ≫ g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
    rw [← Category.assoc, h]
  have e1 := DFunLike.congr_fun (fundamentalGroupMap_comp g f rfl h h₁) γ
  have h₂ : y ≫ p ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
    rw [← Category.assoc, hy, hs]
  have e2 := DFunLike.congr_fun (fundamentalGroupMap_comp p
    (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) hy hs h₂) γ
  have e3 : fundamentalGroupMap (g ≫ f) h₁ γ =
      fundamentalGroupMap (p ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) h₂ γ := by
    have key : ∀ (u v : Y ⟶ Spec (.of k)) (_ : u = v)
        (hu : y ≫ u = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
        (hv : y ≫ v = Spec.map (CommRingCat.ofHom (algebraMap k Ω))),
        fundamentalGroupMap u hu γ = fundamentalGroupMap v hv γ := by
      rintro u v rfl hu hv
      rfl
    exact key _ _ hgp _ _
  haveI := subsingleton_fundamentalGroup_self (Ω := Ω)
  have e4 : fundamentalGroupMap p hy γ = 1 := Subsingleton.elim _ _
  have e5 : fundamentalGroupMap f h (fundamentalGroupMap g rfl γ) = 1 := by
    have := e1.symm.trans (e3.trans e2)
    change fundamentalGroupMap f h (fundamentalGroupMap g rfl γ) =
      fundamentalGroupMap _ hs (fundamentalGroupMap p hy γ) at this
    rw [e4, map_one] at this
    exact this
  change (mulEquivAutFiber k Ω).symm (fundamentalGroupMap f h (fundamentalGroupMap g rfl γ)) = 1
  rw [e5, map_one]

end AlgebraicGeometry.FiniteEtale
