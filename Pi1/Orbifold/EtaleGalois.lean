/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.FundamentalGroup.GenericPoint
public import Pi1.Orbifold.Comparison
public import Pi1.Orbifold.EtaleScheme

/-!
# `π₁ᵉᵗ(Spec R)` as a Galois group, via the generic point (SGA 1 V.8.2)

Let `D : GaloisData k t` (`H_L ≤ H ≤ Gal(Ω / k(t))`, `L = Ω^{H_L}`, `R` the integral closure of
`k[t]` in `L`), with `Ω` separably closed. The generic point `Spec L ⟶ Spec R`
(`GaloisData.genericPoint`) gives the **intrinsic Galois action**

  `GaloisData.galoisHomL : H_L →* Gal(Ω / L) ≅ π₁ᵉᵗ(Spec L) → π₁ᵉᵗ(Spec R)`,

where `σ` acts on a point `Spec Ω ⟶ Y` of a finite étale `Spec R`-scheme by precomposition with
`Spec σ` (`GaloisData.galoisHomL_hom_app_left`). It is surjective, as `R` is integrally closed in
`L` (`GaloisData.galoisHomL_surjective`).

If `H ≤ H_L` (so `H = H_L` and `A = H ⧸ H_L` is trivial), then `GaloisData.galoisHom : H →*
π₁ᵉᵗ(Spec R)` agrees with the action `D.toEtalePi1` on pi1's algebraic model under
`etalePi1SpecEquivOfSubsingleton` (`GaloisData.etalePi1SpecEquiv_galoisHom`). Hence, by the
comparison theorem `GaloisData.equivPi1`:

* `GaloisData.ker_galoisHom`: `ker (H → π₁ᵉᵗ(Spec R)) = ⟨⟨S⟩⟩` (closed normal closure of the
  inertia elements);
* `GaloisData.galoisHom_surjective`;
* `GaloisData.equivPi1Spec : π₁ᵉᵗ(Spec R) ≃ₜ* GaloisPi1.pi1 H S = H ⧸ ⟨⟨S⟩⟩`, whose inverse is
  induced by `galoisHom` (`GaloisData.equivPi1Spec_symm_mk`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale AffOrbicurve
  IntermediateField.algebraAdjoinAdjoin

namespace Pi1.Orbifold

noncomputable section

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

namespace GaloisData

variable (D : GaloisData k t)

/-- The inclusion `R ⊆ L` of the coordinate ring into the function field. -/
instance algebraL : Algebra D.R D.L :=
  ((algebraMap D.R Ω).codRestrict D.L CoordRing.algebraMap_mem).toAlgebra

instance : IsScalarTower D.R D.L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma algebraMap_L_injective : Function.Injective (algebraMap D.R D.L) :=
  fun _ _ h => CoordRing.ext (congrArg Subtype.val h)

/-- `R` is integrally closed in `L`. -/
lemma mem_range_algebraMap_L {x : D.L} (hx : IsIntegral D.R x) :
    x ∈ Set.range (algebraMap D.R D.L) := by
  have h1 : IsIntegral D.R (x : Ω) := hx.map (IsScalarTower.toAlgHom D.R D.L Ω)
  have h2 : IsIntegral (A₀ k t) (x : Ω) := isIntegral_trans (A := D.R) _ h1
  exact ⟨CoordRing.mk (x : Ω) x.2 h2, Subtype.ext rfl⟩

/-- The generic point `Spec L ⟶ Spec R`. -/
abbrev genericPoint : Spec (.of D.L) ⟶ Spec (.of D.R) :=
  Spec.map (CommRingCat.ofHom (algebraMap D.R D.L))

lemma genericPoint_comp :
    Spec.map (CommRingCat.ofHom (algebraMap D.L Ω)) ≫ D.genericPoint = specPoint D.R Ω := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- An element of `H_L` is an automorphism of `Ω` over `L`. -/
def toGalL : D.HL →* (Ω ≃ₐ[D.L] Ω) where
  toFun σ := AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv) fun x =>
    (IntermediateField.mem_fixedField_iff _ _).1 x.2 _ σ.2
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma toGalL_apply (σ : D.HL) (x : Ω) : D.toGalL σ x = (σ : Ω ≃ₐ[K₀ k t] Ω) x := rfl

variable [IsGalois (K₀ k t) Ω]

lemma toGalL_surjective : Function.Surjective D.toGalL := by
  intro τ
  have hτ : τ.restrictScalars (K₀ k t) ∈ D.HL := by
    rw [← D.fixingSubgroup_L, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact τ.commutes ⟨x, hx⟩
  exact ⟨⟨_, hτ⟩, AlgEquiv.ext fun _ => rfl⟩

instance isGalois_L : IsGalois D.L Ω := IsGalois.tower_top_of_isGalois (K₀ k t) D.L Ω

variable [IsSepClosed Ω]

/-- **The intrinsic Galois action of `H_L`** on the fibre functor of `Spec R` at
`Spec Ω ⟶ Spec R`, through the generic point: `H_L → Gal(Ω / L) ≅ π₁ᵉᵗ(Spec L) → π₁ᵉᵗ(Spec R)`.
-/
def galoisHomL : D.HL →* π₁ᵉᵗ(specPoint D.R Ω) :=
  (galoisAction D.L D.genericPoint D.genericPoint_comp).comp D.toGalL

lemma galoisHomL_eq (σ : D.HL) :
    D.galoisHomL σ = galoisAction D.L D.genericPoint D.genericPoint_comp (D.toGalL σ) := rfl

/-- **The intrinsic Galois action**: `σ ∈ H_L` acts on a point `x : Spec Ω ⟶ Y` of a finite étale
`Spec R`-scheme by precomposition with `Spec σ`. -/
lemma galoisHomL_hom_app_left (σ : D.HL) (Y : FiniteEtale (Spec (.of D.R)))
    (x : (fiber (specPoint D.R Ω)).obj Y) :
    (fiberObjEquivHom _ Y ((D.galoisHomL σ).hom.app Y x)).left =
      Spec.map (CommRingCat.ofHom ((σ : Ω ≃ₐ[K₀ k t] Ω) : Ω →+* Ω)) ≫
        (fiberObjEquivHom _ Y x).left :=
  galoisAction_hom_app_left D.L D.genericPoint D.genericPoint_comp (D.toGalL σ) Y x

/-- **Surjectivity from the generic point**: `H_L → π₁ᵉᵗ(Spec R)` is surjective, as `R` is
integrally closed in `L`. -/
theorem galoisHomL_surjective : Function.Surjective D.galoisHomL := by
  have h := galoisAction_surjective D.L D.R (Ω := Ω) D.algebraMap_L_injective
    fun _ hx => D.mem_range_algebraMap_L hx
  rw [galoisHomL, MonoidHom.coe_comp]
  exact h.comp D.toGalL_surjective

omit [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] in
/-- If `H ≤ H_L`, the group `A = H ⧸ H_L` is trivial. -/
lemma subsingleton_A (hH : D.H ≤ D.HL) : Subsingleton D.A := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  exact hH (a⁻¹ * b).2

/-- **The intrinsic Galois action of `H`** (for `H ≤ H_L`) on the fibre functor of `Spec R`. -/
def galoisHom (hH : D.H ≤ D.HL) : D.H →* π₁ᵉᵗ(specPoint D.R Ω) :=
  D.galoisHomL.comp (Subgroup.inclusion hH)

lemma galoisHom_apply (hH : D.H ≤ D.HL) (σ : D.H) :
    D.galoisHom hH σ = D.galoisHomL (Subgroup.inclusion hH σ) := rfl

/-- **The intrinsic Galois action is the action on pi1's algebraic model**: for `H ≤ H_L`, the
action `D.toEtalePi1` of `H` on the fibres `X.B →ₐ[R] Ω` corresponds to the action of `H` on the
points `Spec Ω ⟶ Spec X.B` by precomposition. -/
theorem etalePi1SpecEquiv_galoisHom (hH : D.H ≤ D.HL) (σ : D.H) :
    letI := D.subsingleton_A hH
    etalePi1SpecEquivOfSubsingleton D.R Ω D.A (D.galoisHom hH σ) = D.toEtalePi1 σ := by
  letI := D.subsingleton_A hH
  refine FibreAut.ext fun X f => ?_
  letI := X.etale
  letI := X.finite
  rw [etalePi1SpecEquivOfSubsingleton_app, toEtalePi1_app]
  apply (homSpecEquivAlgHom D.R Ω (CommAlgCat.FiniteEtale.of D.R X.B)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  rw [galoisHom_apply, galoisHomL_hom_app_left, Equiv.apply_symm_apply]
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom f.toRingHom) =
    Spec.map (CommRingCat.ofHom (D.fibreSmul σ X f).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
    (RingHom.ext fun b => (D.fibreSmul_of_mem (hH σ.2) X f b).symm)

lemma continuous_galoisHom (hH : D.H ≤ D.HL) : Continuous (D.galoisHom hH) := by
  letI := D.subsingleton_A hH
  have : ⇑(D.galoisHom hH) = (etalePi1SpecEquivOfSubsingleton D.R Ω D.A).symm ∘ D.toEtalePi1 :=
    funext fun σ => by
      rw [Function.comp_apply, ← etalePi1SpecEquiv_galoisHom,
        ContinuousMulEquiv.symm_apply_apply]
  rw [this]
  exact (etalePi1SpecEquivOfSubsingleton D.R Ω D.A).symm.continuous.comp D.continuous_toEtalePi1

variable [CharZero k]

/-- **The kernel of the intrinsic Galois action** `H → π₁ᵉᵗ(Spec R)` (for `H ≤ H_L`) is the
closed normal subgroup generated by the inertia elements. -/
theorem ker_galoisHom (hH : D.H ≤ D.HL) :
    (D.galoisHom hH).ker = GaloisPi1.kernel D.H D.S := by
  letI := D.subsingleton_A hH
  ext σ
  rw [MonoidHom.mem_ker]
  -- (stated without `1 : H ⧸ ⟨⟨S⟩⟩`, whose `One` instance search times out here)
  have key : D.galoisHom hH σ = 1 ↔ D.toEtalePi1 σ = D.toEtalePi1 1 := by
    rw [map_one, ← D.etalePi1SpecEquiv_galoisHom hH σ]
    exact ⟨fun h => by rw [h, map_one], fun h =>
      (etalePi1SpecEquivOfSubsingleton D.R Ω D.A).injective (h.trans (map_one _).symm)⟩
  rw [key, ← pi1ToEtalePi1_mk, ← pi1ToEtalePi1_mk, D.pi1ToEtalePi1_injective.eq_iff,
    QuotientGroup.eq, mul_one, inv_mem_iff]

theorem galoisHom_surjective (hH : D.H ≤ D.HL) : Function.Surjective (D.galoisHom hH) := by
  letI := D.subsingleton_A hH
  intro γ
  obtain ⟨x, hx⟩ := D.pi1ToEtalePi1_surjective (etalePi1SpecEquivOfSubsingleton D.R Ω D.A γ)
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨σ, (etalePi1SpecEquivOfSubsingleton D.R Ω D.A).injective ?_⟩
  rw [etalePi1SpecEquiv_galoisHom, ← hx, pi1ToEtalePi1_mk]

/-- **SGA 1 V.8.2 for `Spec R`** (`H ≤ H_L`): the étale fundamental group of the scheme `Spec R`
at `Spec Ω ⟶ Spec R` is `H ⧸ ⟨⟨S⟩⟩`. The inverse is induced by the intrinsic Galois action
(`equivPi1Spec_symm_mk`). -/
def equivPi1Spec (hH : D.H ≤ D.HL) :
    π₁ᵉᵗ(specPoint D.R Ω) ≃ₜ* GaloisPi1.pi1 D.H D.S D.isClosed_H :=
  letI := D.subsingleton_A hH
  (etalePi1SpecEquivOfSubsingleton D.R Ω D.A).trans D.equivPi1

lemma equivPi1Spec_symm_mk (hH : D.H ≤ D.HL) (σ : D.H) :
    (D.equivPi1Spec hH).symm (σ : D.H ⧸ GaloisPi1.kernel D.H D.S) = D.galoisHom hH σ := by
  letI := D.subsingleton_A hH
  apply (etalePi1SpecEquivOfSubsingleton D.R Ω D.A).injective
  rw [etalePi1SpecEquiv_galoisHom]
  change (etalePi1SpecEquivOfSubsingleton D.R Ω D.A)
    ((etalePi1SpecEquivOfSubsingleton D.R Ω D.A).symm (D.equivPi1.symm _)) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  rfl

end GaloisData

end

end Pi1.Orbifold
