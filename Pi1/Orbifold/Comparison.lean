/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Orbifold.Induced

/-!
# The étale fundamental group of `[Spec R / A]` is a Galois group (SGA 1 V.8.2)

Let `k` be a field of characteristic `0`, `Ω / k(t)` an algebraic Galois extension (`t`
transcendental over `k`), and `D : GaloisData k t`: open subgroups `H_L ≤ H` of
`Gal(Ω / k(t))`, `H` normalizing `H_L`. Let `L = Ω^{H_L}`, `R` the integral closure of `k[t]`
in `L` and `A = H ⧸ H_L`, acting on `R`. Let `S ⊆ H_L` be the set of inertia elements at the
places of `Ω` centered on `Spec R`.

**Theorem** (`GaloisData.equivPi1`). The action of `H` on the fibres of `A`-equivariant finite
étale covers of `Spec R` induces an isomorphism of profinite groups

  `etalePi1 R A Ω ≃ₜ* GaloisPi1.pi1 H S = H ⧸ ⟨⟨S⟩⟩`.

The map `H ⧸ ⟨⟨S⟩⟩ → etalePi1 R A Ω` is `GaloisData.pi1ToEtalePi1` (inertia acts trivially:
`Pi1.Orbifold.GaloisAction`). It is injective: for `σ ∉ ⟨⟨S⟩⟩` there is an open normal subgroup
`U ⊴ H`, `U ≤ H_L`, containing `S` but not `σ`, and `σ` moves the distinguished fibre element of
the induced cover attached to `U` (`Pi1.Orbifold.Induced`). Its image is dense: given an
automorphism `α` of the fibre functor and finitely many fibre elements, the induced cover of a
small enough level dominates all of them, and its fibre is a single `H`-orbit. As the source is
compact and the target Hausdorff, it is a homeomorphism.
-/

@[expose] public section

universe u

open CategoryTheory AffOrbicurve IntermediateField.algebraAdjoinAdjoin

namespace Pi1.Orbifold

noncomputable section

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

namespace GaloisData

variable (D : GaloisData k t)

lemma mem_kernel_of_mem_S (s : D.H) (hs : (s : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S) :
    s ∈ GaloisPi1.kernel D.H D.S := by
  rw [GaloisPi1.kernel, Subgroup.mem_subgroupOf]
  exact Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨1, D.H.one_mem, s, hs, by simp⟩)

variable [IsGalois (K₀ k t) Ω]

instance compactSpace_H : CompactSpace D.H := GaloisPi1.compactSpace_of_isClosed _ D.isClosed_H

/-- The level `U = core_H(V₀)` attached to an open subgroup `V₀ ≤ H_L` containing the
`H`-conjugates of the inertia elements. -/
def Level.ofOpen (V₀ : Subgroup D.H) (hV₀ : IsOpen (V₀ : Set D.H))
    (hle : V₀ ≤ D.HL.subgroupOf D.H)
    (hS : ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S → ∀ g : D.H, g * σ * g⁻¹ ∈ V₀) : D.Level where
  U := V₀.normalCore
  normal := inferInstance
  isOpen := by
    haveI : Finite (D.H ⧸ V₀) := Subgroup.quotient_finite_of_isOpen _ hV₀
    haveI : V₀.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
      (Subgroup.normalCore_isClosed _ (Subgroup.isClosed_of_isOpen _ hV₀))
  le := (Subgroup.normalCore_le _).trans hle
  S_le σ hσ := fun g => hS σ hσ g

lemma Level.ofOpen_U_le (V₀ : Subgroup D.H) (hV₀ : IsOpen (V₀ : Set D.H))
    (hle : V₀ ≤ D.HL.subgroupOf D.H)
    (hS : ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S → ∀ g : D.H, g * σ * g⁻¹ ∈ V₀) :
    (Level.ofOpen D V₀ hV₀ hle hS).U ≤ V₀ :=
  Subgroup.normalCore_le _

lemma Level.ofOpen_conj_mem {V₀ : Subgroup D.H} {hV₀ : IsOpen (V₀ : Set D.H)}
    {hle : V₀ ≤ D.HL.subgroupOf D.H}
    {hS : ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S → ∀ g : D.H, g * σ * g⁻¹ ∈ V₀} {u : D.H}
    (hu : u ∈ (Level.ofOpen D V₀ hV₀ hle hS).U) (g : D.H) : g * u * g⁻¹ ∈ V₀ :=
  hu g

variable [CharZero k]

/-- **Injectivity**: the action of `H ⧸ ⟨⟨S⟩⟩` on the fibre functor is faithful. -/
theorem pi1ToEtalePi1_injective : Function.Injective D.pi1ToEtalePi1 := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  rw [pi1ToEtalePi1_mk] at hx
  rw [QuotientGroup.eq_one_iff]
  by_contra hσ
  have hK := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := D.H)
    ⟨GaloisPi1.kernel D.H D.S, GaloisPi1.isClosed_kernel _ _⟩
  have hσ' : σ ∉ sInf {N : Subgroup D.H | IsOpen (N : Set D.H) ∧
      GaloisPi1.kernel D.H D.S ≤ N} := by
    rw [← hK]; exact hσ
  rw [Subgroup.mem_sInf] at hσ'
  push Not at hσ'
  obtain ⟨W, ⟨hWo, hKW⟩, hσW⟩ := hσ'
  let V := Level.ofOpen D (W ⊓ D.HL.subgroupOf D.H)
    (hWo.inter (D.isOpen_HL.preimage continuous_subtype_val)) inf_le_right
    (fun s hs g => ⟨hKW ((inferInstance : (GaloisPi1.kernel D.H D.S).Normal).conj_mem s
        (D.mem_kernel_of_mem_S s hs) g),
      (Subgroup.mem_subgroupOf).2 (D.conj_mem g g.2 s hs.1)⟩)
  have hfix : D.fibreSmul σ V.X V.f₀ = V.f₀ := by
    have := congrArg (fun α : etalePi1 D.R D.A Ω => α.app V.X V.f₀) hx
    exact this
  exact hσW (Level.ofOpen_U_le D _ _ _ _ (V.mem_U_of_fibreSmul_f₀ hfix)).1

/-- **Density**: every automorphism of the fibre functor agrees with the action of an element of
`H` on any given finite set of fibre elements. -/
theorem exists_toEtalePi1_eq (α : etalePi1 D.R D.A Ω)
    (T : Finset (Σ X : EquivEtale D.R D.A, (etaleFibre D.R D.A Ω).obj X)) :
    ∃ σ : D.H, ∀ p ∈ T, (D.toEtalePi1 σ).app p.1 p.2 = α.app p.1 p.2 := by
  let V₀ : Subgroup D.H :=
    D.HL.subgroupOf D.H ⊓ (FibreAut.stabilizer _ T).comap D.toEtalePi1
  have hV₀ : IsOpen (V₀ : Set D.H) :=
    (D.isOpen_HL.preimage continuous_subtype_val).inter
      ((FibreAut.isOpen_stabilizer _ T).preimage D.continuous_toEtalePi1)
  let V := Level.ofOpen D V₀ hV₀ inf_le_left (fun s hs g => by
    refine ⟨(Subgroup.mem_subgroupOf).2 (D.conj_mem g g.2 s hs.1), ?_⟩
    show D.toEtalePi1 (g * s * g⁻¹) ∈ FibreAut.stabilizer _ T
    rw [map_mul, map_mul, D.toEtalePi1_eq_one_of_mem_S hs, mul_one,
      ← map_mul, mul_inv_cancel, map_one]
    exact (FibreAut.stabilizer _ T).one_mem)
  obtain ⟨σ, hσ⟩ := V.exists_fibreSmul_f₀ (α.app V.X V.f₀)
  refine ⟨σ, fun p hp => ?_⟩
  obtain ⟨m, hm⟩ := V.exists_hom p.1 p.2 (fun u hu h => by
    have h1 := (Level.ofOpen_conj_mem D hu h⁻¹).2 p hp
    rw [inv_inv, toEtalePi1_app] at h1
    conv_rhs => rw [← h1]
    rw [← fibreSmul_mul, ← fibreSmul_mul]
    congr 1
    group)
  rw [← hm, FibreAut.app_naturality, FibreAut.app_naturality, toEtalePi1_app, hσ]

instance : CompactSpace (D.H ⧸ GaloisPi1.kernel D.H D.S) := Quotient.compactSpace

/-- **Surjectivity** of `H ⧸ ⟨⟨S⟩⟩ → etalePi1 R A Ω`. -/
theorem pi1ToEtalePi1_surjective : Function.Surjective D.pi1ToEtalePi1 := by
  have hclosed : IsClosed (Set.range D.pi1ToEtalePi1) :=
    (isCompact_range D.continuous_pi1ToEtalePi1).isClosed
  intro α
  have hα : α ∈ closure (Set.range D.pi1ToEtalePi1) := by
    rw [mem_closure_iff_nhds]
    intro N hN
    rw [← map_mul_left_nhds_one α, Filter.mem_map] at hN
    obtain ⟨T, -, hT⟩ := (FibreAut.nhds_one_hasBasis _).mem_iff.1 hN
    obtain ⟨σ, hσ⟩ := D.exists_toEtalePi1_eq α T
    refine ⟨D.toEtalePi1 σ, ?_, ⟨(σ : D.H ⧸ GaloisPi1.kernel D.H D.S), rfl⟩⟩
    have hmem : α⁻¹ * D.toEtalePi1 σ ∈ FibreAut.stabilizer _ T := fun p hp => by
      rw [FibreAut.mul_app, hσ p hp, FibreAut.inv_app_app]
    have := hT hmem
    simpa using this
  rw [hclosed.closure_eq] at hα
  exact hα

/-- **The comparison theorem** (SGA 1, V.8.2, with a finite group action): the étale
fundamental group of the orbifold `[Spec R / A]` is isomorphic, as a profinite group, to
`H ⧸ ⟨⟨S⟩⟩`, the Galois group of the maximal extension of `L` unramified over `Spec R`, over the
function field of `Spec R / A`. The inverse is induced by the action `f ↦ σ ∘ f ∘ (X.act σ̄)⁻¹` of
`σ ∈ H` on fibres (`GaloisData.equivPi1_symm_mk_app`). -/
def equivPi1 : etalePi1 D.R D.A Ω ≃ₜ* GaloisPi1.pi1 D.H D.S D.isClosed_H :=
  let e : (D.H ⧸ GaloisPi1.kernel D.H D.S) ≃* etalePi1 D.R D.A Ω :=
    MulEquiv.ofBijective D.pi1ToEtalePi1
      ⟨D.pi1ToEtalePi1_injective, D.pi1ToEtalePi1_surjective⟩
  let e' : (D.H ⧸ GaloisPi1.kernel D.H D.S) ≃ₜ* etalePi1 D.R D.A Ω :=
    { e with
      continuous_toFun := D.continuous_pi1ToEtalePi1
      continuous_invFun :=
        D.continuous_pi1ToEtalePi1.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) }
  e'.symm

@[simp] lemma equivPi1_symm_mk_app (σ : D.H) (X : EquivEtale D.R D.A)
    (f : X.B →ₐ[D.R] Ω) :
    (D.equivPi1.symm (σ : D.H ⧸ GaloisPi1.kernel D.H D.S)).app X f = D.fibreSmul σ X f := rfl

end GaloisData

end

end Pi1.Orbifold
