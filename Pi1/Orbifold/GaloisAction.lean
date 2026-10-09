/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Orbifold.GaloisData
public import Pi1.RingTheory.UnramifiedValuation

/-!
# The Galois action on the fibres of equivariant finite étale covers

Let `D : GaloisData k t` (open subgroups `H_L ≤ H` of `Gal(Ω / k(t))`, `L = Ω^{H_L}`, `R` the
coordinate ring of the normalization of the `t`-line in `L`, `A = H ⧸ H_L`). An element `σ ∈ H`
acts on the fibre `X.B →ₐ[R] Ω` of an `A`-equivariant finite étale `R`-algebra `X` by
`f ↦ σ ∘ f ∘ (X.act σ̄)⁻¹` (`GaloisData.fibreSmul`); this is natural in `X` and defines a continuous
homomorphism `GaloisData.toEtalePi1 : H →* etalePi1 R A Ω`.

The inertia elements `S` act trivially (`GaloisData.fibreSmul_eq_self_of_mem_S`): for `σ ∈ H_L`
in the inertia group of a valuation subring `W ⊇ k[t]`, the maps `f` and `σ ∘ f` take values in
`W` and agree modulo its maximal ideal, hence agree since `X.B` is unramified over `R`.
Consequently `toEtalePi1` factors through `GaloisPi1.pi1 H S` (`GaloisData.pi1ToEtalePi1`).
-/

@[expose] public section

universe w v u

open CategoryTheory AffOrbicurve IntermediateField.algebraAdjoinAdjoin

namespace Pi1.Orbifold

noncomputable section

namespace FibreAut

variable {C : Type u} [Category.{v} C] {F : C ⥤ Type w}

/-- An automorphism of a fibre functor given by compatible bijections of the fibres. -/
def ofEquivs (e : ∀ c, F.obj c ≃ F.obj c)
    (h : ∀ {c d : C} (f : c ⟶ d) (x : F.obj c), e d (F.map f x) = F.map f (e c x)) :
    FibreAut F :=
  show Aut F from NatIso.ofComponents (fun c => (e c).toIso) (fun f => by ext x; exact h f x)

@[simp] lemma ofEquivs_app (e : ∀ c, F.obj c ≃ F.obj c)
    (h : ∀ {c d : C} (f : c ⟶ d) (x : F.obj c), e d (F.map f x) = F.map f (e c x)) (c : C)
    (x : F.obj c) : (ofEquivs e h).app c x = e c x := rfl

end FibreAut

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

lemma aut_apply_inv_apply (σ : Ω ≃ₐ[K₀ k t] Ω) (x : Ω) : σ (σ⁻¹ x) = x := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

lemma aut_inv_apply_apply (σ : Ω ≃ₐ[K₀ k t] Ω) (x : Ω) : σ⁻¹ (σ x) = x := by
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

/-- The stabilizer of an element of `Ω` is open in the Krull topology. -/
lemma isOpen_setOf_apply_eq [IsGalois (K₀ k t) Ω] (x : Ω) :
    IsOpen {σ : Ω ≃ₐ[K₀ k t] Ω | σ x = x} := by
  have : FiniteDimensional (K₀ k t) (IntermediateField.adjoin (K₀ k t) {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have hM : (IntermediateField.adjoin (K₀ k t) {x}).fixingSubgroup ≤
      MulAction.stabilizer (Ω ≃ₐ[K₀ k t] Ω) x :=
    fun σ hσ => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x
      (IntermediateField.mem_adjoin_simple_self _ x)
  exact Subgroup.isOpen_mono hM (IntermediateField.fixingSubgroup_isOpen _)

/-- An element of `Ω` integral over `k[t]` lies in every valuation subring containing `k` and
`t`. -/
lemma mem_of_isIntegral {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    (ht : t ∈ W) {x : Ω} (hx : IsIntegral (A₀ k t) x) : x ∈ W := by
  let Wk : Subalgebra k Ω := { W.toSubring with algebraMap_mem' := hk }
  have hle : A₀ k t ≤ Wk := Algebra.adjoin_le (Set.singleton_subset_iff.2 ht)
  let φ : A₀ k t →+* W := (Subalgebra.inclusion hle).toRingHom
  have hW : IsIntegral W x :=
    IsIntegral.map_of_comp_eq (T := W) φ (RingHom.id Ω) (RingHom.ext fun _ => rfl) hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hW
  rw [← hy]
  exact y.2

namespace GaloisData

variable (D : GaloisData k t)

lemma mk_eq_one_of_mem {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.HL) : (σ : D.A) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (by rwa [Subgroup.mem_subgroupOf])

/-- **The action of `σ ∈ H` on the fibre of `X`**: `f ↦ σ ∘ f ∘ (X.act σ̄)⁻¹`. -/
def fibreSmul (σ : D.H) (X : EquivEtale D.R D.A) (f : X.B →ₐ[D.R] Ω) : X.B →ₐ[D.R] Ω where
  toRingHom := ((σ : Ω ≃ₐ[K₀ k t] Ω) : Ω →+* Ω).comp
    (f.toRingHom.comp ((X.act (σ⁻¹ : D.H)).σ : X.B →+* X.B))
  commutes' r := by
    change (σ : Ω ≃ₐ[K₀ k t] Ω) (f ((X.act (σ⁻¹ : D.H)).σ (algebraMap D.R X.B r))) = _
    rw [(X.act _).map_algebraMap, X.act_a, AlgHom.commutes, algebraMap_smul]
    exact aut_apply_inv_apply _ _

lemma fibreSmul_apply (σ : D.H) (X : EquivEtale D.R D.A) (f : X.B →ₐ[D.R] Ω) (b : X.B) :
    D.fibreSmul σ X f b = (σ : Ω ≃ₐ[K₀ k t] Ω) (f ((X.act (σ⁻¹ : D.H)).σ b)) := rfl

lemma fibreSmul_one (X : EquivEtale D.R D.A) (f : X.B →ₐ[D.R] Ω) : D.fibreSmul 1 X f = f := by
  ext b
  simp [fibreSmul_apply]

lemma fibreSmul_mul (σ τ : D.H) (X : EquivEtale D.R D.A) (f : X.B →ₐ[D.R] Ω) :
    D.fibreSmul (σ * τ) X f = D.fibreSmul σ X (D.fibreSmul τ X f) := by
  ext b
  simp [fibreSmul_apply, mul_inv_rev, AlgEquiv.mul_apply]

lemma fibreSmul_comp (σ : D.H) {X Y : EquivEtale D.R D.A} (φ : X ⟶ Y) (f : X.B →ₐ[D.R] Ω) :
    D.fibreSmul σ Y (f.comp φ.f) = (D.fibreSmul σ X f).comp φ.f := by
  ext y
  simp only [fibreSmul_apply, AlgHom.comp_apply]
  rw [φ.f_act]

lemma fibreSmul_of_mem {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.HL) (X : EquivEtale D.R D.A)
    (f : X.B →ₐ[D.R] Ω) (b : X.B) :
    D.fibreSmul σ X f b = (σ : Ω ≃ₐ[K₀ k t] Ω) (f b) := by
  rw [fibreSmul_apply, QuotientGroup.mk_inv, D.mk_eq_one_of_mem hσ, inv_one, map_one]
  rfl

/-- **The action of `H` on the fibre functor**: a homomorphism `H →* etalePi1 R A Ω`. -/
def toEtalePi1 : D.H →* etalePi1 D.R D.A Ω where
  toFun σ := FibreAut.ofEquivs
    (fun X => ⟨D.fibreSmul σ X, D.fibreSmul σ⁻¹ X,
      fun f => by rw [← fibreSmul_mul, inv_mul_cancel, fibreSmul_one],
      fun f => by rw [← fibreSmul_mul, mul_inv_cancel, fibreSmul_one]⟩)
    (fun φ f => D.fibreSmul_comp σ φ f)
  map_one' := FibreAut.ext fun X f => D.fibreSmul_one X f
  map_mul' σ τ := FibreAut.ext fun X f => D.fibreSmul_mul σ τ X f

@[simp] lemma toEtalePi1_app (σ : D.H) (X : EquivEtale D.R D.A) (f : X.B →ₐ[D.R] Ω) :
    (D.toEtalePi1 σ).app X f = D.fibreSmul σ X f := rfl

/-- Two `R`-algebra maps out of a coded algebra agree if they agree on the generators. -/
lemma algHom_ext_levelRing {X : EquivEtale D.R D.A} {f g : X.B →ₐ[D.R] Ω}
    (h : ∀ i, f (Ideal.Quotient.mk X.I (MvPolynomial.X i)) =
      g (Ideal.Quotient.mk X.I (MvPolynomial.X i))) : f = g :=
  Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext h)

theorem continuous_toEtalePi1 [IsGalois (K₀ k t) Ω] : Continuous D.toEtalePi1 := by
  refine FibreAut.continuous_of_stabilizer _ _ fun T => ?_
  let V : Set (Ω ≃ₐ[K₀ k t] Ω) := (D.HL : Set (Ω ≃ₐ[K₀ k t] Ω)) ∩
    ⋂ p ∈ T, ⋂ i : Fin p.1.n,
      {σ | σ ((show p.1.B →ₐ[D.R] Ω from p.2) (Ideal.Quotient.mk p.1.I (MvPolynomial.X i))) =
        (show p.1.B →ₐ[D.R] Ω from p.2) (Ideal.Quotient.mk p.1.I (MvPolynomial.X i))}
  have hV : IsOpen V := D.isOpen_HL.inter
    (isOpen_biInter_finset fun p _ => isOpen_iInter_of_finite fun i => isOpen_setOf_apply_eq _)
  refine Filter.mem_of_superset ((hV.preimage continuous_subtype_val).mem_nhds ?_) ?_
  · refine ⟨D.HL.one_mem, ?_⟩
    simp only [Set.mem_iInter]
    intro p _ i
    rfl
  · intro σ hσ p hp
    obtain ⟨hσL, hσT⟩ := hσ
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hσT
    change D.fibreSmul σ p.1 p.2 = p.2
    refine D.algHom_ext_levelRing fun i => ?_
    rw [fibreSmul_of_mem D hσL]
    exact hσT p hp i

/-- The values of fibre elements are integral over `k[t]`. -/
lemma isIntegral_fibre (X : EquivEtale D.R D.A) (f : X.B →ₐ[D.R] Ω) (b : X.B) :
    IsIntegral (A₀ k t) (f b) := by
  letI := X.finite
  have hb : IsIntegral D.R (f b) := ((Algebra.IsIntegral.of_finite D.R X.B).isIntegral b).map f
  exact isIntegral_trans (A := D.R) _ hb

/-- **Inertia acts trivially on fibres**: an element of `S` fixes every fibre element. -/
theorem fibreSmul_eq_self_of_mem_S {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S)
    (X : EquivEtale D.R D.A) (f : X.B →ₐ[D.R] Ω) : D.fibreSmul σ X f = f := by
  obtain ⟨hσL, W, hk, ht, hin⟩ := hσ
  letI := X.etale
  letI := X.finite
  have hW : ∀ b, f b ∈ W := fun b => mem_of_isIntegral hk ht (D.isIntegral_fibre X f b)
  have hsub : ∀ b, (σ : Ω ≃ₐ[K₀ k t] Ω) (f b) - f b ∈ W := by
    intro b
    exact (W.valuation_le_one_iff _).1 ((hin _ (hW b)).le)
  refine (Algebra.FormallyUnramified.algHom_eq_of_valuation W _ _ ?_ hW ?_).trans rfl
  · intro b
    rw [fibreSmul_of_mem D hσL]
    have := W.add_mem _ _ (hsub b) (hW b)
    rwa [sub_add_cancel] at this
  · intro b
    rw [fibreSmul_of_mem D hσL]
    exact hin _ (hW b)

lemma toEtalePi1_eq_one_of_mem_S {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S) :
    D.toEtalePi1 σ = 1 :=
  FibreAut.ext fun X f => D.fibreSmul_eq_self_of_mem_S hσ X f

lemma mem_H_of_mem_S {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ D.S) : σ ∈ D.H := D.le hσ.1

variable [IsGalois (K₀ k t) Ω]

/-- **The inertia subgroup acts trivially**: the closed normal subgroup of `H` generated by `S`
lies in the kernel of `H → etalePi1 R A Ω`. -/
theorem kernel_le_ker : GaloisPi1.kernel D.H D.S ≤ D.toEtalePi1.ker := by
  intro x hx
  let K : Subgroup (Ω ≃ₐ[K₀ k t] Ω) := D.toEtalePi1.ker.map D.H.subtype
  have hKc : IsClosed (K : Set (Ω ≃ₐ[K₀ k t] Ω)) := by
    have hker : IsClosed (D.toEtalePi1.ker : Set D.H) :=
      isClosed_singleton.preimage D.continuous_toEtalePi1
    simp only [K, Subgroup.coe_map, Subgroup.coe_subtype]
    exact D.isClosed_H.isClosedEmbedding_subtypeVal.isClosedMap _ hker
  have hle : GaloisPi1.ambientKernel D.H D.S ≤ K := by
    refine Subgroup.topologicalClosure_minimal _ ?_ hKc
    rw [Subgroup.closure_le]
    rintro _ ⟨h, hh, s, hs, rfl⟩
    refine ⟨⟨h, hh⟩ * ⟨s, D.mem_H_of_mem_S hs⟩ * ⟨h, hh⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul,
      D.toEtalePi1_eq_one_of_mem_S (σ := ⟨s, _⟩) hs,
      mul_one, ← map_mul, mul_inv_cancel, map_one]
  obtain ⟨y, hy, hyx⟩ := hle hx
  rwa [← Subtype.ext hyx]

/-- **The map `GaloisPi1.pi1 H S → etalePi1 R A Ω`** induced by the action of `H` on fibres. -/
def pi1ToEtalePi1 : D.H ⧸ GaloisPi1.kernel D.H D.S →* etalePi1 D.R D.A Ω :=
  QuotientGroup.lift _ D.toEtalePi1 D.kernel_le_ker

@[simp] lemma pi1ToEtalePi1_mk (σ : D.H) :
    D.pi1ToEtalePi1 (σ : D.H ⧸ GaloisPi1.kernel D.H D.S) = D.toEtalePi1 σ := rfl

theorem continuous_pi1ToEtalePi1 : Continuous D.pi1ToEtalePi1 :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 D.continuous_toEtalePi1

end GaloisData

end

end Pi1.Orbifold
