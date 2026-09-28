module

public import Pi1.Orbicurve.Morphisms
public import Pi1.Orbicurve.IntegralClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Affine orbicurves with function field inside a fixed field

Let `Ω` be a field over `k`, `t ∈ Ω` transcendental over `k`, `A₀ = k[t] ⊆ Ω` and
`K₀ = k(t) ⊆ Ω`. For an intermediate field `K₀ ⊆ L ⊆ Ω`, finite and separable over `K₀`, the
integral closure `coordRing k t L` of `k[t]` in `L` is the coordinate ring of the normalization of the
`t`-line in `L` (a smooth affine curve with function field `L`). With stabilizer orders `m` this
is the affine orbicurve `AffOrbicurve.ofSubfield t L m`.

For `L ⊆ L'` the inclusion induces `ringMap : coordRing k t L → coordRing k t L'` (injective and integral), and
`AffOrbicurve.homOfLE` is the resulting finite étale morphism when the multiplicity condition
holds.
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω)

/-- `k[t] ⊆ Ω`. -/
abbrev A₀ (k : Type u) [Field k] [Algebra k Ω] (t : Ω) : Subalgebra k Ω := Algebra.adjoin k {t}

/-- `k(t) ⊆ Ω`. -/
abbrev K₀ (k : Type u) [Field k] [Algebra k Ω] (t : Ω) : IntermediateField k Ω := IntermediateField.adjoin k {t}

variable {t} (ht : Transcendental k t)

include ht in
lemma isPrincipalIdealRing_A₀ : IsPrincipalIdealRing (A₀ k t) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental k t ht).toRingHom
    (Polynomial.algEquivOfTranscendental k t ht).surjective

include ht in
lemma isDedekindDomain_A₀ : IsDedekindDomain (A₀ k t) :=
  haveI := isPrincipalIdealRing_A₀ ht
  inferInstance

include ht in
lemma finiteType_A₀ : Algebra.FiniteType k (A₀ k t) :=
  Algebra.FiniteType.equiv inferInstance (Polynomial.algEquivOfTranscendental k t ht)

include ht in
lemma not_isField_A₀ : ¬ IsField (A₀ k t) := by
  intro h
  exact Polynomial.not_isField k
    (MulEquiv.isField h (Polynomial.algEquivOfTranscendental k t ht).toMulEquiv)

variable (t)

/-- **The coordinate ring** of the normalization of the `t`-line in `L`: the integral closure of
`k[t]` in `L`. -/
abbrev coordRing (k : Type u) [Field k] [Algebra k Ω] (t : Ω) (L : IntermediateField (K₀ k t) Ω) : Subalgebra (A₀ k t) L := integralClosure (A₀ k t) L

section Instances

variable (L : IntermediateField (K₀ k t) Ω)

instance : IsScalarTower k (A₀ k t) L := IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : FaithfulSMul (A₀ k t) L := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro a b h
  exact Subtype.ext (congrArg (fun x : L => (x : Ω)) h)

end Instances

section OfSubfield

variable (L : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) L]
  [Algebra.IsSeparable (K₀ k t) L]

include ht in
lemma isDedekindDomain_ring : IsDedekindDomain (coordRing k t L) :=
  haveI := isDedekindDomain_A₀ ht
  integralClosure.isDedekindDomain (A₀ k t) (K₀ k t) L

include ht in
lemma finite_ring : Module.Finite (A₀ k t) (coordRing k t L) :=
  haveI := isDedekindDomain_A₀ ht
  IsIntegralClosure.finite (A₀ k t) (K₀ k t) L (coordRing k t L)

include ht in
lemma finiteType_ring : Algebra.FiniteType k (coordRing k t L) :=
  haveI := finite_ring t ht L
  haveI := finiteType_A₀ ht
  Algebra.FiniteType.trans (S := A₀ k t) inferInstance inferInstance

omit [FiniteDimensional (K₀ k t) L] [Algebra.IsSeparable (K₀ k t) L] in
include ht in
lemma not_isField_ring : ¬ IsField (coordRing k t L) := by
  intro hC
  refine not_isField_A₀ ht (isField_of_isIntegral_of_isField ?_ hC)
  intro a b hab
  have := congrArg (fun c : coordRing k t L => ((c : L) : Ω)) hab
  exact Subtype.val_injective (by simpa using this)

/-- **The affine orbicurve with function field `L`** (coarse space the normalization of the
`t`-line in `L`) and stabilizer orders `m`. -/
noncomputable def ofSubfield (m : Ideal (coordRing k t L) → ℕ) (m_pos : ∀ v, v.IsMaximal → 0 < m v)
    (m_fin : {v : Ideal (coordRing k t L) | v.IsMaximal ∧ m v ≠ 1}.Finite) : AffOrbicurve k :=
  letI := isDedekindDomain_ring t ht L
  letI := finiteType_ring t ht L
  { A := coordRing k t L
    not_isField := not_isField_ring t ht L
    mult := m
    mult_pos := m_pos
    finite_mult := m_fin }

/-- **The normalization of the `t`-line in `L`, as a scheme** (all stabilizers trivial). -/
noncomputable def ofSubfieldScheme : AffOrbicurve k :=
  ofSubfield t ht L (fun _ => 1) (fun _ _ => Nat.one_pos) (by simp)

end OfSubfield

section Map

variable {L L' : IntermediateField (K₀ k t) Ω} (h : L ≤ L')

/-- The inclusion `coordRing k t L → coordRing k t L'` for `L ⊆ L'`. -/
noncomputable def ringMap : coordRing k t L →ₐ[k] coordRing k t L' where
  toFun a := ⟨IntermediateField.inclusion h a, by
    have := a.2
    rw [mem_integralClosure_iff] at this ⊢
    exact this.map (IntermediateField.inclusion h |>.restrictScalars (A₀ k t))⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] lemma coe_ringMap (a : coordRing k t L) : ((ringMap t h a : L') : Ω) = ((a : L) : Ω) := rfl

lemma ringMap_injective : Function.Injective (ringMap t h) := by
  intro a b hab
  have := congrArg (fun c : coordRing k t L' => ((c : L') : Ω)) hab
  simp only [coe_ringMap] at this
  exact Subtype.val_injective (Subtype.val_injective this)

lemma ringMap_isIntegral : (ringMap t h).toRingHom.IsIntegral := by
  intro b
  obtain ⟨p, hp, hpb⟩ := integralClosure.isIntegral (R := A₀ k t) (A := L') b
  refine ⟨p.map (algebraMap (A₀ k t) (coordRing k t L)), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have : (ringMap t h).toRingHom.comp (algebraMap (A₀ k t) (coordRing k t L)) =
      algebraMap (A₀ k t) (coordRing k t L') := RingHom.ext fun _ => rfl
  rw [this]
  exact hpb

end Map

end AffOrbicurve
