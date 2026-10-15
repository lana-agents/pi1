/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Pi1.FundamentalGroup.Functoriality

/-!
# Extension of algebraically closed base fields: surjectivity on `π₁ᵉᵗ`

Let `k` be an algebraically closed field and `Ω / k` any field extension. Then

* `Algebra.TensorProduct.isDomain_of_isAlgClosed`: `Ω ⊗[k] K` is a domain for every field
  extension `K / k` (proved with the Nullstellensatz: points `A → k` of finitely generated
  `k`-subalgebras `A ⊆ Ω` separate elements);
* `AlgebraicGeometry.geometricallyConnected_Spec_of_isAlgClosed`: `Spec Ω ⟶ Spec k` is
  geometrically connected;
* `AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_surjective_of_isAlgClosed`: for every
  connected `k`-scheme `X`, the base change `X_Ω` is connected and
  `π₁ᵉᵗ(X_Ω) → π₁ᵉᵗ(X)` is surjective.

This is the easy half of the invariance of `π₁ᵉᵗ` under extension of algebraically closed fields
(SGA 1 X.1.8 in characteristic `0`); injectivity, i.e. that every finite étale cover of `X_Ω`
comes from `X`, is not proved here.
-/

@[expose] public section

universe u

open TensorProduct

noncomputable section

section Nullstellensatz

variable {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- **Nullstellensatz**: a non-zero element of a finitely generated domain over an algebraically
closed field `k` does not vanish at some `k`-point. -/
theorem Algebra.exists_algHom_ne_zero_of_isAlgClosed {d : A} (hd : d ≠ 0) :
    ∃ χ : A →ₐ[k] k, χ d ≠ 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hj : d ∉ (⊥ : Ideal A).jacobson := by
    rw [← Ideal.radical_eq_jacobson, Ideal.isPrime_bot.radical]
    simpa using hd
  obtain ⟨m, hm, hdm⟩ : ∃ m : Ideal A, m.IsMaximal ∧ d ∉ m := by
    simp only [Ideal.jacobson, Submodule.mem_sInf, Set.mem_setOf_eq, bot_le, true_and,
      not_forall] at hj
    obtain ⟨m, hm, hdm⟩ := hj
    exact ⟨m, hm, hdm⟩
  letI := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hbij : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] A ⧸ m := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hbij
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), fun h ↦ hdm ?_⟩
  have : Ideal.Quotient.mk m d = 0 := by
    simpa using congr(e $h)
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

/-- The evaluation `A ⊗[k] K → K` at a `k`-point `χ : A → k`. -/
def Algebra.TensorProduct.evalPoint {K : Type*} [Field K] [Algebra k K] (χ : A →ₐ[k] k) :
    A ⊗[k] K →ₐ[k] K :=
  (Algebra.TensorProduct.lid k K).toAlgHom.comp (Algebra.TensorProduct.map χ (AlgHom.id k K))

omit [IsAlgClosed k] [IsDomain A] [Algebra.FiniteType k A] in
lemma Algebra.TensorProduct.evalPoint_eq_zero_iff {K : Type*} [Field K] [Algebra k K]
    {ι : Type*} (b : Module.Basis ι k K) (χ : A →ₐ[k] k) (x : A ⊗[k] K) :
    evalPoint χ x = 0 ↔ ∀ i, χ ((Algebra.TensorProduct.basis A b).repr x i) = 0 := by
  classical
  set B := Algebra.TensorProduct.basis A b
  have hx (x : A ⊗[k] K) : evalPoint χ x =
      b.repr.symm (Finsupp.mapRange χ (map_zero χ) (B.repr x)) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      have : Finsupp.mapRange χ (map_zero χ) (B.repr (a ⊗ₜ c)) = χ a • b.repr c := by
        ext i
        simp [B]
      rw [this, map_smul, b.repr.symm_apply_apply]
      simp [evalPoint]
    | add x y hx hy =>
      rw [map_add, hx, hy, map_add, Finsupp.mapRange_add (map_add χ), map_add]
  rw [hx, LinearEquiv.map_eq_zero_iff, Finsupp.ext_iff]
  simp

end Nullstellensatz

section Domain

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- `A ⊗[k] K` is a domain for a finitely generated domain `A` and a field `K` over an
algebraically closed field `k`. -/
theorem Algebra.TensorProduct.isDomain_of_finiteType {A K : Type u} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra k K] : IsDomain (A ⊗[k] K) := by
  classical
  let b := Module.Free.chooseBasis k K
  set B := Algebra.TensorProduct.basis A b
  haveI : Nonempty (Module.Free.ChooseBasisIndex k K) := b.index_nonempty
  haveI : Nontrivial (A ⊗[k] K) := B.repr.toEquiv.nontrivial
  suffices NoZeroDivisors (A ⊗[k] K) from NoZeroDivisors.to_isDomain _
  refine ⟨fun {x y} hxy ↦ ?_⟩
  by_contra! h
  obtain ⟨i, hi⟩ : ∃ i, B.repr x i ≠ 0 := by
    by_contra! H
    exact h.1 (B.repr.injective (by ext i; simp [H i]))
  obtain ⟨j, hj⟩ : ∃ j, B.repr y j ≠ 0 := by
    by_contra! H
    exact h.2 (B.repr.injective (by ext j; simp [H j]))
  obtain ⟨χ, hχ⟩ := Algebra.exists_algHom_ne_zero_of_isAlgClosed (k := k) (mul_ne_zero hi hj)
  rw [map_mul] at hχ
  have h0 : evalPoint χ x * evalPoint χ y = 0 := by rw [← map_mul, hxy, map_zero]
  rcases mul_eq_zero.mp h0 with h0 | h0
  · exact left_ne_zero_of_mul hχ ((evalPoint_eq_zero_iff b χ x).mp h0 i)
  · exact right_ne_zero_of_mul hχ ((evalPoint_eq_zero_iff b χ y).mp h0 j)

variable {Ω K : Type u} [Field Ω] [Algebra k Ω] [Field K] [Algebra k K]

/-- The inclusion `A ⊗[k] K → Ω ⊗[k] K` for a subalgebra `A ⊆ Ω`. -/
abbrev Subalgebra.inclTensor (A : Subalgebra k Ω) (K : Type u) [Field K] [Algebra k K] :
    A ⊗[k] K →ₐ[k] Ω ⊗[k] K :=
  Algebra.TensorProduct.map A.val (AlgHom.id k K)

omit [IsAlgClosed k] in
lemma Subalgebra.range_inclTensor_mono {A A' : Subalgebra k Ω} (h : A ≤ A') :
    Set.range (A.inclTensor K) ⊆ Set.range (A'.inclTensor K) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id k K) x, ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

omit [IsAlgClosed k] in
lemma Subalgebra.inclTensor_injective (A : Subalgebra k Ω) :
    Function.Injective (A.inclTensor K) := by
  have : Function.Injective (LinearMap.rTensor K (A.val.toLinearMap : A →ₗ[k] Ω)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  convert this using 1
  funext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [IsAlgClosed k] in
/-- Every element of `Ω ⊗[k] K` comes from `k[s] ⊗[k] K` for a finite set `s ⊆ Ω`. -/
lemma exists_finset_mem_range_inclTensor (x : Ω ⊗[k] K) :
    ∃ s : Finset Ω, x ∈ Set.range ((Algebra.adjoin k (s : Set Ω)).inclTensor K) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨∅, 0, map_zero _⟩
  | tmul ω c =>
    exact ⟨{ω}, ⟨ω, Algebra.subset_adjoin (by simp)⟩ ⊗ₜ c, rfl⟩
  | add x y hx hy =>
    obtain ⟨s, x', rfl⟩ := hx
    obtain ⟨t, y', rfl⟩ := hy
    obtain ⟨x'', hx''⟩ := Subalgebra.range_inclTensor_mono (K := K)
      (Algebra.adjoin_mono (s := (s : Set Ω)) (t := ((s ∪ t : Finset Ω) : Set Ω)) (by simp))
      ⟨x', rfl⟩
    obtain ⟨y'', hy''⟩ := Subalgebra.range_inclTensor_mono (K := K)
      (Algebra.adjoin_mono (s := (t : Set Ω)) (t := ((s ∪ t : Finset Ω) : Set Ω)) (by simp))
      ⟨y', rfl⟩
    exact ⟨s ∪ t, x'' + y'', by rw [map_add, hx'', hy'']⟩

/-- **`Ω ⊗[k] K` is a domain** for field extensions `Ω`, `K` of an algebraically closed field
`k`. -/
theorem Algebra.TensorProduct.isDomain_of_isAlgClosed : IsDomain (Ω ⊗[k] K) := by
  classical
  let b := Module.Free.chooseBasis k K
  haveI : Nonempty (Module.Free.ChooseBasisIndex k K) := b.index_nonempty
  haveI : Nontrivial (Ω ⊗[k] K) := (Algebra.TensorProduct.basis Ω b).repr.toEquiv.nontrivial
  suffices NoZeroDivisors (Ω ⊗[k] K) from NoZeroDivisors.to_isDomain _
  refine ⟨fun {x y} hxy ↦ ?_⟩
  obtain ⟨s, x', rfl⟩ := exists_finset_mem_range_inclTensor (K := K) x
  obtain ⟨t, y', rfl⟩ := exists_finset_mem_range_inclTensor (K := K) y
  let A := Algebra.adjoin k ((s ∪ t : Finset Ω) : Set Ω)
  obtain ⟨x'', hx''⟩ := Subalgebra.range_inclTensor_mono (K := K) (A' := A)
    (Algebra.adjoin_mono (by simp)) ⟨x', rfl⟩
  obtain ⟨y'', hy''⟩ := Subalgebra.range_inclTensor_mono (K := K) (A' := A)
    (Algebra.adjoin_mono (by simp)) ⟨y', rfl⟩
  rw [← hx'', ← hy''] at hxy ⊢
  haveI : Algebra.FiniteType k A :=
    (Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset _)
  haveI : IsDomain (A ⊗[k] K) := isDomain_of_finiteType
  rw [← map_mul, ← map_zero (A.inclTensor K)] at hxy
  rcases mul_eq_zero.mp (A.inclTensor_injective hxy) with h | h
  · exact .inl (by rw [h, map_zero])
  · exact .inr (by rw [h, map_zero])

end Domain

end

namespace AlgebraicGeometry

open CategoryTheory Limits

/-- **`Spec Ω ⟶ Spec k` is geometrically connected** for an algebraically closed field `k` and
any field extension `Ω / k`. -/
theorem geometricallyConnected_Spec_of_isAlgClosed (k Ω : Type u) [Field k] [IsAlgClosed k]
    [Field Ω] [Algebra k Ω] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  haveI : IsDomain (Ω ⊗[k] K) := Algebra.TensorProduct.isDomain_of_isAlgClosed
  haveI : IrreducibleSpace (Spec (.of (Ω ⊗[k] K))) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (Ω ⊗[k] K)))
  haveI : ConnectedSpace (Spec (.of (Ω ⊗[k] K))) := inferInstance
  exact ((pullbackSpecIso k Ω K).hom.homeomorph.connectedSpace_iff).mpr this

namespace FiniteEtale

/-- **Surjectivity of `π₁ᵉᵗ(X_Ω) → π₁ᵉᵗ(X)` for an extension `Ω / k` of an algebraically closed
field** (the easy half of SGA 1 X.1.8): for a connected `k`-scheme `X`, the base change
`X_Ω = X ×_k Ω` is connected and the projection `X_Ω ⟶ X` induces a surjection on étale
fundamental groups, at every geometric point `ξ` of `X_Ω`. -/
theorem fundamentalGroupMap_surjective_of_isAlgClosed {k Ω : Type u} [Field k] [IsAlgClosed k]
    [Field Ω] [Algebra k Ω] {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of k))
    {L : Type u} [Field L] [IsSepClosed L]
    (ξ : Spec (.of L) ⟶ Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) :
    ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) ∧
      Function.Surjective (fundamentalGroupMap
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) (rfl :
          ξ ≫ Limits.pullback.fst _ _ = _)) := by
  haveI := geometricallyConnected_Spec_of_isAlgClosed k Ω
  exact ⟨inferInstance, fundamentalGroupMap_surjective_of_geometricallyConnected _ rfl⟩

end FiniteEtale

end AlgebraicGeometry
