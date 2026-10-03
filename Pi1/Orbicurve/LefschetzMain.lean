module

public import Pi1.Orbicurve.Descent
public import Pi1.Orbicurve.EmbedComplex
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.Polynomial.Subring

/-!
# [CanLift], Proposition 2.7 over any field of characteristic `0` from the case `k = ℂ`

`AffOrbicurve.canLift27_of_complex`: if for every elliptic curve `E / ℂ` with non-exceptional
`j`-invariant `(E ∖ {0}) / {±1}` is the `ℂ`-core of `E ∖ {0}`, then the same holds over every
field of characteristic `0` (`CanLift27.{0}`). The proof (Lefschetz principle):

* `CanLift27` is equivalent to `CoreStar` (uniqueness of morphisms from covers of `E ∖ {0}` to
  `(E ∖ {0}) / {±1}`, `isCoreOf_iff_coreStar`);
* `CoreStar` descends along field embeddings (`coreStar_of_map`), in particular from `ℂ` to any
  countable algebraically closed field (`nonempty_ringHom_complex`) and from `k̄` to `k`;
* over an algebraically closed field `K`, the data of a violation of `CoreStar` are defined over a
  countable algebraically closed subfield (`eq_of_descended`).
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial WeierstrassCurve

namespace AffOrbicurve

section JMap

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω]

/-- An embedding of `K(E_K)` restricts to an embedding of `k(E)` with the same coordinates. -/
lemma exists_j_of_map (E : WeierstrassCurve k) (E' : WeierstrassCurve K)
    (hE : E.map (algebraMap k K) = E') (j : E'.toAffine.FunctionField →ₐ[K] Ω) :
    ∃ j₀ : E.toAffine.FunctionField →ₐ[k] Ω, tE j₀ = tE j ∧ yE j₀ = yE j := by
  subst hE
  refine ⟨{ (j.toRingHom.comp (ffMap (algebraMap k K) E)) with
      commutes' := fun c => by
        change j (ffMap (algebraMap k K) E (algebraMap k _ c)) = algebraMap k Ω c
        rw [IsScalarTower.algebraMap_apply k K Ω]
        have : algebraMap k E.toAffine.FunctionField c =
            algebraMap E.toAffine.CoordinateRing _ (algebraMap k _ c) := rfl
        rw [this, ffMap_algebraMap]
        have h2 : Affine.CoordinateRing.map E.toAffine (algebraMap k K) (algebraMap k _ c) =
            algebraMap K (E.map (algebraMap k K)).toAffine.CoordinateRing (algebraMap k K c) := by
          change Affine.CoordinateRing.map E.toAffine (algebraMap k K) (Affine.CoordinateRing.mk _ (C (C c))) = _
          rw [Affine.CoordinateRing.map_mk]
          simp; rfl
        rw [h2, ← IsScalarTower.algebraMap_apply, AlgHom.commutes] }, ?_, ?_⟩
  · change j (ffMap (algebraMap k K) E (ellX E)) = _
    rw [ffMap_ellX]; rfl
  · change j (ffMap (algebraMap k K) E (ellY E)) = _
    rw [ffMap_ellY]; rfl

end JMap

section Countable

open Cardinal

/-- **Countable algebraically closed subfields**: every finite subset of an algebraically closed
field of characteristic `0` lies in a countable algebraically closed subfield. -/
lemma exists_algClosed_countable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Set K) (hS : S.Finite) :
    ∃ L₀ : Subfield K, IsAlgClosed L₀ ∧ Countable L₀ ∧ S ⊆ L₀ := by
  let F := Subfield.closure S
  have hF : #F ≤ ℵ₀ := by
    refine (Subfield.cardinalMk_closure_le_max S).trans (max_le ?_ le_rfl)
    exact le_of_lt (Cardinal.lt_aleph0_iff_set_finite.mpr hS)
  let A := algebraicClosure F K
  haveI : IsAlgClosed A := IsAlgClosure.isAlgClosed F
  have hA : #A ≤ ℵ₀ := (Algebra.IsAlgebraic.cardinalMk_le_max F A).trans (max_le hF le_rfl)
  refine ⟨A.toSubfield, inferInstanceAs (IsAlgClosed A), ?_, ?_⟩
  · have : Countable A := Cardinal.mk_le_aleph0_iff.mp hA
    exact this
  · intro x hx
    have hxF : x ∈ F := Subfield.subset_closure hx
    exact (algebraicClosure F K).algebraMap_mem ⟨x, hxF⟩

end Countable

end AffOrbicurve
