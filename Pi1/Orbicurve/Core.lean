/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.FiniteType

/-!
# Affine orbicurves and their cores

This file sets up the notion of *core* of a hyperbolic orbicurve, following
S. Mochizuki, *The absolute anabelian geometry of canonical curves* ([CanLift]), §2
(and *Correspondences on hyperbolic curves*, §3).

## Orbicurves

Let `k` be a field of characteristic zero. [CanLift], Definition 2.2, calls an *orbicurve*
over `k` a smooth, geometrically connected, generically scheme-like algebraic stack of
dimension one and of finite type over `k`. The objects of the categories `Loc_k(X)`,
`\overline{Loc}_k(X)` of [CanLift], §2 are the (connected, but not necessarily geometrically
connected) generically scheme-like stacks that are finite étale over, or finite étale
quotients of objects finite étale over, a hyperbolic orbicurve `X`.

In characteristic zero such a stack `Y` is determined by its coarse moduli space `Y_crs`
(a smooth connected curve over `k`) together with the orders `m(v) ≥ 1` of the stabilizers
at the closed points `v` of `Y_crs` (finitely many of which are `> 1`): `Y` is the root stack
of `Y_crs` extracting an `m(v)`-th root at each `v`. When `X` is not proper (e.g. a
once-punctured elliptic curve), every object of `\overline{Loc}_k(X)` is not proper
(cusps pull back to cusps under finite étale morphisms), so its coarse space is affine:
`Y_crs = Spec A` for a Dedekind domain `A` of finite type over `k` (which is not a field).
This is the structure `AffOrbicurve k`: the coordinate ring `A` of the coarse space and the
multiplicity function `mult` on the maximal ideals of `A`.

## Finite étale morphisms

A morphism `Y → C` of such stacks is determined by the induced morphism of coarse spaces
(the stacks are generically scheme-like, so the 2-category of such stacks is equivalent to a
1-category, cf. [CanLift], §2). A morphism of coarse spaces `f : Y_crs → C_crs`, i.e. an
injective `k`-algebra map `A_C → A_Y` with `A_Y` integral over `A_C` (a finite morphism of
curves), lifts to a finite étale morphism of the root stacks if and only if, at every
closed point `w` of `Y_crs` over `v`,

  `e(w | v) · m_Y(w) = m_C(v)`,

where `e(w | v)` is the ramification index (local computation: in the charts
`[Spec k[s] / μ_m]`, the map `s ↦ u^{m_C/m_Y}` is étale exactly when `e = m_C / m_Y`; in
characteristic `0` all ramification is tame and the residue field extensions are separable).
This is `AffOrbicurve.Hom`.

## Cores

Following [CanLift], Definition 2.1 and Remark 2.1.1:

* `Y ∈ \overline{Loc}_k(X)` (`AffOrbicurve.LocBar X Y`): there is `Z` with finite étale
  morphisms `Z → X` and `Z → Y` (`Y` is a finite étale quotient of an object `Z` of
  `Loc_k(X)`);
* `C` is **the `k`-core of `X`** (`AffOrbicurve.IsCoreOf X C`): `C` is a terminal object of
  `\overline{Loc}_k(X)`, i.e. `C ∈ \overline{Loc}_k(X)` and every object of
  `\overline{Loc}_k(X)` admits exactly one (finite étale) morphism to `C`;
* `X` is **`k`-arithmetic** if `\overline{Loc}_k(X)` has no terminal object.

Only connected objects are considered; this does not change the notion of terminal object
(a morphism from a finite disjoint union is a family of morphisms from the components).

The definitions make sense over any field; they carry their intended meaning in
characteristic zero, to which [CanLift] restricts.
-/

@[expose] public section

universe u

open Ideal

/-- **An affine orbicurve** over `k` (in characteristic zero: a connected, smooth,
generically scheme-like algebraic stack of dimension one and of finite type over `k` whose
coarse moduli space is affine): the coordinate ring `A` of the coarse moduli space, a
Dedekind domain of finite type over `k` which is not a field, together with the orders
`mult v ≥ 1` of the stabilizers at the maximal ideals `v` of `A`, finitely many of which are
`≠ 1`. (The values of `mult` at non-maximal ideals play no role.) -/
structure AffOrbicurve (k : Type u) [Field k] : Type (u + 1) where
  /-- The coordinate ring of the coarse moduli space. -/
  A : Type u
  [commRing : CommRing A]
  [isDomain : IsDomain A]
  [algebra : Algebra k A]
  [isDedekindDomain : IsDedekindDomain A]
  [finiteType : Algebra.FiniteType k A]
  /-- The coarse moduli space is a curve (`A` has dimension one). -/
  not_isField : ¬ IsField A
  /-- The orders of the stabilizers at the closed points. -/
  mult : Ideal A → ℕ
  /-- The stabilizer orders are positive. -/
  mult_pos : ∀ v : Ideal A, v.IsMaximal → 0 < mult v
  /-- Only finitely many closed points have a nontrivial stabilizer. -/
  finite_mult : {v : Ideal A | v.IsMaximal ∧ mult v ≠ 1}.Finite

namespace AffOrbicurve

attribute [instance] commRing isDomain algebra isDedekindDomain finiteType

variable {k : Type u} [Field k]

/-- **A finite étale morphism** `Y → C` of affine orbicurves: an injective `k`-algebra map
`f : A_C → A_Y` of coordinate rings of the coarse spaces, with `A_Y` integral over `A_C`
(the morphism of coarse spaces is finite), such that at every maximal ideal `w` of `A_Y`,
lying over `v = f⁻¹(w)`, the ramification index satisfies `e(w | v) · m_Y(w) = m_C(v)`
(the morphism of root stacks is étale). -/
structure Hom (Y C : AffOrbicurve k) where
  /-- The map of coordinate rings of the coarse spaces. -/
  f : C.A →ₐ[k] Y.A
  /-- The map is injective (the morphism is dominant). -/
  injective : Function.Injective f
  /-- `A_Y` is integral over `A_C` (the morphism of coarse spaces is finite). -/
  isIntegral : f.toRingHom.IsIntegral
  /-- The multiplicity condition: `e(w | v) · m_Y(w) = m_C(v)`. -/
  etale : ∀ w : Ideal Y.A, w.IsMaximal →
    (letI := f.toRingHom.toAlgebra; w.ramificationIdx C.A) * Y.mult w = C.mult (w.comap f)

/-- Morphisms are determined by their map of coordinate rings. -/
@[ext] lemma Hom.ext {Y C : AffOrbicurve k} {φ ψ : Hom Y C} (h : φ.f = ψ.f) : φ = ψ := by
  cases φ; cases ψ; cases h; rfl

/-- `Y` belongs to `\overline{Loc}_k(X)` ([CanLift], §2): `Y` is a finite étale quotient of
an object `Z` finite étale over `X`. -/
def LocBar (X Y : AffOrbicurve k) : Prop :=
  ∃ Z : AffOrbicurve k, Nonempty (Hom Z X) ∧ Nonempty (Hom Z Y)

/-- **`C` is the `k`-core of `X`** ([CanLift], Definition 2.1, Remark 2.1.1): `C` is a
terminal object of `\overline{Loc}_k(X)`. -/
def IsCoreOf (X C : AffOrbicurve k) : Prop :=
  LocBar X C ∧ ∀ Y : AffOrbicurve k, LocBar X Y → Nonempty (Hom Y C) ∧ Subsingleton (Hom Y C)

/-- `X` is a **`k`-core** ([CanLift], Definition 2.1(ii)): `X` is terminal in
`\overline{Loc}_k(X)`. -/
def IsCore (X : AffOrbicurve k) : Prop := IsCoreOf X X

/-- `X` is **`k`-arithmetic** ([CanLift], Definition 2.1(i), Remark 2.1.1):
`\overline{Loc}_k(X)` has no terminal object. -/
def IsArithmetic (X : AffOrbicurve k) : Prop := ¬ ∃ C : AffOrbicurve k, IsCoreOf X C

end AffOrbicurve
