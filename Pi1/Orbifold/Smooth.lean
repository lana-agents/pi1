/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Pi1.Orbifold.GaloisData
public import Pi1.RingTheory.Smooth.Dedekind

/-!
# The coordinate rings of the normalized `t`-line are smooth curves

Let `k` be a perfect field (e.g. of characteristic `0`), `t ∈ Ω` transcendental over `k` and
`k(t) ⊆ L ⊆ Ω` finite and separable over `k(t)`. The coordinate ring `coordRing k t L` (the
integral closure of `k[t]` in `L`) is a Dedekind domain of finite type over `k`, hence smooth over
`k` (`Algebra.smooth_of_isDedekindDomain`), and of Krull dimension `1`:

* `AffOrbicurve.smooth_ring`, `AffOrbicurve.ringKrullDim_ring` for `coordRing k t L`;
* `Pi1.Orbifold.CoordRing.smooth`, `Pi1.Orbifold.CoordRing.ringKrullDim_eq_one` for the type
  synonym `CoordRing k t L` (with its `k`-algebra structure `CoordRing.algebraK`);
* `Pi1.Orbifold.GaloisData.smooth_R`, `Pi1.Orbifold.GaloisData.ringKrullDim_R` for the coordinate
  ring `D.R` of Galois data (when `Ω / k(t)` is Galois, `L` is automatically separable).
-/

@[expose] public section

universe u

open AffOrbicurve

namespace AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (ht : Transcendental k t)
  (L : IntermediateField (K₀ k t) Ω)

include ht in
/-- **The coordinate ring of the normalization of the `t`-line in `L` is smooth** over a perfect
field `k`. -/
theorem smooth_ring [PerfectField k] [FiniteDimensional (K₀ k t) L]
    [Algebra.IsSeparable (K₀ k t) L] : Algebra.Smooth k (coordRing k t L) :=
  haveI := isDedekindDomain_ring t ht L
  haveI := finiteType_ring t ht L
  Algebra.smooth_of_isDedekindDomain

include ht in
/-- The coordinate ring of the normalization of the `t`-line in `L` has Krull dimension `1`. -/
theorem ringKrullDim_ring [FiniteDimensional (K₀ k t) L] [Algebra.IsSeparable (K₀ k t) L] :
    ringKrullDim (coordRing k t L) = 1 :=
  haveI := isDedekindDomain_ring t ht L
  IsDedekindDomain.ringKrullDim_eq_one (not_isField_ring t ht L)

end AffOrbicurve

namespace Pi1.Orbifold

namespace CoordRing

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (ht : Transcendental k t)
  (L : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) L]
  [Algebra.IsSeparable (K₀ k t) L]

include ht in
lemma isDedekindDomain : IsDedekindDomain (CoordRing k t L) :=
  haveI := isDedekindDomain_ring t ht L
  inferInstanceAs (IsDedekindDomain (coordRing k t L))

include ht in
lemma finiteType : Algebra.FiniteType k (CoordRing k t L) := by
  haveI : Module.Finite (A₀ k t) (CoordRing k t L) :=
    haveI := finite_ring t ht L
    inferInstanceAs (Module.Finite (A₀ k t) (coordRing k t L))
  haveI : IsScalarTower k (A₀ k t) (CoordRing k t L) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := finiteType_A₀ ht
  exact Algebra.FiniteType.trans (S := A₀ k t) inferInstance inferInstance

include ht in
/-- **The coordinate ring `CoordRing k t L` is smooth** over a perfect field `k`. -/
theorem smooth [PerfectField k] : Algebra.Smooth k (CoordRing k t L) :=
  haveI := isDedekindDomain ht L
  haveI := finiteType ht L
  Algebra.smooth_of_isDedekindDomain

omit [FiniteDimensional (K₀ k t) L] [Algebra.IsSeparable (K₀ k t) L] in
include ht in
lemma not_isField : ¬ IsField (CoordRing k t L) :=
  not_isField_ring t ht L

include ht in
/-- The coordinate ring `CoordRing k t L` has Krull dimension `1`. -/
theorem ringKrullDim_eq_one : ringKrullDim (CoordRing k t L) = 1 :=
  haveI := isDedekindDomain ht L
  IsDedekindDomain.ringKrullDim_eq_one (not_isField ht L)

end CoordRing

namespace GaloisData

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} [IsGalois (K₀ k t) Ω]
  (D : GaloisData k t)

instance isSeparable_L : Algebra.IsSeparable (K₀ k t) D.L :=
  Algebra.isSeparable_tower_bot_of_isSeparable (K₀ k t) D.L Ω

/-- **The coordinate ring `R` of Galois data is smooth** over a perfect field `k`. -/
instance smooth_R [PerfectField k] : Algebra.Smooth k D.R :=
  CoordRing.smooth D.transcendental D.L

/-- The coordinate ring `R` of Galois data has Krull dimension `1`. -/
theorem ringKrullDim_R : ringKrullDim D.R = 1 :=
  CoordRing.ringKrullDim_eq_one D.transcendental D.L

end GaloisData

end Pi1.Orbifold
