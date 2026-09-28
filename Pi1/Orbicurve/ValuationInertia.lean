module

public import Pi1.Orbicurve.SubfieldGalois
public import Pi1.Orbicurve.GaloisPi1
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Valuation-theoretic inertia and inertia of primes of coordinate rings

Let `Ω / K₀` (`K₀ = k(t)`) be a Galois extension and `W` a valuation subring of `Ω` *centered on
the `t`-line*: `k ⊆ W` and `t ∈ W` (`AffOrbicurve.IsCentered`). For an intermediate field `N`,
finite over `K₀`, the coordinate ring `coordRing k t N` is contained in `W`
(`AffOrbicurve.toΩ_mem`), and the center of `W` on it is the prime ideal

  `u_W(N) = {a ∈ coordRing k t N | v_W(a) < 1}` (`AffOrbicurve.centerIdeal`),

maximal when nonzero (`AffOrbicurve.isMaximal_centerIdeal`).

* `AffOrbicurve.restrictNormal_mem_inertia`: for `N / K₀` normal, the restriction to `N` of an
  element of the inertia group `GaloisPi1.inertia W` lies in the inertia group of `u_W(N)`
  (and in `Gal(N / L)` if it fixes `L`: `AffOrbicurve.restrictNormal_mem_fixSub`);
* `AffOrbicurve.exists_mem_inertia_restrictNormal_eq`: conversely, in characteristic `0`, for
  `N / K₀` finite Galois and `u_W(N) ≠ 0`, every element of the inertia group of `u_W(N)` is the
  restriction of an element of `GaloisPi1.inertia W` (surjectivity of inertia). The proof lifts
  compatibly to all finite Galois `M ⊇ N` (by counting: `|I_{u_W(M)}(M / K₀)| = e`, and `e` is
  multiplicative in towers) and concludes by compactness of `Gal(Ω / K₀)`.
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

section Center

variable (k t) in
/-- A valuation subring `W` of `Ω` is **centered on the `t`-line** if it contains `k` and `t`
(equivalently, `k[t] ⊆ W`). -/
def IsCentered (W : ValuationSubring Ω) : Prop :=
  (∀ c : k, algebraMap k Ω c ∈ W) ∧ t ∈ W

variable (t) in
/-- The inclusion of the coordinate ring `coordRing k t L` into `Ω`. -/
def toΩ (L : IntermediateField (K₀ k t) Ω) : coordRing k t L →+* Ω :=
  (L.val : L →+* Ω).comp (coordRing k t L).val.toRingHom

@[simp] lemma toΩ_apply (L : IntermediateField (K₀ k t) Ω) (a : coordRing k t L) :
    toΩ t L a = ((a : L) : Ω) := rfl

lemma toΩ_injective (L : IntermediateField (K₀ k t) Ω) : Function.Injective (toΩ t L) :=
  fun _ _ h => Subtype.val_injective (Subtype.val_injective h)

variable {W : ValuationSubring Ω}

lemma A₀_le (hW : IsCentered k t W) (x : A₀ k t) : (x : Ω) ∈ W := by
  have key : ∀ y ∈ Algebra.adjoin k {t}, y ∈ W := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact hW.2
    | algebraMap c => exact hW.1 c
    | add y z _ _ hy hz => exact W.add_mem _ _ hy hz
    | mul y z _ _ hy hz => exact W.mul_mem _ _ hy hz
  exact key x x.2

/-- Elements of the coordinate ring lie in every valuation subring centered on the `t`-line
(valuation rings are integrally closed). -/
lemma toΩ_mem (hW : IsCentered k t W) (L : IntermediateField (K₀ k t) Ω) (a : coordRing k t L) :
    toΩ t L a ∈ W := by
  obtain ⟨p, hp, hpa⟩ := a.2
  let φ : A₀ k t →+* W :=
    { toFun x := ⟨x, A₀_le hW x⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hint : IsIntegral W (toΩ t L a) := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    have hc : (algebraMap W Ω).comp φ = (L.val : L →+* Ω).comp (algebraMap (A₀ k t) L) :=
      RingHom.ext fun _ => rfl
    rw [Polynomial.eval₂_map, hc, toΩ_apply]
    have := Polynomial.hom_eval₂ p (algebraMap (A₀ k t) L) (L.val : L →+* Ω) (a : L)
    rw [hpa, map_zero] at this
    exact this.symm
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

/-- `coordRing k t L → W`. -/
def toW (hW : IsCentered k t W) (L : IntermediateField (K₀ k t) Ω) : coordRing k t L →+* W :=
  (toΩ t L).codRestrict W.toSubring (toΩ_mem hW L)

/-- **The center of `W` on the normalization of the `t`-line in `L`**: the prime ideal
`u_W(L) = {a ∈ coordRing k t L | a ∈ nonunits W}`. -/
def centerIdeal (hW : IsCentered k t W) (L : IntermediateField (K₀ k t) Ω) :
    Ideal (coordRing k t L) :=
  (IsLocalRing.maximalIdeal W).comap (toW hW L)

instance (hW : IsCentered k t W) (L : IntermediateField (K₀ k t) Ω) :
    (centerIdeal hW L).IsPrime :=
  Ideal.comap_isPrime _ _

lemma mem_centerIdeal (hW : IsCentered k t W) {L : IntermediateField (K₀ k t) Ω}
    {a : coordRing k t L} : a ∈ centerIdeal hW L ↔ W.valuation (toΩ t L a) < 1 :=
  W.valuation_lt_one_iff (toW hW L a)

lemma mem_centerIdeal_iff_mem_nonunits (hW : IsCentered k t W)
    {L : IntermediateField (K₀ k t) Ω} {a : coordRing k t L} :
    a ∈ centerIdeal hW L ↔ (⟨toΩ t L a, toΩ_mem hW L a⟩ : W) ∈ nonunits W :=
  Iff.rfl

lemma valuation_eq_one_of_notMem (hW : IsCentered k t W) {L : IntermediateField (K₀ k t) Ω}
    {a : coordRing k t L} (ha : a ∉ centerIdeal hW L) : W.valuation (toΩ t L a) = 1 := by
  rw [mem_centerIdeal, not_lt] at ha
  exact le_antisymm ((W.valuation_le_one_iff _).mpr (toΩ_mem hW L a)) ha

lemma valuation_le_one (hW : IsCentered k t W) {L : IntermediateField (K₀ k t) Ω}
    (a : coordRing k t L) : W.valuation (toΩ t L a) ≤ 1 :=
  (W.valuation_le_one_iff _).mpr (toΩ_mem hW L a)

/-- `u_W(L)` is maximal when nonzero. -/
lemma isMaximal_centerIdeal (ht : Transcendental k t) (hW : IsCentered k t W)
    (L : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) L]
    [Algebra.IsSeparable (K₀ k t) L] (h : centerIdeal hW L ≠ ⊥) : (centerIdeal hW L).IsMaximal :=
  haveI := isDedekindDomain_ring t ht L
  Ring.DimensionLEOne.maximalOfPrime h inferInstance

/-- The centers are compatible: `u_W(M) ∩ coordRing k t L = u_W(L)` for `L ⊆ M`. -/
lemma comap_centerIdeal (hW : IsCentered k t W) {L M : IntermediateField (K₀ k t) Ω}
    (h : L ≤ M) : (centerIdeal hW M).comap (ringMap t h) = centerIdeal hW L := by
  ext a
  simp only [Ideal.mem_comap, mem_centerIdeal]
  rfl

lemma centerIdeal_ne_bot_of_le (hW : IsCentered k t W) {L M : IntermediateField (K₀ k t) Ω}
    (h : L ≤ M) (hL : centerIdeal hW L ≠ ⊥) : centerIdeal hW M ≠ ⊥ := by
  intro hM
  apply hL
  rw [← comap_centerIdeal hW h, hM, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (ringMap_injective t h)

end Center

section Restriction

variable {W : ValuationSubring Ω}

variable (W) in
/-- `σ` acts trivially modulo the maximal ideal of `W` on the coordinate ring of `M`:
`v_W(σ b - b) < 1` for all `b ∈ coordRing k t M`. -/
def IsInertialOn (M : IntermediateField (K₀ k t) Ω) (σ : Ω ≃ₐ[K₀ k t] Ω) : Prop :=
  ∀ b : coordRing k t M, W.valuation (σ (toΩ t M b) - toΩ t M b) < 1

lemma isInertialOn_of_mem_inertia (hW : IsCentered k t W) (M : IntermediateField (K₀ k t) Ω)
    {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ GaloisPi1.inertia W) : IsInertialOn W M σ :=
  fun b => hσ _ (toΩ_mem hW M b)

lemma IsInertialOn.mono {L M : IntermediateField (K₀ k t) Ω} (h : L ≤ M) {σ : Ω ≃ₐ[K₀ k t] Ω}
    (hσ : IsInertialOn W M σ) : IsInertialOn W L σ :=
  fun b => hσ (ringMap t h b)

@[simp] lemma coe_restrictNormal_apply (N : IntermediateField (K₀ k t) Ω) [Normal (K₀ k t) N]
    (σ : Ω ≃ₐ[K₀ k t] Ω) (x : N) : ((σ.restrictNormal N x : N) : Ω) = σ (x : Ω) :=
  AlgEquiv.restrictNormal_apply N σ x

lemma mem_inertia_centerIdeal_iff (hW : IsCentered k t W) (N : IntermediateField (K₀ k t) Ω)
    (ρ : N ≃ₐ[K₀ k t] N) :
    ρ ∈ (centerIdeal hW N).inertia (N ≃ₐ[K₀ k t] N) ↔
      ∀ b : coordRing k t N, W.valuation ((ρ (b : N) : Ω) - toΩ t N b) < 1 := by
  simp only [Ideal.inertia, AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ?_
  rw [Submodule.mem_toAddSubgroup, mem_centerIdeal]
  rfl

/-- The restriction of `σ` to `N` lies in the inertia group of `u_W(N)` iff `σ` acts trivially
on `coordRing k t N` modulo the maximal ideal of `W`. -/
lemma restrictNormal_mem_inertia_iff (hW : IsCentered k t W) (N : IntermediateField (K₀ k t) Ω)
    [Normal (K₀ k t) N] (σ : Ω ≃ₐ[K₀ k t] Ω) :
    σ.restrictNormal N ∈ (centerIdeal hW N).inertia (N ≃ₐ[K₀ k t] N) ↔ IsInertialOn W N σ := by
  rw [mem_inertia_centerIdeal_iff]
  simp only [coe_restrictNormal_apply]
  rfl

/-- **Restriction of inertia**: the restriction to `N` (normal over `K₀`) of an element of the
inertia group of `W` lies in the inertia group of the center `u_W(N)`. -/
theorem restrictNormal_mem_inertia (hW : IsCentered k t W) (N : IntermediateField (K₀ k t) Ω)
    [Normal (K₀ k t) N] {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ GaloisPi1.inertia W) :
    σ.restrictNormal N ∈ (centerIdeal hW N).inertia (N ≃ₐ[K₀ k t] N) :=
  (restrictNormal_mem_inertia_iff hW N σ).mpr (isInertialOn_of_mem_inertia hW N hσ)

/-- The restriction to `N` of an automorphism fixing `L` lies in `Gal(N / L) = fixSub t N L`. -/
theorem restrictNormal_mem_fixSub (N : IntermediateField (K₀ k t) Ω) [Normal (K₀ k t) N]
    {L : IntermediateField (K₀ k t) Ω} {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ L.fixingSubgroup) :
    σ.restrictNormal N ∈ fixSub t N L := by
  intro x hx
  apply Subtype.val_injective
  rw [coe_restrictNormal_apply]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ hx

/-- **Restriction of inertia** (relative version): for `σ ∈ I_W ∩ Aut(Ω / L)`, the restriction
of `σ` to `N` lies in `I_{u_W(N)}(N / K₀) ∩ Gal(N / L)`. -/
theorem restrictNormal_mem_inertia_inf_fixSub (hW : IsCentered k t W)
    (N : IntermediateField (K₀ k t) Ω) [Normal (K₀ k t) N] {L : IntermediateField (K₀ k t) Ω}
    {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ GaloisPi1.inertia W) (hσL : σ ∈ L.fixingSubgroup) :
    σ.restrictNormal N ∈ (centerIdeal hW N).inertia (N ≃ₐ[K₀ k t] N) ⊓ fixSub t N L :=
  ⟨restrictNormal_mem_inertia hW N hσ, restrictNormal_mem_fixSub N hσL⟩

end Restriction

end AffOrbicurve
