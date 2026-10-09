/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.DiscreteValuationRing.Basic


/-!
# Tame inertia groups are cyclic

Let `B` be a Dedekind domain, `G` a finite group acting on `B` by ring automorphisms, and `u` a
nonzero maximal ideal of `B` whose residue field has characteristic `0`. Then the inertia group
`I_u = {σ | σ x ≡ x mod u}` is cyclic (`TameInertia.isCyclic_inertia`): with `R = B_u` (a
discrete valuation ring) and a uniformizer `π`, the map `σ ↦ (σ π / π mod u)` is an injective
homomorphism `I_u → (R / 𝔪)ˣ`. Injectivity is the usual argument: if `σ π ≡ π mod 𝔪²`, then
`δ = σ − 1` maps `𝔪ⁿ` into `𝔪ⁿ⁺¹`, and `σ^r = 1` gives `r δ = −∑_{i ≥ 2} C(r, i) δⁱ`, whence, `r`
being a unit, `δ(𝔪ⁿ) ⊆ 𝔪ⁿ⁺ʲ` for all `j`, so `δ = 0`.
-/

@[expose] public section

open scoped Pointwise
open Ideal IsLocalRing

namespace TameInertia

variable {B : Type*} [CommRing B] [IsDedekindDomain B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
  (u : Ideal B) [hu : u.IsMaximal] (hu0 : u ≠ ⊥)

local notation "R" => Localization.AtPrime u

set_option linter.unusedSectionVars false in
lemma comap_eq_of_mem_inertia {σ : G} (hσ : σ ∈ u.inertia G) :
    u = u.comap (MulSemiringAction.toRingHom G B σ) := by
  ext x
  have hx : σ • x - x ∈ u := hσ x
  simp only [Ideal.mem_comap, MulSemiringAction.toRingHom_apply]
  constructor
  · intro h
    have := u.add_mem hx h
    simpa using this
  · intro h
    have := u.sub_mem h hx
    simpa using this

/-- The ring endomorphism of `B_u` induced by an inertia element. -/
noncomputable def loc {σ : G} (hσ : σ ∈ u.inertia G) : R →+* R :=
  Localization.localRingHom u u (MulSemiringAction.toRingHom G B σ) (comap_eq_of_mem_inertia u hσ)

lemma loc_algebraMap {σ : G} (hσ : σ ∈ u.inertia G) (b : B) :
    loc u hσ (algebraMap B R b) = algebraMap B R (σ • b) :=
  Localization.localRingHom_to_map _ _ _ _ b

lemma loc_mul {σ τ : G} (hσ : σ ∈ u.inertia G) (hτ : τ ∈ u.inertia G) :
    loc u (Subgroup.mul_mem _ hσ hτ) = (loc u hσ).comp (loc u hτ) := by
  apply IsLocalization.ringHom_ext u.primeCompl
  ext b
  simp only [RingHom.comp_apply, loc_algebraMap, mul_smul]

lemma loc_one : loc u (Subgroup.one_mem (u.inertia G)) = RingHom.id R := by
  apply IsLocalization.ringHom_ext u.primeCompl
  ext b
  simp [loc_algebraMap]

/-- Inertia elements act trivially on the residue field of `B_u`. -/
lemma loc_sub_mem {σ : G} (hσ : σ ∈ u.inertia G) (r : R) :
    loc u hσ r - r ∈ maximalIdeal R := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective u.primeCompl r
  have hs : σ • (s : B) ∈ u.primeCompl := by
    intro h
    apply s.2
    have := u.sub_mem h (hσ (s : B))
    simpa using this
  have e : loc u hσ (IsLocalization.mk' R b s) =
      IsLocalization.mk' R (σ • b) (⟨σ • (s : B), hs⟩ : u.primeCompl) := by
    rw [loc, Localization.localRingHom_mk']
    rfl
  rw [e, ← IsLocalization.mk'_sub, IsLocalization.AtPrime.mk'_mem_maximal_iff R u]
  have h1 := hσ b
  have h2 := hσ (s : B)
  have : σ • b * (s : B) - b * (σ • (s : B)) = (σ • b - b) * s - b * (σ • (s : B) - s) := by ring
  change σ • b * (s : B) - b * (σ • (s : B)) ∈ u
  rw [this]
  exact u.sub_mem (u.mul_mem_right _ h1) (u.mul_mem_left _ h2)

include hu0 in
lemma isDVR : IsDiscreteValuationRing R :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hu0 R

/-- The inverse of an inertia element acts as the inverse of `loc`. -/
lemma loc_inv_comp {σ : G} (hσ : σ ∈ u.inertia G) :
    (loc u ((u.inertia G).inv_mem hσ)).comp (loc u hσ) = RingHom.id R := by
  rw [← loc_mul u, ← loc_one u (G := G)]
  congr 1
  exact inv_mul_cancel σ

lemma loc_comp_inv {σ : G} (hσ : σ ∈ u.inertia G) :
    (loc u hσ).comp (loc u ((u.inertia G).inv_mem hσ)) = RingHom.id R := by
  rw [← loc_mul u, ← loc_one u (G := G)]
  congr 1
  exact mul_inv_cancel σ

/-- `loc` as a ring automorphism. -/
noncomputable def locEquiv {σ : G} (hσ : σ ∈ u.inertia G) : R ≃+* R :=
  RingEquiv.ofRingHom (loc u hσ) (loc u ((u.inertia G).inv_mem hσ)) (loc_comp_inv u hσ)
    (loc_inv_comp u hσ)

section Uniformizer


include hu0 in
lemma exists_unit {π : R} (hπ : Irreducible π) {σ : G} (hσ : σ ∈ u.inertia G) :
    ∃ a : Rˣ, loc u hσ π = π * a := by
  haveI := isDVR u hu0
  have h2 : Irreducible (loc u hσ π) := by
    have := (MulEquiv.irreducible_iff (locEquiv u hσ).toMulEquiv).mpr hπ
    exact this
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.associated_of_irreducible R hπ h2
  exact ⟨a, ha.symm⟩

/-- The unit `σ π / π`. -/
noncomputable def unitOf {π : R} (hπ : Irreducible π) {σ : G} (hσ : σ ∈ u.inertia G) : Rˣ :=
  (exists_unit u hu0 hπ hσ).choose

include hu0 in
lemma unitOf_spec {π : R} (hπ : Irreducible π) {σ : G} (hσ : σ ∈ u.inertia G) :
    loc u hσ π = π * unitOf u hu0 hπ hσ :=
  (exists_unit u hu0 hπ hσ).choose_spec


include hu0 in
lemma unitOf_mul {π : R} (hπ : Irreducible π) {σ τ : G} (hσ : σ ∈ u.inertia G)
    (hτ : τ ∈ u.inertia G) :
    (unitOf u hu0 hπ (Subgroup.mul_mem _ hσ hτ) : R) =
      unitOf u hu0 hπ hσ * loc u hσ (unitOf u hu0 hπ hτ) := by
  have h1 := unitOf_spec u hu0 hπ (Subgroup.mul_mem _ hσ hτ)
  rw [loc_mul u hσ hτ, RingHom.comp_apply, unitOf_spec u hu0 hπ hτ, map_mul,
    unitOf_spec u hu0 hπ hσ, mul_assoc] at h1
  exact (mul_left_cancel₀ hπ.ne_zero h1).symm

/-- **The tame character** `I_u → (R / 𝔪)ˣ`, `σ ↦ σ π / π mod 𝔪`. -/
noncomputable def tameChar {π : R} (hπ : Irreducible π) : u.inertia G →* (ResidueField R)ˣ where
  toFun σ := Units.map (residue R : R →* ResidueField R) (unitOf u hu0 hπ σ.2)
  map_one' := by
    ext
    have h := unitOf_spec u hu0 hπ (Subgroup.one_mem (u.inertia G))
    rw [loc_one u] at h
    have : (unitOf u hu0 hπ (Subgroup.one_mem (u.inertia G)) : R) = 1 := by
      have := mul_left_cancel₀ hπ.ne_zero (h.symm.trans (mul_one π).symm)
      exact this
    simp [this]
  map_mul' σ τ := by
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mul]
    have := unitOf_mul u hu0 hπ σ.2 τ.2
    change (residue R) (unitOf u hu0 hπ (Subgroup.mul_mem _ σ.2 τ.2) : R) = _
    rw [this, map_mul]
    congr 1
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact loc_sub_mem u σ.2 _

lemma loc_pow {σ : G} (hσ : σ ∈ u.inertia G) (n : ℕ) (x : R) :
    loc u (Subgroup.pow_mem _ hσ n) x = (loc u hσ)^[n] x := by
  induction n generalizing x with
  | zero =>
    simp only [pow_zero, Function.iterate_zero, id_eq]
    rw [loc_one u]; rfl
  | succ n ih =>
    have : loc u (Subgroup.pow_mem _ hσ (n + 1)) =
        (loc u hσ).comp (loc u (Subgroup.pow_mem _ hσ n)) := by
      rw [← loc_mul u hσ (Subgroup.pow_mem _ hσ n)]
      congr 1
      rw [pow_succ']
    rw [this, RingHom.comp_apply, ih, ← Function.iterate_succ_apply' (loc u hσ) n x]

include hu0 in
/-- **Injectivity of the tame character** (residue characteristic `0`). -/
theorem tameChar_injective [CharZero (ResidueField R)] [FaithfulSMul G B] {π : R}
    (hπ : Irreducible π) : Function.Injective (tameChar (G := G) u hu0 hπ) := by
  haveI := isDVR u hu0
  rw [injective_iff_map_eq_one]
  intro σ hσ1
  set f := loc u σ.2 with hf
  set a := unitOf u hu0 hπ σ.2 with ha
  have hres : (a : R) - 1 ∈ maximalIdeal R := by
    have := congrArg (fun x : (ResidueField R)ˣ => (x : ResidueField R)) hσ1
    simp only [tameChar, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map, MonoidHom.coe_coe,
      Units.val_one] at this
    rw [← residue_eq_zero_iff, map_sub, this, map_one, sub_self]
  have hfπ : f π = π * a := unitOf_spec u hu0 hπ σ.2
  have hm : maximalIdeal R = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hmn : ∀ n : ℕ, maximalIdeal R ^ n = Ideal.span {π ^ n} := fun n => by
    rw [hm, Ideal.span_singleton_pow]
  -- `D = f - 1` raises the `𝔪`-adic order
  have hD1 : ∀ n : ℕ, ∀ x ∈ maximalIdeal R ^ n, f x - x ∈ maximalIdeal R ^ (n + 1) := by
    intro n x hx
    rw [hmn n, Ideal.mem_span_singleton'] at hx
    obtain ⟨y, rfl⟩ := hx
    have e : f (y * π ^ n) - y * π ^ n = π ^ n * ((a : R) ^ n * f y - y) := by
      rw [map_mul, map_pow, hfπ]; ring
    rw [e, pow_succ]
    refine Ideal.mul_mem_mul (by rw [hmn n]; exact Ideal.mem_span_singleton_self _) ?_
    have h1 : (a : R) ^ n - 1 ∈ maximalIdeal R := by
      have hr : residue R (a : R) = 1 := by
        have := (residue_eq_zero_iff _).mpr hres
        rwa [map_sub, map_one, sub_eq_zero] at this
      rw [← residue_eq_zero_iff, map_sub, map_pow, hr, one_pow, map_one, sub_self]
    have h2 : f y - y ∈ maximalIdeal R := loc_sub_mem u σ.2 y
    have : (a : R) ^ n * f y - y = (a : R) ^ n * (f y - y) + ((a : R) ^ n - 1) * y := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_right _ _ h1)
  -- `f` has finite order `r`
  set r := orderOf σ with hr
  have hrpos : 0 < r := orderOf_pos σ
  have hfr : ∀ x, f^[r] x = x := by
    intro x
    rw [← loc_pow u σ.2 r x]
    have h1 : ((σ : G) ^ r) = 1 := by
      have := pow_orderOf_eq_one σ
      rw [← hr] at this
      exact congrArg Subtype.val this
    have : ∀ (τ : G) (hτ : τ ∈ u.inertia G), τ = 1 → loc u hτ x = x := by
      rintro τ hτ rfl
      rw [loc_one u]; rfl
    exact this _ _ h1
  -- the endomorphism `D = f - 1` of `R` as a `ℤ`-module
  let F : Module.End ℤ R := f.toAddMonoidHom.toIntLinearMap
  let D : Module.End ℤ R := F - 1
  have hFr : F ^ r = 1 := by
    ext x
    rw [Module.End.coe_pow]
    exact hfr x
  have hbinom : ∀ x : R, ∑ i ∈ Finset.range r, (r.choose (i + 1)) • (D ^ (i + 1)) x = 0 := by
    intro x
    have h := (Commute.one_right D).add_pow r
    have hDF : D + 1 = F := by simp [D]
    rw [hDF, hFr] at h
    have hx := congrArg (fun φ : Module.End ℤ R => φ x) h
    simp only [one_pow, mul_one, Module.End.one_apply] at hx
    rw [LinearMap.coe_sum, Finset.sum_apply, Finset.sum_range_succ'] at hx
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Module.End.one_apply] at hx
    have : ∀ i, ((D ^ (i + 1) * ((r.choose (i + 1) : ℕ) : Module.End ℤ R)) x) =
        (r.choose (i + 1)) • (D ^ (i + 1)) x := by
      intro i
      rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]
    simp only [this] at hx
    linear_combination -hx
  have hD : ∀ x : R, D x = f x - x := fun x => rfl
  -- `r` is a unit of `R`
  have hrunit : IsUnit (r : R) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
    exact_mod_cast hrpos.ne'
  -- iterates of `D`
  have hiter : ∀ J : ℕ, (∀ n : ℕ, ∀ x ∈ maximalIdeal R ^ n, D x ∈ maximalIdeal R ^ (n + J)) →
      ∀ i n : ℕ, ∀ x ∈ maximalIdeal R ^ n, (D ^ i) x ∈ maximalIdeal R ^ (n + i * J) := by
    intro J hJ i
    induction i with
    | zero => intro n x hx; simpa using hx
    | succ i ih =>
      intro n x hx
      rw [pow_succ', Module.End.mul_apply]
      have := hJ _ _ (ih n x hx)
      convert this using 2
      ring
  have hall : ∀ j : ℕ, ∀ n : ℕ, ∀ x ∈ maximalIdeal R ^ n, D x ∈ maximalIdeal R ^ (n + (j + 1)) := by
    intro j
    induction j with
    | zero => intro n x hx; rw [hD]; exact hD1 n x hx
    | succ j ih =>
      intro n x hx
      have hsum := hbinom x
      obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      rw [hs, Finset.sum_range_succ'] at hsum
      simp only [zero_add, pow_one, Nat.choose_one_right] at hsum
      have hrest : ∑ i ∈ Finset.range s, ((s + 1).choose (i + 1 + 1)) • (D ^ (i + 1 + 1)) x ∈
          maximalIdeal R ^ (n + (j + 1 + 1)) := by
        refine Ideal.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ ?_
        have := hiter (j + 1) ih (i + 1 + 1) n x hx
        refine Ideal.pow_le_pow_right ?_ this
        nlinarith
      have hmem : ((s + 1 : ℕ) : R) * D x ∈ maximalIdeal R ^ (n + (j + 1 + 1)) := by
        have : ((s + 1 : ℕ) : R) * D x =
            -∑ i ∈ Finset.range s, ((s + 1).choose (i + 1 + 1)) • (D ^ (i + 1 + 1)) x := by
          rw [← nsmul_eq_mul]; linear_combination hsum
        rw [this]; exact neg_mem hrest
      rw [← hs] at hmem
      obtain ⟨v, hv⟩ := hrunit
      have : D x = (↑v⁻¹ : R) * ((r : R) * D x) := by
        rw [← hv, ← mul_assoc, Units.inv_mul, one_mul]
      rw [this]; exact Ideal.mul_mem_left _ _ hmem
  -- hence `f = id`
  have hfid : ∀ x : R, f x = x := by
    intro x
    have h0 : D x ∈ ⨅ j : ℕ, maximalIdeal R ^ j := by
      refine Ideal.mem_iInf.mpr fun j => ?_
      cases j with
      | zero => simp
      | succ j =>
        have := hall j 0 x (by simp)
        simpa using this
    rw [Ideal.iInf_pow_eq_bot_of_isDomain (maximalIdeal R)
      (Ideal.IsMaximal.ne_top inferInstance), Ideal.mem_bot, hD, sub_eq_zero] at h0
    exact h0
  -- hence `σ` acts trivially on `B`, so `σ = 1`
  apply Subtype.ext
  apply FaithfulSMul.eq_of_smul_eq_smul (α := B)
  intro b
  rw [OneMemClass.coe_one, one_smul]
  apply IsLocalization.injective R (M := u.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors u)
  have := hfid (algebraMap B R b)
  rw [hf, loc_algebraMap] at this
  exact this

end Uniformizer

include hu0 in
/-- **Tame inertia is cyclic**: if the residue field at `u` has characteristic `0` and `G` acts
faithfully, the inertia group of `u` embeds into the units of the residue field, hence is
cyclic. -/
theorem isCyclic_inertia [CharZero (ResidueField R)] [FaithfulSMul G B] :
    IsCyclic (u.inertia G) := by
  haveI := isDVR u hu0
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact isCyclic_of_injective_ringHom ((Units.coeHom (ResidueField R)).comp (tameChar u hu0 hπ))
    ((Units.val_injective).comp (tameChar_injective u hu0 hπ))

end TameInertia
