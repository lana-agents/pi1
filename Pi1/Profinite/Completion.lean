/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Homomorphisms from a profinite completion to a finite group

For a group `G` and a finite group `P`, every homomorphism `f : G →* P` extends uniquely to a
continuous homomorphism `Ĝ →* P` on the profinite completion
`Ĝ = ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)` (Mathlib's `lift`, with `P`
discrete). This file packages that extension as a plain monoid homomorphism
`Pi1.Profinite.liftFinite f : Ĝ →* P` and records:

* `liftFinite_eta`: `liftFinite f (etaFn x) = f x`;
* `isOpen_liftFinite_fiber`: the fibres of `liftFinite f` are open (continuity for the discrete
  topology on `P`);
* `liftFinite_comp`: `liftFinite (h ∘ f) = h ∘ liftFinite f` for `h : P →* P'`;
* `eq_one_of_forall_liftFinite`: an element of `Ĝ` that is killed by every `liftFinite f` is
  trivial (the extensions of homomorphisms to finite groups separate the points of `Ĝ`);
* `exists_etaFn_eq`: given finitely many such extensions, every element of `Ĝ` has the same
  values as some element of `G`, and can be chosen in a given open neighbourhood.
-/

@[expose] public section

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology

universe u

namespace Pi1.Profinite

variable {G : Type u} [Group G] {P : Type u} [Group P] [Finite P]

/-- The profinite group `P` (finite, with the discrete topology). -/
noncomputable abbrev finiteProfinite (P : Type u) [Group P] [Finite P] : ProfiniteGrp.{u} :=
  ProfiniteGrp.ofFiniteGrp (FiniteGrp.of P)

/-- **The continuous extension** `Ĝ →* P` of a homomorphism `f : G →* P` to a finite group. -/
noncomputable def liftFinite (f : G →* P) : completion (GrpCat.of G) →* P :=
  (lift (P := finiteProfinite P) (GrpCat.ofHom f)).hom.toMonoidHom

@[simp]
theorem liftFinite_eta (f : G →* P) (x : G) :
    liftFinite f (etaFn (GrpCat.of G) x) = f x :=
  ConcreteCategory.congr_hom (lift_eta (P := finiteProfinite P) (GrpCat.ofHom f)) x

/-- The fibres of `liftFinite f` are open. -/
theorem isOpen_liftFinite_fiber (f : G →* P) (p : P) :
    IsOpen {x : completion (GrpCat.of G) | liftFinite f x = p} := by
  letI : TopologicalSpace P := ⊥
  haveI : DiscreteTopology P := ⟨rfl⟩
  have hc : Continuous (liftFinite f) :=
    (lift (P := finiteProfinite P) (GrpCat.ofHom f)).hom.continuous
  exact hc.isOpen_preimage {p} (isOpen_discrete _)

/-- **Approximation by elements of `G`**: for two homomorphisms `f₁`, `f₂` to finite groups and
an open set `U ∋ z`, some `x : G` has `etaFn x ∈ U` and the same values as `z` under
`liftFinite f₁` and `liftFinite f₂`. -/
theorem exists_etaFn_eq₂ {P₁ P₂ : Type u} [Group P₁] [Finite P₁] [Group P₂] [Finite P₂]
    (f₁ : G →* P₁) (f₂ : G →* P₂) {U : Set (completion (GrpCat.of G))} (hU : IsOpen U)
    {z : completion (GrpCat.of G)} (hz : z ∈ U) :
    ∃ x : G, etaFn (GrpCat.of G) x ∈ U ∧ f₁ x = liftFinite f₁ z ∧ f₂ x = liftFinite f₂ z := by
  have hV : IsOpen (U ∩ {y | liftFinite f₁ y = liftFinite f₁ z} ∩
      {y | liftFinite f₂ y = liftFinite f₂ z}) :=
    (hU.inter (isOpen_liftFinite_fiber f₁ _)).inter (isOpen_liftFinite_fiber f₂ _)
  obtain ⟨x, hx⟩ := (denseRange (GrpCat.of G)).exists_mem_open hV ⟨z, ⟨hz, rfl⟩, rfl⟩
  refine ⟨x, hx.1.1, ?_, ?_⟩
  · simpa using hx.1.2
  · simpa using hx.2

/-- **Approximation by elements of `G`**, for one homomorphism. -/
theorem exists_etaFn_eq (f : G →* P) {U : Set (completion (GrpCat.of G))} (hU : IsOpen U)
    {z : completion (GrpCat.of G)} (hz : z ∈ U) :
    ∃ x : G, etaFn (GrpCat.of G) x ∈ U ∧ f x = liftFinite f z := by
  obtain ⟨x, hx, h, -⟩ := exists_etaFn_eq₂ f f hU hz
  exact ⟨x, hx, h⟩

/-- Naturality of `liftFinite`. -/
theorem liftFinite_comp {P' : Type u} [Group P'] [Finite P'] (f : G →* P) (h : P →* P')
    (z : completion (GrpCat.of G)) : liftFinite (h.comp f) z = h (liftFinite f z) := by
  obtain ⟨x, -, h1, h2⟩ := exists_etaFn_eq₂ (h.comp f) f isOpen_univ (Set.mem_univ z)
  rw [← h1, ← h2, MonoidHom.comp_apply]

/-- The set of `y` with `y M = z M` is open, for an open subgroup `M`. -/
lemma isOpen_setOf_mk_eq {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (M : Subgroup H) (hM : IsOpen (M : Set H)) (z : H) :
    IsOpen {y : H | (QuotientGroup.mk y : H ⧸ M) = QuotientGroup.mk z} := by
  have : IsOpen ((z * ·) '' (M : Set H)) := (Homeomorph.mulLeft z).isOpenMap _ hM
  convert this using 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
  constructor
  · intro h
    exact ⟨z⁻¹ * y, QuotientGroup.eq.1 h.symm, by group⟩
  · rintro ⟨n, hn, rfl⟩
    exact (QuotientGroup.eq.2 (by simpa using hn)).symm

/-- **The extensions to finite quotients separate points**: if every `liftFinite f` (for all
homomorphisms `f` from `G` to finite groups) kills `z`, then `z = 1`. -/
theorem eq_one_of_forall_liftFinite {z : completion (GrpCat.of G)}
    (hz : ∀ (P : Type u) [Group P] [Finite P] (f : G →* P), liftFinite f z = 1) : z = 1 := by
  by_contra hne
  have hU : IsOpen ({z}ᶜ : Set (completion (GrpCat.of G))) := isOpen_compl_singleton
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU
    (by simpa [eq_comm] using hne)
  haveI : Finite (completion (GrpCat.of G) ⧸ N.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ N.isOpen
  obtain ⟨x, hx, hxz⟩ := exists_etaFn_eq
    ((QuotientGroup.mk' N.toSubgroup).comp (eta (GrpCat.of G)).hom)
    (isOpen_setOf_mk_eq N.toSubgroup N.isOpen z) rfl
  rw [hz] at hxz
  have hmem : z ∈ N.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff]
    exact hx.symm.trans hxz
  exact hN hmem rfl

/-! ### Functoriality -/

section Map

variable {H : Type u} [Group H]

/-- The continuous homomorphism `Ĝ → Ĥ` induced by `φ : G →* H`. -/
noncomputable def completionMap (φ : G →* H) :
    completion (GrpCat.of G) →* completion (GrpCat.of H) :=
  (profiniteCompletion.map (GrpCat.ofHom φ)).hom.toMonoidHom

theorem continuous_completionMap (φ : G →* H) : Continuous (completionMap φ) :=
  (profiniteCompletion.map (GrpCat.ofHom φ)).hom.continuous

@[simp]
theorem completionMap_eta (φ : G →* H) (x : G) :
    completionMap φ (etaFn (GrpCat.of G) x) = etaFn (GrpCat.of H) (φ x) :=
  ConcreteCategory.congr_hom (lift_eta (GrpCat.ofHom φ ≫ eta (GrpCat.of H))) x

theorem liftFinite_completionMap (φ : G →* H) (ρ : H →* P) (x : completion (GrpCat.of G)) :
    liftFinite ρ (completionMap φ x) = liftFinite (ρ.comp φ) x := by
  have hU : IsOpen {y | liftFinite ρ (completionMap φ y) = liftFinite ρ (completionMap φ x)} :=
    (isOpen_liftFinite_fiber ρ _).preimage (continuous_completionMap φ)
  obtain ⟨w, hw, hw'⟩ := exists_etaFn_eq (ρ.comp φ) hU (z := x) rfl
  have hw2 : liftFinite ρ (completionMap φ (etaFn _ w)) = liftFinite ρ (completionMap φ x) := hw
  rw [← hw', ← hw2, completionMap_eta, liftFinite_eta, MonoidHom.comp_apply]

/-- A group isomorphism induces an isomorphism of profinite completions. -/
noncomputable def completionCongr (e : G ≃* H) :
    completion (GrpCat.of G) ≃ₜ* completion (GrpCat.of H) :=
  let i := profiniteCompletion.mapIso (MulEquiv.toGrpIso (X := GrpCat.of G) (Y := GrpCat.of H) e)
  { toFun := i.hom
    invFun := i.inv
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp
    map_mul' := map_mul i.hom.hom
    continuous_toFun := i.hom.hom.continuous
    continuous_invFun := i.inv.hom.continuous }

theorem completionCongr_apply (e : G ≃* H) (x : completion (GrpCat.of G)) :
    completionCongr e x = completionMap e.toMonoidHom x := rfl

end Map

/-- **Injectivity on a procyclic subgroup.** Let `γ : G`. If for every `n > 0` some homomorphism
from `G` to a finite group sends `γ` to an element of order exactly `n`, then the map
`ℤ̂ → Ĝ` induced by `k ↦ γ ^ k` is injective. -/
theorem completionMap_zpowersHom_injective {G : Type} [Group G] {γ : G}
    (h : ∀ n : ℕ, 0 < n → ∃ (R : Type) (_ : Group R) (_ : Finite R) (ρ : G →* R),
      orderOf (ρ γ) = n) :
    Function.Injective (completionMap (zpowersHom G γ)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  refine eq_one_of_forall_liftFinite fun P _ _ f ↦ ?_
  set p := f (Multiplicative.ofAdd 1)
  obtain ⟨R, _, _, ρ, hρ⟩ := h (orderOf p) (orderOf_pos p)
  have h1 : liftFinite (ρ.comp (zpowersHom G γ)) x = 1 := by
    rw [← liftFinite_completionMap, hx, map_one]
  obtain ⟨w, -, hf, hg⟩ := exists_etaFn_eq₂ f (ρ.comp (zpowersHom G γ)) isOpen_univ
    (Set.mem_univ x)
  rw [h1] at hg
  rw [← hf]
  have hw : w = Multiplicative.ofAdd 1 ^ (Multiplicative.toAdd w) := by
    rw [← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
  rw [MonoidHom.comp_apply, zpowersHom_apply, map_zpow] at hg
  rw [hw, map_zpow, ← orderOf_dvd_iff_zpow_eq_one, ← hρ]
  exact orderOf_dvd_iff_zpow_eq_one.2 hg

end Pi1.Profinite
