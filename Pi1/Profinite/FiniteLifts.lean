/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Profinite.Slim
public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Finite embedding problems and open subgroups of free profinite groups

A topological group `P` has **finite lifts** (`Pi1.Profinite.HasFiniteLifts P`) if every finite
embedding problem for `P` is solvable: for every surjection `π : E ↠ A` of finite groups and every
continuous homomorphism `φ : P → A` (continuity meaning that the fibres of `φ` are open, i.e.
continuity for the discrete topology on `A`), there is a continuous `ψ : P → E` with `π ∘ ψ = φ`.
For profinite groups this is (the finite-group form of) **projectivity**: [NSW] (3.5.1), (3.5.5)
define embedding problems and projective profinite groups (there `φ` is surjective and `E` is
allowed to be profinite), and by Gruenberg's theorem [NSW] (3.5.6) a profinite group is projective
iff every extension of it by a finite abelian `p`-group splits iff `cd_p G ≤ 1` for all `p`; free
pro-`c`-groups are projective by [NSW] (3.5.15). (Here [NSW] = Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, 2nd ed., electronic version 2.3, Chapter III §5.)

## Main results

* `HasFiniteLifts.of_mulEquiv`, `HasFiniteLifts.of_continuousMulEquiv`: invariance under
  isomorphisms of topological groups.
* `FreeHat.hasFiniteLifts_of_isOpen`: **every open subgroup of the profinite completion
  `F̂(α)` of a free group has finite lifts** (for an arbitrary set `α` of generators).
  The proof is elementary: for an open `H ≤ F̂(α)`, the preimage `H₀` of `H` in the discrete free
  group `F(α)` has finite index, hence is free (Nielsen–Schreier, Mathlib's
  `subgroupIsFreeOfIsFree`); lift `φ|_{H₀}` on a basis of `H₀` to `ψ₀ : H₀ → E`; `ψ₀` factors
  through `H₀ → F(α)/L` for a normal subgroup `L` of finite index, and the extension
  `F̂(α) → F(α)/L` of `F(α) → F(α)/L` maps `H` into the image of `H₀`, which defines `ψ`.
* `HasFiniteLifts.of_isOpen_of_continuousMulEquiv`: the same for open subgroups of any
  topological group isomorphic to `F̂(α)`.
-/

@[expose] public section

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology

universe u

namespace Pi1.Profinite

/-- **Finite embedding problems are solvable**: for every surjection `π : E ↠ A` of finite groups
and every homomorphism `φ : P →* A` with open fibres (i.e. continuous for the discrete topology on
`A`), there is a homomorphism `ψ : P →* E` with open fibres and `π ∘ ψ = φ`. For profinite `P`
this is the finite form of projectivity ([NSW] (3.5.1), (3.5.5)). -/
def HasFiniteLifts (P : Type*) [Group P] [TopologicalSpace P] : Prop :=
  ∀ (E A : Type) [Group E] [Group A] [Finite E] (π : E →* A), Function.Surjective π →
    ∀ φ : P →* A, (∀ a, IsOpen (φ ⁻¹' {a})) →
      ∃ ψ : P →* E, (∀ e, IsOpen (ψ ⁻¹' {e})) ∧ π.comp ψ = φ

/-- Finite lifts are transported along isomorphisms that are continuous in both directions. -/
theorem HasFiniteLifts.of_mulEquiv {P Q : Type*} [Group P] [TopologicalSpace P] [Group Q]
    [TopologicalSpace Q] (hP : HasFiniteLifts P) (e : P ≃* Q) (he : Continuous e)
    (he' : Continuous e.symm) : HasFiniteLifts Q := by
  intro E A _ _ _ π hπ φ hφ
  obtain ⟨ψ, hψ, hψφ⟩ := hP E A π hπ (φ.comp e.toMonoidHom) fun a ↦ (hφ a).preimage he
  refine ⟨ψ.comp e.symm.toMonoidHom, fun x ↦ (hψ x).preimage he', ?_⟩
  ext q
  have := DFunLike.congr_fun hψφ (e.symm q)
  simpa using this

/-- Finite lifts are transported along isomorphisms of topological groups. -/
theorem HasFiniteLifts.of_continuousMulEquiv {P Q : Type*} [Group P] [TopologicalSpace P]
    [Group Q] [TopologicalSpace Q] (hP : HasFiniteLifts P) (e : P ≃ₜ* Q) : HasFiniteLifts Q :=
  hP.of_mulEquiv e.toMulEquiv e.continuous e.symm.continuous

variable (α : Type u)

/-- **Open subgroups of `F̂(α)` have finite lifts** (finite embedding problems for them are
solvable). -/
theorem FreeHat.hasFiniteLifts_of_isOpen (H : Subgroup (FreeHat α))
    (hH : IsOpen (H : Set (FreeHat α))) : HasFiniteLifts H := by
  classical
  intro E A _ _ _ π hπ φ hφ
  set G := FreeGroup α
  let η : G →* FreeHat α := (eta (GrpCat.of G)).hom
  -- `H₀ = η⁻¹(H)` has finite index in `G`
  set H₀ : Subgroup G := H.comap η with hH₀
  haveI : Finite (FreeHat α ⧸ H) := Subgroup.quotient_finite_of_isOpen _ hH
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : H₀.FiniteIndex := ⟨by
    have h := Subgroup.relIndex_comap_ne_zero η (J := H) (K := ⊤)
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.FiniteIndex.index_ne_zero)
    rwa [Subgroup.comap_top, Subgroup.relIndex_top_right] at h⟩
  -- lift `φ|_{H₀}` on a basis of the free group `H₀`
  let φ₀ : H₀ →* A := φ.comp (η.subgroupComap H)
  let ψ₀ : H₀ →* E := IsFreeGroup.lift fun b ↦ (hπ (φ₀ (IsFreeGroup.of b))).choose
  have hψ₀ : π.comp ψ₀ = φ₀ :=
    IsFreeGroup.ext_hom fun b ↦ by
      simp only [MonoidHom.comp_apply, ψ₀, IsFreeGroup.lift_of]
      exact (hπ _).choose_spec
  -- a normal subgroup `L` of finite index of `G` with `L ∩ H₀ ⊆ ker ψ₀`
  haveI : ψ₀.ker.FiniteIndex := Subgroup.finiteIndex_ker ψ₀
  set K₁ : Subgroup G := ψ₀.ker.map H₀.subtype
  haveI : K₁.FiniteIndex := ⟨by
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩
  set L := K₁.normalCore
  haveI : L.FiniteIndex := inferInstance
  haveI : Finite (G ⧸ L) := Subgroup.finite_quotient_of_finiteIndex
  let q : G →* G ⧸ L := QuotientGroup.mk' L
  let q₀ : H₀ →* G ⧸ L := q.comp H₀.subtype
  have hker : q₀.ker ≤ ψ₀.ker := by
    intro x hx
    have hxL : (x : G) ∈ L := by
      rw [MonoidHom.mem_ker] at hx
      exact (QuotientGroup.eq_one_iff _).1 hx
    obtain ⟨k, hk, hkx⟩ := Subgroup.normalCore_le K₁ hxL
    have : k = x := Subgroup.subtype_injective H₀ hkx
    rwa [← this]
  -- `ψ̄ : q(H₀) → E`
  let ψbar : q₀.range →* E :=
    (QuotientGroup.lift q₀.ker ψ₀ hker).comp
      (QuotientGroup.quotientKerEquivRange q₀).symm.toMonoidHom
  have hψbar (x : H₀) : ψbar ⟨q₀ x, x, rfl⟩ = ψ₀ x := by
    have : (QuotientGroup.quotientKerEquivRange q₀).symm ⟨q₀ x, x, rfl⟩ =
        (QuotientGroup.mk x : H₀ ⧸ q₀.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [ψbar, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this,
      QuotientGroup.lift_mk]
  -- `q̂ : F̂(α) → G/L` maps `H` into `q(H₀)`
  let qhat : FreeHat α →* G ⧸ L := liftFinite q
  have happrox (h : H) {U : Set (FreeHat α)} (hU : IsOpen U) (hhU : (h : FreeHat α) ∈ U)
      (hUH : U ⊆ H) : ∃ x : H₀, (⟨η x, x.2⟩ : H) ∈ Subtype.val ⁻¹' U ∧ q₀ x = qhat h := by
    obtain ⟨x, hxU, hx⟩ := exists_etaFn_eq q hU hhU
    exact ⟨⟨x, hUH hxU⟩, hxU, hx⟩
  have hmem (h : H) : qhat h ∈ q₀.range := by
    obtain ⟨x, -, hx⟩ := happrox h hH h.2 subset_rfl
    exact ⟨x, hx⟩
  let k : H →* q₀.range := (qhat.comp H.subtype).codRestrict q₀.range hmem
  let ψ : H →* E := ψbar.comp k
  have hψk (h : H) (x : H₀) (hx : q₀ x = qhat h) : ψ h = ψ₀ x := by
    have : k h = ⟨q₀ x, x, rfl⟩ := Subtype.ext hx.symm
    simp only [ψ, MonoidHom.comp_apply, this, hψbar]
  refine ⟨ψ, fun e ↦ ?_, ?_⟩
  · -- the fibres of `ψ` are unions of fibres of `q̂`
    have : ψ ⁻¹' {e} = Subtype.val ⁻¹'
        (⋃ y ∈ {y : G ⧸ L | ∃ hy : y ∈ q₀.range, ψbar ⟨y, hy⟩ = e},
          {z : FreeHat α | qhat z = y}) := by
      ext h
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_setOf_eq,
        exists_prop]
      constructor
      · intro hh
        exact ⟨qhat h, ⟨hmem h, hh⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hye⟩, hyh⟩
        subst hyh
        exact hye
    rw [this]
    exact (isOpen_biUnion fun y _ ↦ isOpen_liftFinite_fiber q y).preimage continuous_subtype_val
  · ext h
    -- approximate `h` by `x ∈ H₀` with the same values under `q̂` and `φ`
    have hU : IsOpen (Subtype.val '' (φ ⁻¹' {φ h}) : Set (FreeHat α)) :=
      hH.isOpenMap_subtype_val _ (hφ _)
    obtain ⟨x, hxU, hx⟩ := happrox h hU ⟨h, rfl, rfl⟩ (by rintro _ ⟨y, -, rfl⟩; exact y.2)
    obtain ⟨y, hy, hyx⟩ := hxU
    have hyx' : y = ⟨η x, x.2⟩ := Subtype.ext hyx
    rw [MonoidHom.comp_apply, hψk h x hx, ← MonoidHom.comp_apply, hψ₀]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hyx'] at hy
    simp only [φ₀, MonoidHom.comp_apply]
    exact hy

/-- **Open subgroups of a group isomorphic to `F̂(α)` have finite lifts.** -/
theorem HasFiniteLifts.of_isOpen_of_continuousMulEquiv {P : Type*} [Group P] [TopologicalSpace P]
    (e : P ≃ₜ* FreeHat α) (H : Subgroup P) (hH : IsOpen (H : Set P)) : HasFiniteLifts H := by
  have hH' :
      IsOpen ((H.map e.toMulEquiv.toMonoidHom : Subgroup (FreeHat α)) : Set (FreeHat α)) := by
    rw [Subgroup.coe_map]
    exact e.toHomeomorph.isOpenMap _ hH
  let f : H ≃* H.map e.toMulEquiv.toMonoidHom := e.toMulEquiv.subgroupMap H
  have hf (h : H) : (f h : FreeHat α) = e h := rfl
  have hf' (y : H.map e.toMulEquiv.toMonoidHom) : (f.symm y : P) = e.symm y := by
    have := congrArg Subtype.val (f.apply_symm_apply y)
    rw [hf] at this
    rw [← this, ContinuousMulEquiv.symm_apply_apply]
  refine (FreeHat.hasFiniteLifts_of_isOpen α _ hH').of_mulEquiv f.symm ?_ ?_
  · refine continuous_induced_rng.2 ?_
    have : (Subtype.val ∘ f.symm : H.map e.toMulEquiv.toMonoidHom → P) =
        e.symm ∘ Subtype.val := funext hf'
    rw [this]
    exact e.symm.continuous.comp continuous_subtype_val
  · refine continuous_induced_rng.2 ?_
    have : (Subtype.val ∘ f.symm.symm : H → FreeHat α) = e ∘ Subtype.val := funext hf
    rw [this]
    exact e.continuous.comp continuous_subtype_val

end Pi1.Profinite
