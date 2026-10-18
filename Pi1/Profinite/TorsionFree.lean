/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Profinite.Slim
public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Torsion-freeness of profinite completions of free groups

We prove that the profinite completion `F̂(α)` of a free group is **torsion-free**
(`Pi1.Profinite.FreeHat.eq_one_of_isOfFinOrder`), for an arbitrary set `α` of generators.

The argument is elementary and only uses finite quotients. Say that a group `G` has the
**mod-`p²` lifting property** (`Pi1.Profinite.HasModSqLift G p`) if for every subgroup `K` of
finite index, every homomorphism `K → ℤ/p` lifts to a homomorphism `K → ℤ/p²`. Free groups have
this property for every `p`, since subgroups of free groups are free (Nielsen–Schreier, Mathlib's
`subgroupIsFreeOfIsFree`): lift the values on a basis.

**Key lemma** (`eq_one_of_pow_prime_eq_one`): if `G` has the mod-`p²` lifting property, then the
profinite completion `Ĝ` has no element of order `p`. Indeed, let `z ∈ Ĝ` with `z ^ p = 1`,
`z ≠ 1`, and let `f : G → P` be a homomorphism to a finite group with `a = f̂(z) ≠ 1` (finite
quotients separate points of `Ĝ`), so `a` has order `p`. On `K = f⁻¹⟨a⟩` (finite index) we have
`χ : K → ⟨a⟩ ≅ ℤ/p`; lift it to `ψ : K → ℤ/p²` and let `N ⊆ ker ψ` be normal of finite index in
`G`. Approximate `z` by `x ∈ G` with the same images in `P` and in `G/N`: then `f(x) = a`, so
`x ∈ K` and `χ(x) ≠ 0`, while `x ^ p ∈ N`, so `p · ψ(x) = 0` in `ℤ/p²`, whence
`χ(x) = ψ(x) mod p = 0` — a contradiction.

Consequently (`eq_one_of_isOfFinOrder`) `Ĝ` is torsion-free when `G` has the lifting property
for every prime `p`. Applied to free groups this gives the torsion-freeness of `F̂(α)`, and hence
of the profinite surface groups `Π̂_{g,r}` with `r ≥ 1` (`Pi1.SurfaceGroup.eq_one_of_isOfFinOrder`
in `Pi1.Surface.TorsionFree`): the geometric fundamental group of an affine hyperbolic curve in
characteristic `0` is torsion-free. This is the torsion-freeness used in the de-cuspidalisation
step `•` of [AbsTopI] Definition 4.2 (iii)(c).
-/

@[expose] public section

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology

universe u

namespace Pi1.Profinite

/-- **The mod-`p²` lifting property**: for every subgroup `K` of finite index in `G`, every
homomorphism `χ : K → ℤ/p` lifts along the reduction `ℤ/p² → ℤ/p` to a homomorphism
`ψ : K → ℤ/p²`. -/
def HasModSqLift (G : Type*) [Group G] (p : ℕ) : Prop :=
  ∀ (K : Subgroup G), K.FiniteIndex → ∀ χ : K →* Multiplicative (ZMod p),
    ∃ ψ : K →* Multiplicative (ZMod (p ^ 2)), ∀ k,
      (χ k).toAdd = ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) (ψ k).toAdd

/-- In `ℤ/p²`, an element killed by `p` reduces to `0` modulo `p`. -/
theorem ZMod.castHom_sq_eq_zero_of_nsmul_eq_zero {p : ℕ} [NeZero p] {b : ZMod (p ^ 2)}
    (hb : p • b = 0) : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) b = 0 := by
  have hp : p ≠ 0 := NeZero.ne p
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  have h1 : ((p * b.val : ℕ) : ZMod (p ^ 2)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, hb]
  rw [ZMod.natCast_eq_zero_iff] at h1
  exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hp) ((dvd_of_eq (pow_two p).symm).trans h1)

variable {G : Type u} [Group G]

/-- **No `p`-torsion in the completion**: if `G` has the mod-`p²` lifting property, then every
`z ∈ Ĝ` with `z ^ p = 1` is trivial. -/
theorem eq_one_of_pow_prime_eq_one {p : ℕ} [hp : Fact p.Prime] (hG : HasModSqLift G p)
    {z : completion (GrpCat.of G)} (hz : z ^ p = 1) : z = 1 := by
  classical
  by_contra hz1
  obtain ⟨P, _, _, f, hf⟩ : ∃ (P : Type u) (_ : Group P) (_ : Finite P) (f : G →* P),
      liftFinite f z ≠ 1 := by
    by_contra h
    push Not at h
    exact hz1 (eq_one_of_forall_liftFinite fun P _ _ f ↦ h P _ _ f)
  set a := liftFinite f z with ha_def
  have ha : orderOf a = p := orderOf_eq_prime (by rw [ha_def, ← map_pow, hz, map_one]) hf
  -- the character `χ : K = f⁻¹⟨a⟩ → ⟨a⟩ ≅ ℤ/p`
  set K : Subgroup G := (Subgroup.zpowers a).comap f with hK
  haveI : K.FiniteIndex := ⟨by
    have h := Subgroup.relIndex_comap_ne_zero f (J := Subgroup.zpowers a) (K := ⊤)
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.FiniteIndex.index_ne_zero)
    rwa [Subgroup.comap_top, Subgroup.relIndex_top_right] at h⟩
  let e : Subgroup.zpowers a ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq ((Nat.card_zpowers a).trans ha) (by simp)
  let χ : K →* Multiplicative (ZMod p) := e.toMonoidHom.comp (f.subgroupComap _)
  obtain ⟨ψ, hψ⟩ := hG K inferInstance χ
  -- a normal subgroup of finite index inside `ker ψ`
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩
  haveI : ψ.ker.FiniteIndex := Subgroup.finiteIndex_ker ψ
  set L : Subgroup G := ψ.ker.map K.subtype
  haveI : L.FiniteIndex := ⟨by
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩
  set N := L.normalCore
  obtain ⟨x, -, h1, h2⟩ := exists_etaFn_eq₂ (QuotientGroup.mk' N) f isOpen_univ (Set.mem_univ z)
  have hxK : x ∈ K := by
    change f x ∈ Subgroup.zpowers a
    rw [h2]
    exact Subgroup.mem_zpowers a
  have hxN : x ^ p ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, h1, ← map_pow, hz,
      map_one]
  obtain ⟨k', hk', hk'x⟩ := Subgroup.normalCore_le L hxN
  have hk'eq : k' = ⟨x, hxK⟩ ^ p := Subgroup.subtype_injective K (by simpa using hk'x)
  have hψp : p • (ψ ⟨x, hxK⟩).toAdd = 0 := by
    rw [← toAdd_pow, ← map_pow, ← hk'eq, MonoidHom.mem_ker.1 hk', toAdd_one]
  have hχ : χ ⟨x, hxK⟩ = 1 := by
    rw [← toAdd_eq_zero, hψ, ZMod.castHom_sq_eq_zero_of_nsmul_eq_zero hψp]
  apply hf
  have : e (f.subgroupComap _ ⟨x, hxK⟩) = 1 := hχ
  rw [map_eq_one_iff _ e.injective] at this
  have := congrArg Subtype.val this
  simpa [h2] using this

/-- **Torsion-freeness of the completion**: if `G` has the mod-`p²` lifting property for every
prime `p`, then every element of finite order of `Ĝ` is trivial. -/
theorem eq_one_of_isOfFinOrder (hG : ∀ p, p.Prime → HasModSqLift G p)
    {z : completion (GrpCat.of G)} (hz : IsOfFinOrder z) : z = 1 := by
  by_contra hz1
  have h0 : orderOf z ≠ 0 := (orderOf_pos_iff.2 hz).ne'
  have h1 : orderOf z ≠ 1 := fun h ↦ hz1 (orderOf_eq_one_iff.1 h)
  obtain ⟨p, hp, hpz⟩ := Nat.exists_prime_and_dvd h1
  haveI : Fact p.Prime := ⟨hp⟩
  have hw : orderOf (z ^ (orderOf z / p)) = p := orderOf_pow_orderOf_div h0 hpz
  have hwp : (z ^ (orderOf z / p)) ^ p = 1 := by
    have := pow_orderOf_eq_one (z ^ (orderOf z / p))
    rwa [hw] at this
  have := eq_one_of_pow_prime_eq_one (hG p hp) hwp
  rw [this, orderOf_one] at hw
  exact hp.one_lt.ne hw

/-- **Free groups have the mod-`p²` lifting property** (subgroups of free groups are free,
Nielsen–Schreier). -/
theorem hasModSqLift_of_isFreeGroup (F : Type*) [Group F] [IsFreeGroup F] (p : ℕ) [NeZero p] :
    HasModSqLift F p := by
  intro K _ χ
  refine ⟨IsFreeGroup.lift fun b ↦ Multiplicative.ofAdd
    (((χ (IsFreeGroup.of b)).toAdd.val : ℕ) : ZMod (p ^ 2)), fun k ↦ ?_⟩
  let red : Multiplicative (ZMod (p ^ 2)) →* Multiplicative (ZMod p) :=
    AddMonoidHom.toMultiplicative
      (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)).toAddMonoidHom
  have : χ = red.comp (IsFreeGroup.lift fun b ↦ Multiplicative.ofAdd
      (((χ (IsFreeGroup.of b)).toAdd.val : ℕ) : ZMod (p ^ 2))) := by
    refine IsFreeGroup.ext_hom fun b ↦ ?_
    simp [red, IsFreeGroup.lift_of]
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun this k)

variable (α : Type u)

/-- **The profinite completion `F̂(α)` of a free group is torsion-free.** -/
theorem FreeHat.eq_one_of_isOfFinOrder {z : FreeHat α} (hz : IsOfFinOrder z) : z = 1 :=
  Profinite.eq_one_of_isOfFinOrder
    (fun p hp ↦ haveI : NeZero p := ⟨hp.ne_zero⟩; hasModSqLift_of_isFreeGroup _ p) hz

end Pi1.Profinite
