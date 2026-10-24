/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Finite.Prod

/-!
# Finite quotients of surface groups with prescribed cuspidal orders

For a hyperbolic type `(g, r)` and `n > 0` we construct finite quotients of the surface group
`Π_{g,r}` (`Pi1.SurfaceGroup g r`) in which **every** cuspidal generator `cⱼ` has a prescribed
order, and whose order only involves the primes dividing `n`. This is the group-theoretic content
of the "observation" in [SemiAnbd, Example 2.10] (a hyperbolic Riemann surface admits Galois
coverings of degree a `Σ`-integer with prescribed ramification at the cusps), in the form needed
for the coherence and elevation conditions of [SemiAnbd, Definition 2.3, Definition 2.4].

## Main results

* `Pi1.SurfaceGroup.exists_finite_quotient_cusp_order`: **Lemma A.** For `n > 0` and `(g, r)`
  hyperbolic there is a finite quotient `ρ : Π_{g,r} ↠ Q` with `n ≤ |Q|`, every prime factor of
  `|Q|` dividing `n`, and `ρ(cⱼ)` of order exactly `n` for every `j`. The quotients are abelian
  (`r ≠ 1`) or the Heisenberg group mod `n` (`r = 1`, where `c₁ = (∏ᵢ [aᵢ, bᵢ])⁻¹`).
* `Pi1.SurfaceGroup.exists_elevated_quotient`: **the elevation property at a vertex**
  ([SemiAnbd, Definition 2.4 (i)]). For `n > 0` and `(g, r)` hyperbolic there is a finite quotient
  `ρ : Π_{g,r} ↠ P` with every prime factor of `|P|` dividing `n`, every `ρ(cⱼ)` of order exactly
  `n ^ 3`, and a subgroup `N ⊆ P` of order `≥ n` meeting every conjugate of every cuspidal
  subgroup `⟨ρ(cⱼ)⟩` trivially.
* `Pi1.SurfaceGroup.exists_finite_quotient_cusp_order_of_primes`,
  `Pi1.SurfaceGroup.exists_elevated_quotient_of_primes`: the same with the prime factors in a
  given set `S` of primes (pro-`Σ` version, `Σ = S`).

The elevation result comes from the product trick `Pi1.SurfaceGroup.exists_elevated_of_homs`: for
two finite quotients `ρ₁, ρ₂` with `ord ρ₁(cⱼ) ∣ ord ρ₂(cⱼ)`, the image `P` of `(ρ₁, ρ₂)` and
`N = P ∩ (Q₁ × 1) ≅ ρ₁(ker ρ₂)` work (`Pi1.SurfaceGroup.ker_inf_conj_zpowers_eq_bot`). The
diagonal `(ρ, ρ)` does not work inside its image (the image is the diagonal, which meets `Q × 1`
trivially). For `g ≥ 1` we take `ρ₂` from Lemma A at level `n ^ 3` and `ρ₁ : aᵢ ↦ 1 ∈ ℤ/(|Q₂| n)`;
for `g = 0` (so `r ≥ 3`) we take `ρ₂` abelian at level `n ^ 3` and `ρ₁` the Heisenberg group mod
`n` with `c₁, c₂ ↦` the two standard generators, so that `ρ₁([c₁, c₂])` is central of order `n`.

## References

* [SemiAnbd] S. Mochizuki, *Semi-graphs of Anabelioids*.
-/

@[expose] public section

open Pointwise

namespace Pi1

/-! ### The Heisenberg group mod `n` -/

/-- The Heisenberg group mod `n`: triples `(x, y, z)` of residues mod `n` with
`(x, y, z) (x', y', z') = (x + x', y + y', z + z' + x y')`. -/
@[ext]
structure HeisenbergMod (n : ℕ) where
  /-- The first coordinate. -/
  x : ZMod n
  /-- The second coordinate. -/
  y : ZMod n
  /-- The central coordinate. -/
  z : ZMod n

namespace HeisenbergMod

variable {n : ℕ}

instance : Mul (HeisenbergMod n) := ⟨fun p q ↦ ⟨p.x + q.x, p.y + q.y, p.z + q.z + p.x * q.y⟩⟩
instance : One (HeisenbergMod n) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (HeisenbergMod n) := ⟨fun p ↦ ⟨-p.x, -p.y, -p.z + p.x * p.y⟩⟩

@[simp] lemma mul_x (p q : HeisenbergMod n) : (p * q).x = p.x + q.x := rfl
@[simp] lemma mul_y (p q : HeisenbergMod n) : (p * q).y = p.y + q.y := rfl
@[simp] lemma mul_z (p q : HeisenbergMod n) : (p * q).z = p.z + q.z + p.x * q.y := rfl
@[simp] lemma one_x : (1 : HeisenbergMod n).x = 0 := rfl
@[simp] lemma one_y : (1 : HeisenbergMod n).y = 0 := rfl
@[simp] lemma one_z : (1 : HeisenbergMod n).z = 0 := rfl
@[simp] lemma inv_x (p : HeisenbergMod n) : p⁻¹.x = -p.x := rfl
@[simp] lemma inv_y (p : HeisenbergMod n) : p⁻¹.y = -p.y := rfl
@[simp] lemma inv_z (p : HeisenbergMod n) : p⁻¹.z = -p.z + p.x * p.y := rfl

instance : Group (HeisenbergMod n) where
  mul_assoc p q s := by ext <;> simp <;> ring
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by ext <;> simp

/-- `HeisenbergMod n ≃ (ℤ/n)³` as types. -/
def equivTriple : HeisenbergMod n ≃ ZMod n × ZMod n × ZMod n where
  toFun p := (p.x, p.y, p.z)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [NeZero n] : Finite (HeisenbergMod n) := Finite.of_equiv _ equivTriple.symm

lemma card : Nat.card (HeisenbergMod n) = n ^ 3 := by
  rw [Nat.card_congr equivTriple, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  ring

/-- The generator `(1, 0, 0)`. -/
def genX : HeisenbergMod n := ⟨1, 0, 0⟩

/-- The generator `(0, 1, 0)`. -/
def genY : HeisenbergMod n := ⟨0, 1, 0⟩

/-- The central embedding `ℤ/n → HeisenbergMod n`, `z ↦ (0, 0, z)`. -/
def center : Multiplicative (ZMod n) →* HeisenbergMod n where
  toFun z := ⟨0, 0, z.toAdd⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

lemma center_injective : Function.Injective (center (n := n)) := fun _ _ h ↦
  congrArg HeisenbergMod.z h

lemma commutator_genX_genY :
    genX * genY * genX⁻¹ * genY⁻¹ = center (n := n) (Multiplicative.ofAdd 1) := by
  ext <;> simp [genX, genY, center]

lemma orderOf_commutator_genX_genY :
    orderOf (genX * genY * genX⁻¹ * genY⁻¹ : HeisenbergMod n) = n := by
  rw [commutator_genX_genY, orderOf_injective _ center_injective, orderOf_ofAdd_eq_addOrderOf,
    ZMod.addOrderOf_one]

end HeisenbergMod

namespace SurfaceGroup

open SurfaceGen HeisenbergMod

variable {g r n : ℕ}

/-! ### Some homomorphisms to finite groups -/

/-- `aᵢ ↦ 1 ∈ ℤ/m`, `bᵢ, cⱼ ↦ 0`. -/
def genusAbHom (m : ℕ) : SurfaceGroup g r →* Multiplicative (ZMod m) :=
  lift (fun _ ↦ Multiplicative.ofAdd 1) (fun _ ↦ 1) (fun _ ↦ 1) (by
    simp [commProd, ordProd])

@[simp] lemma genusAbHom_genA (m : ℕ) (i : Fin g) :
    genusAbHom (r := r) m (genA i) = Multiplicative.ofAdd 1 :=
  lift_genA _ _ _ _ i

@[simp] lemma genusAbHom_cusp (m : ℕ) (j : Fin r) : genusAbHom (g := g) m (cusp j) = 1 :=
  lift_cusp _ _ _ _ j

/-- The abelian quotient `Π_{g,r} → (ℤ/m)^r`, `cⱼ ↦ eⱼ - e_{j+1}` (indices mod `r`),
`aᵢ, bᵢ ↦ 0`. -/
def cuspAbHom (m : ℕ) : SurfaceGroup g r →* Multiplicative (Fin r → ZMod m) :=
  lift (fun _ ↦ 1) (fun _ ↦ 1)
    (fun j ↦ Multiplicative.ofAdd (Pi.single j 1 - Pi.single (finRotate r j) 1)) (by
      simp only [commProd, ordProd, mul_one, inv_one, List.prod_ofFn, Finset.prod_const_one,
        one_mul]
      rw [← ofAdd_sum, Finset.sum_sub_distrib,
        Equiv.sum_comp (finRotate r) (fun j ↦ (Pi.single j 1 : Fin r → ZMod m)), sub_self,
        ofAdd_zero])

lemma orderOf_cuspAbHom_cusp (m : ℕ) (hr : 1 < r) (j : Fin r) :
    orderOf (cuspAbHom (g := g) m (cusp j)) = m := by
  have hj : finRotate r j ≠ j := by
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
    rw [Ne, Fin.ext_iff, coe_finRotate]
    split_ifs with h
    · simp [h]
    · omega
  rw [cuspAbHom, lift_cusp, orderOf_ofAdd_eq_addOrderOf]
  refine Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero ?_) ?_
  · funext k
    simp [nsmul_eq_mul]
  · have := addOrderOf_map_dvd (Pi.evalAddMonoidHom (fun _ : Fin r ↦ ZMod m) j)
      (Pi.single j 1 - Pi.single (finRotate r j) 1)
    rwa [Pi.evalAddMonoidHom_apply, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne' hj, sub_zero, ZMod.addOrderOf_one] at this

/-- For `r = 1`: `Π_{g+1,1} → HeisenbergMod n`, `a₁ ↦ X`, `b₁ ↦ Y`, the other `aᵢ, bᵢ ↦ 1`,
`c₁ ↦ [X, Y]⁻¹`. -/
def heisGenusHom (n g : ℕ) : SurfaceGroup (g + 1) 1 →* HeisenbergMod n :=
  lift (Fin.cases genX fun _ ↦ 1) (Fin.cases genY fun _ ↦ 1)
    (fun _ ↦ (genX * genY * genX⁻¹ * genY⁻¹)⁻¹) (by
      simp [commProd, ordProd, List.ofFn_succ, mul_assoc])

/-- For `g = 0`: `Π_{0,r+3} → HeisenbergMod n`, `c₁ ↦ X`, `c₂ ↦ Y`, `c₃ ↦ (X Y)⁻¹`, the other
`cⱼ ↦ 1`. -/
def heisCuspHom (n r : ℕ) : SurfaceGroup 0 (r + 3) →* HeisenbergMod n :=
  lift Fin.elim0 Fin.elim0
    (Fin.cases genX (Fin.cases genY (Fin.cases (genX * genY)⁻¹ fun _ ↦ 1))) (by
      simp [commProd, ordProd, List.ofFn_succ, mul_assoc])

/-! ### Lemma A -/

lemma prime_dvd_of_card_eq_pow {G : Type*} {k : ℕ} (hG : Nat.card G = n ^ k) {p : ℕ}
    (hp : p.Prime) (hpG : p ∣ Nat.card G) : p ∣ n :=
  hp.dvd_of_dvd_pow (hG ▸ hpG)

/-- Lemma A from a homomorphism to a finite group: pass to the image. -/
theorem exists_finite_quotient_of_hom {G : Type} [Group G] [Finite G]
    (f : SurfaceGroup g r →* G) (hG : ∀ p, p.Prime → p ∣ Nat.card G → p ∣ n)
    (x : SurfaceGroup g r) (hx : orderOf (f x) = n) (hc : ∀ j, orderOf (f (cusp j)) = n) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (ρ : SurfaceGroup g r →* Q),
      Function.Surjective ρ ∧ n ≤ Nat.card Q ∧ (∀ p, p.Prime → p ∣ Nat.card Q → p ∣ n) ∧
        ∀ j, orderOf (ρ (cusp j)) = n := by
  have key : ∀ y, orderOf (f.rangeRestrict y) = orderOf (f y) := fun y ↦ by
    rw [← Subgroup.orderOf_coe, MonoidHom.coe_rangeRestrict]
  refine ⟨f.range, inferInstance, inferInstance, f.rangeRestrict, f.rangeRestrict_surjective,
    ?_, fun p hp hpd ↦ hG p hp (hpd.trans (Subgroup.card_subgroup_dvd_card _)),
    fun j ↦ (key _).trans (hc j)⟩
  rw [← hx, ← key]
  exact orderOf_le_card

/-- **Lemma A** (cf. [SemiAnbd, Example 2.10]): for `n > 0` and `(g, r)` hyperbolic, `Π_{g,r}`
has a finite quotient `Q` with `n ≤ |Q|`, all prime factors of `|Q|` dividing `n`, in which every
cuspidal generator `cⱼ` has order exactly `n`. -/
theorem exists_finite_quotient_cusp_order (hn : 0 < n) (h : IsHyperbolic g r) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (ρ : SurfaceGroup g r →* Q),
      Function.Surjective ρ ∧ n ≤ Nat.card Q ∧ (∀ p, p.Prime → p ∣ Nat.card Q → p ∣ n) ∧
        ∀ j, orderOf (ρ (cusp j)) = n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  unfold IsHyperbolic at h
  rcases r with _ | _ | r
  · -- `r = 0`, `g ≥ 2`
    refine exists_finite_quotient_of_hom (genusAbHom n)
      (fun p hp ↦ prime_dvd_of_card_eq_pow (k := 1) (by rw [pow_one]; exact Nat.card_zmod n) hp)
      (genA ⟨0, by omega⟩) ?_ (fun j ↦ j.elim0)
    rw [genusAbHom_genA, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  · -- `r = 1`, `g ≥ 1`: the Heisenberg group
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hc : ∀ j, orderOf (heisGenusHom n g (cusp j)) = n := fun j ↦ by
      rw [heisGenusHom, lift_cusp, orderOf_inv, orderOf_commutator_genX_genY]
    exact exists_finite_quotient_of_hom (heisGenusHom n g)
      (fun p hp ↦ prime_dvd_of_card_eq_pow HeisenbergMod.card hp) (cusp 0) (hc 0) hc
  · -- `r ≥ 2`: abelian
    have hc := orderOf_cuspAbHom_cusp (g := g) n (by omega : 1 < r + 2)
    refine exists_finite_quotient_of_hom (cuspAbHom n)
      (fun p hp ↦ prime_dvd_of_card_eq_pow (k := r + 2) ?_ hp) (cusp 0) (hc 0) hc
    change Nat.card (Fin (r + 2) → ZMod n) = _
    rw [Nat.card_pi, Nat.card_zmod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Lemma A for a set `S` of primes**: if every prime factor of `n` is in `S`, then so is every
prime factor of `|Q|`. -/
theorem exists_finite_quotient_cusp_order_of_primes {S : Set ℕ} (hn : 0 < n)
    (hS : ∀ p, p.Prime → p ∣ n → p ∈ S) (h : IsHyperbolic g r) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (ρ : SurfaceGroup g r →* Q),
      Function.Surjective ρ ∧ n ≤ Nat.card Q ∧ (∀ p, p.Prime → p ∣ Nat.card Q → p ∈ S) ∧
        ∀ j, orderOf (ρ (cusp j)) = n := by
  obtain ⟨Q, iG, iF, ρ, hs, hcard, hp, hc⟩ := exists_finite_quotient_cusp_order hn h
  exact ⟨Q, iG, iF, ρ, hs, hcard, fun p hp' hpQ ↦ hS p hp' (hp p hp' hpQ), hc⟩

/-! ### Elevation -/

/-- The kernel of a homomorphism `φ` meets every conjugate of `⟨z⟩` trivially as soon as `φ` is
injective on `⟨z⟩`. -/
theorem ker_inf_conj_zpowers_eq_bot {P Q : Type*} [Group P] [Group Q] (φ : P →* Q) (z : P)
    (hz : ∀ k : ℤ, φ z ^ k = 1 → z ^ k = 1) (q : P) :
    φ.ker ⊓ (ConjAct.toConjAct q • Subgroup.zpowers z) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_inf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, Subgroup.mem_zpowers_iff] at hy
  obtain ⟨hy, k, hk⟩ := hy
  have h1 : φ z ^ k = 1 := by
    rw [← map_zpow, hk]
    simp [MonoidHom.mem_ker.1 hy]
  rw [hz k h1] at hk
  exact Subgroup.mem_bot.2 (conj_eq_one_iff.1 hk.symm)

/-- **The product trick for elevation.** Let `ρ₁ : Π_{g,r} → Q₁`, `ρ₂ : Π_{g,r} → Q₂` be
homomorphisms to finite groups with `ord ρ₁(cⱼ) ∣ ord ρ₂(cⱼ)` for all `j`, and `x ∈ ker ρ₂`.
Then the image `P` of `(ρ₁, ρ₂)` has `ord(cⱼ) = ord ρ₂(cⱼ)`, and `N = P ∩ (Q₁ × 1)` has order
`≥ ord ρ₁(x)` and meets every conjugate of every `⟨cⱼ⟩` in `P` trivially. -/
theorem exists_elevated_of_homs {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] [Finite Q₁] [Finite Q₂]
    (ρ₁ : SurfaceGroup g r →* Q₁) (ρ₂ : SurfaceGroup g r →* Q₂)
    (hdvd : ∀ j, orderOf (ρ₁ (cusp j)) ∣ orderOf (ρ₂ (cusp j)))
    (x : SurfaceGroup g r) (hx : ρ₂ x = 1) :
    ∃ (P : Type) (_ : Group P) (_ : Finite P) (ρ : SurfaceGroup g r →* P) (N : Subgroup P),
      Function.Surjective ρ ∧ Nat.card P ∣ Nat.card Q₁ * Nat.card Q₂ ∧
        (∀ j, orderOf (ρ (cusp j)) = orderOf (ρ₂ (cusp j))) ∧ orderOf (ρ₁ x) ≤ Nat.card N ∧
          ∀ j (q : P), N ⊓ (ConjAct.toConjAct q • Subgroup.zpowers (ρ (cusp j))) = ⊥ := by
  set f := ρ₁.prod ρ₂
  have key : ∀ y, orderOf (f.rangeRestrict y) = (orderOf (ρ₁ y)).lcm (orderOf (ρ₂ y)) :=
    fun y ↦ by
      rw [← Subgroup.orderOf_coe, MonoidHom.coe_rangeRestrict, MonoidHom.prod_apply,
        Prod.orderOf_mk]
  let N : Subgroup f.range := ((MonoidHom.snd Q₁ Q₂).comp f.range.subtype).ker
  have hxN : f.rangeRestrict x ∈ N := by
    simp [N, MonoidHom.mem_ker, f, hx]
  refine ⟨f.range, inferInstance, inferInstance, f.rangeRestrict, N, f.rangeRestrict_surjective,
    ?_, fun j ↦ by rw [key, Nat.lcm_eq_right (hdvd j)], ?_, fun j q ↦ ?_⟩
  · rw [← Nat.card_prod]
    exact Subgroup.card_subgroup_dvd_card _
  · have h := orderOf_le_card (G := N) (x := ⟨_, hxN⟩)
    rwa [Subgroup.orderOf_mk, key, hx, orderOf_one, Nat.lcm_one_right] at h
  · refine ker_inf_conj_zpowers_eq_bot _ _ (fun k hk ↦ ?_) q
    replace hk : ρ₂ (cusp j) ^ k = 1 := by simpa [f] using hk
    have h2 : (orderOf (ρ₂ (cusp j)) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.2 hk
    have h1 : ρ₁ (cusp j) ^ k = 1 :=
      orderOf_dvd_iff_zpow_eq_one.1 ((Int.natCast_dvd_natCast.2 (hdvd j)).trans h2)
    ext
    · simp [f, h1]
    · simp [f, hk]

/-- **Elevation at a vertex** ([SemiAnbd, Definition 2.4 (i)], cf. [SemiAnbd, Example 2.10]):
for `n > 0` and `(g, r)` hyperbolic there is a finite quotient `ρ : Π_{g,r} ↠ P`, all of whose
prime factors divide `n`, in which every cuspidal generator has order exactly `n ^ 3`, together
with a subgroup `N ⊆ P` of order `≥ n` meeting every conjugate of every `⟨ρ(cⱼ)⟩` trivially. -/
theorem exists_elevated_quotient (hn : 0 < n) (h : IsHyperbolic g r) :
    ∃ (P : Type) (_ : Group P) (_ : Finite P) (ρ : SurfaceGroup g r →* P) (N : Subgroup P),
      Function.Surjective ρ ∧ (∀ p, p.Prime → p ∣ Nat.card P → p ∣ n) ∧
        (∀ j, orderOf (ρ (cusp j)) = n ^ 3) ∧ n ≤ Nat.card N ∧
          ∀ j (q : P), N ⊓ (ConjAct.toConjAct q • Subgroup.zpowers (ρ (cusp j))) = ⊥ := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · -- `g = 0`, `r ≥ 3`
    have hr : 3 ≤ r := by unfold IsHyperbolic at h; omega
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 3 := ⟨r - 3, by omega⟩
    haveI : NeZero (n ^ 3) := ⟨by positivity⟩
    have hc := orderOf_cuspAbHom_cusp (g := 0) (n ^ 3) (by omega : 1 < r + 3)
    let c₀ : SurfaceGroup 0 (r + 3) := cusp 0
    let c₁ : SurfaceGroup 0 (r + 3) := cusp (Fin.succ 0)
    have hx : cuspAbHom (n ^ 3) (c₀ * c₁ * c₀⁻¹ * c₁⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul,
        mul_comm]
    obtain ⟨P, iG, iF, ρ, N, hs, hcard, hcusp, hN, hconj⟩ :=
      exists_elevated_of_homs (heisCuspHom n r) (cuspAbHom (n ^ 3)) (fun j ↦ by
        rw [hc j, ← HeisenbergMod.card]; exact orderOf_dvd_natCard _) _ hx
    refine ⟨P, iG, iF, ρ, N, hs, fun p hp hpP ↦ ?_, fun j ↦ (hcusp j).trans (hc j), ?_, hconj⟩
    · have hQ₂ : Nat.card (Multiplicative (Fin (r + 3) → ZMod (n ^ 3))) = n ^ (3 * (r + 3)) := by
        change Nat.card (Fin (r + 3) → ZMod (n ^ 3)) = _
        rw [Nat.card_pi, Nat.card_zmod, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          pow_mul]
      rw [HeisenbergMod.card, hQ₂, ← pow_add] at hcard
      exact hp.dvd_of_dvd_pow (hpP.trans hcard)
    · have : heisCuspHom n r (c₀ * c₁ * c₀⁻¹ * c₁⁻¹) = genX * genY * genX⁻¹ * genY⁻¹ := by
        simp only [c₀, c₁, heisCuspHom, map_mul, map_inv, lift_cusp]
        rfl
      rwa [this, orderOf_commutator_genX_genY] at hN
  · -- `g ≥ 1`
    obtain ⟨Q₂, _, _, ρ₂, -, -, hp₂, hc₂⟩ :=
      exists_finite_quotient_cusp_order (n := n ^ 3) (by positivity) h
    set c := Nat.card Q₂
    have hc0 : 0 < c := Nat.card_pos
    haveI : NeZero (c * n) := ⟨by positivity⟩
    let a : SurfaceGroup g r := genA ⟨0, hg⟩
    obtain ⟨P, iG, iF, ρ, N, hs, hcard, hcusp, hN, hconj⟩ :=
      exists_elevated_of_homs (genusAbHom (c * n)) ρ₂ (fun j ↦ by simp) (a ^ c) (by
        rw [map_pow]; exact pow_card_eq_one')
    refine ⟨P, iG, iF, ρ, N, hs, fun p hp hpP ↦ ?_, fun j ↦ (hcusp j).trans (hc₂ j), ?_, hconj⟩
    · have := hpP.trans hcard
      rw [show Nat.card (Multiplicative (ZMod (c * n))) = c * n from Nat.card_zmod _,
        (Nat.Prime.prime hp).dvd_mul, (Nat.Prime.prime hp).dvd_mul] at this
      rcases this with (h1 | h1) | h1
      · exact hp.dvd_of_dvd_pow (hp₂ p hp h1)
      · exact h1
      · exact hp.dvd_of_dvd_pow (hp₂ p hp h1)
    · have : orderOf (genusAbHom (c * n) (a ^ c)) = n := by
        rw [map_pow, genusAbHom_genA, ← ofAdd_nsmul, orderOf_ofAdd_eq_addOrderOf, nsmul_one,
          ZMod.addOrderOf_coe _ (NeZero.ne _), Nat.gcd_mul_right_left,
          Nat.mul_div_cancel_left _ hc0]
      rwa [this] at hN

/-- **Elevation for a set `S` of primes**: if every prime factor of `n` is in `S`, then so is
every prime factor of `|P|`. -/
theorem exists_elevated_quotient_of_primes {S : Set ℕ} (hn : 0 < n)
    (hS : ∀ p, p.Prime → p ∣ n → p ∈ S) (h : IsHyperbolic g r) :
    ∃ (P : Type) (_ : Group P) (_ : Finite P) (ρ : SurfaceGroup g r →* P) (N : Subgroup P),
      Function.Surjective ρ ∧ (∀ p, p.Prime → p ∣ Nat.card P → p ∈ S) ∧
        (∀ j, orderOf (ρ (cusp j)) = n ^ 3) ∧ n ≤ Nat.card N ∧
          ∀ j (q : P), N ⊓ (ConjAct.toConjAct q • Subgroup.zpowers (ρ (cusp j))) = ⊥ := by
  obtain ⟨P, iG, iF, ρ, N, hs, hp, hc, hN, hconj⟩ := exists_elevated_quotient hn h
  exact ⟨P, iG, iF, ρ, N, hs, fun p hp' hpP ↦ hS p hp' (hp p hp' hpP), hc, hN, hconj⟩

end SurfaceGroup

end Pi1
