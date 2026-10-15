/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Data.List.OfFn

/-!
# Surface groups

The topological fundamental group of a compact Riemann surface of genus `g` with `r` points
removed has the presentation

  `Π_{g,r} = ⟨a₁, b₁, …, a_g, b_g, c₁, …, c_r | ∏ᵢ [aᵢ, bᵢ] · ∏ⱼ cⱼ = 1⟩`

(`[x, y] = x y x⁻¹ y⁻¹`), where `cⱼ` is a loop around the `j`-th puncture. The conventions are
those of `GeneralizedAlbanese.SurfaceGroup` (lana-agents/generalized-albanese), so that the two
definitions agree.

## Main declarations

* `Pi1.SurfaceGen g r`, `Pi1.SurfaceGen.relator g r`, `Pi1.SurfaceGroup g r`;
* `Pi1.SurfaceGroup.cusp j`: the cuspidal generator `cⱼ`;
* `Pi1.SurfaceGroup.freeEquiv`: for `r = r' + 1 ≥ 1`, `Π_{g,r'+1}` is free on
  `a₁, b₁, …, a_g, b_g, c₁, …, c_{r'}` (the last cusp is eliminated by the relation);
* `Pi1.SurfaceGroup.IsHyperbolic g r`: `2g - 2 + r > 0`.
-/

@[expose] public section

namespace Pi1

/-- Generators of `Π_{g,r}`: `aᵢ, bᵢ` (`i < g`) and the cuspidal generators `cⱼ` (`j < r`). -/
inductive SurfaceGen (g r : ℕ) : Type
  | a : Fin g → SurfaceGen g r
  | b : Fin g → SurfaceGen g r
  | c : Fin r → SurfaceGen g r
  deriving DecidableEq

namespace SurfaceGen

variable {g r : ℕ}

/-- The product of commutators `∏ᵢ [aᵢ, bᵢ]` in a group, for families `x, y : Fin g → G`. -/
def commProd {G : Type*} [Group G] (x y : Fin g → G) : G :=
  (List.ofFn fun i : Fin g ↦ x i * y i * (x i)⁻¹ * (y i)⁻¹).prod

/-- The product `∏ⱼ zⱼ` (in order) of a family `z : Fin r → G`. -/
def ordProd {G : Type*} [Group G] (z : Fin r → G) : G := (List.ofFn z).prod

lemma map_commProd {G H : Type*} [Group G] [Group H] (φ : G →* H) (x y : Fin g → G) :
    φ (commProd x y) = commProd (fun i ↦ φ (x i)) (fun i ↦ φ (y i)) := by
  simp [commProd, map_list_prod, List.map_ofFn, Function.comp_def]

lemma map_ordProd {G H : Type*} [Group G] [Group H] (φ : G →* H) (z : Fin r → G) :
    φ (ordProd z) = ordProd (fun j ↦ φ (z j)) := by
  simp [ordProd, map_list_prod, List.map_ofFn, Function.comp_def]

lemma ordProd_succ {G : Type*} [Group G] (z : Fin (r + 1) → G) :
    ordProd z = ordProd (fun j : Fin r ↦ z j.castSucc) * z (Fin.last r) := by
  rw [ordProd, ordProd, List.ofFn_succ', List.prod_concat]

/-- The surface relator `∏ᵢ [aᵢ, bᵢ] · ∏ⱼ cⱼ`. -/
def relator (g r : ℕ) : FreeGroup (SurfaceGen g r) :=
  commProd (fun i ↦ FreeGroup.of (a i)) (fun i ↦ FreeGroup.of (b i)) *
    ordProd (fun j ↦ FreeGroup.of (c j))

end SurfaceGen

open SurfaceGen

/-- **The surface group** `Π_{g,r}` of a genus-`g` surface with `r` punctures. -/
abbrev SurfaceGroup (g r : ℕ) : Type := PresentedGroup {relator g r}

namespace SurfaceGroup

variable {g r : ℕ}

/-- `2g - 2 + r > 0`: the surface is hyperbolic. -/
def IsHyperbolic (g r : ℕ) : Prop := 2 < 2 * g + r

/-- The generator `aᵢ`. -/
def genA (i : Fin g) : SurfaceGroup g r := PresentedGroup.of (.a i)

/-- The generator `bᵢ`. -/
def genB (i : Fin g) : SurfaceGroup g r := PresentedGroup.of (.b i)

/-- The cuspidal generator `cⱼ`. -/
def cusp (j : Fin r) : SurfaceGroup g r := PresentedGroup.of (.c j)

/-- The surface relation `∏ᵢ [aᵢ, bᵢ] · ∏ⱼ cⱼ = 1` in `Π_{g,r}`. -/
theorem relation : commProd (genA (r := r)) (genB (g := g)) * ordProd (cusp (g := g)) = 1 := by
  have h : PresentedGroup.mk {relator g r} (relator g r) = 1 :=
    PresentedGroup.mk_eq_one_iff.2 (Subgroup.subset_normalClosure rfl)
  rw [relator, map_mul, map_commProd, map_ordProd] at h
  exact h

/-- Construct a homomorphism out of `Π_{g,r}` from images of the generators satisfying the
surface relation. -/
def lift {G : Type*} [Group G] (x y : Fin g → G) (z : Fin r → G)
    (h : commProd x y * ordProd z = 1) : SurfaceGroup g r →* G :=
  PresentedGroup.toGroup (rels := {relator g r})
    (f := fun s ↦ match s with
      | .a i => x i
      | .b i => y i
      | .c j => z j) (by
    rintro _ rfl
    rw [relator, map_mul, map_commProd, map_ordProd]
    simpa using h)

section lift

variable {G : Type*} [Group G] (x y : Fin g → G) (z : Fin r → G)
  (h : commProd x y * ordProd z = 1)

@[simp] lemma lift_genA (i : Fin g) : lift x y z h (genA i) = x i := PresentedGroup.toGroup.of _
@[simp] lemma lift_genB (i : Fin g) : lift x y z h (genB i) = y i := PresentedGroup.toGroup.of _
@[simp] lemma lift_cusp (j : Fin r) : lift x y z h (cusp j) = z j := PresentedGroup.toGroup.of _

end lift

/-- Homomorphisms out of `Π_{g,r}` are determined by the images of the generators. -/
theorem hom_ext {G : Type*} [Group G] {φ ψ : SurfaceGroup g r →* G}
    (ha : ∀ i, φ (genA i) = ψ (genA i)) (hb : ∀ i, φ (genB i) = ψ (genB i))
    (hc : ∀ j, φ (cusp j) = ψ (cusp j)) : φ = ψ := by
  refine PresentedGroup.ext fun s ↦ ?_
  cases s with
  | a i => exact ha i
  | b i => exact hb i
  | c j => exact hc j

/-! ### `Π_{g,r+1}` is free -/

/-- The embedding of generators `SurfaceGen g r → SurfaceGen g (r + 1)` (`cⱼ ↦ cⱼ`). -/
def embGen : SurfaceGen g r → SurfaceGen g (r + 1)
  | .a i => .a i
  | .b i => .b i
  | .c j => .c j.castSucc

/-- The image of the last cusp in the free group: `(∏ᵢ [aᵢ, bᵢ] · ∏_{j < r} cⱼ)⁻¹`. -/
def lastCuspWord (g r : ℕ) : FreeGroup (SurfaceGen g r) :=
  (commProd (fun i ↦ FreeGroup.of (SurfaceGen.a i)) (fun i ↦ FreeGroup.of (SurfaceGen.b i)) *
    ordProd (fun j : Fin r ↦ FreeGroup.of (SurfaceGen.c j)))⁻¹

/-- The homomorphism `Π_{g,r+1} → F(a, b, c_{<r})`. -/
def toFree : SurfaceGroup g (r + 1) →* FreeGroup (SurfaceGen g r) :=
  lift (fun i ↦ FreeGroup.of (.a i)) (fun i ↦ FreeGroup.of (.b i))
    (Fin.lastCases (lastCuspWord g r) fun j ↦ FreeGroup.of (.c j)) (by
      rw [ordProd_succ]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, lastCuspWord]
      rw [← mul_assoc, mul_inv_cancel])

/-- The homomorphism `F(a, b, c_{<r}) → Π_{g,r+1}`. -/
def ofFree : FreeGroup (SurfaceGen g r) →* SurfaceGroup g (r + 1) :=
  FreeGroup.lift fun s ↦ PresentedGroup.of (embGen s)

lemma ofFree_lastCuspWord : ofFree (lastCuspWord g r) = cusp (Fin.last r) := by
  have h := relation (g := g) (r := r + 1)
  rw [ordProd_succ] at h
  rw [lastCuspWord, map_inv, map_mul, map_commProd, map_ordProd]
  simp only [ofFree, FreeGroup.lift_apply_of, embGen]
  rw [inv_eq_iff_mul_eq_one, ← h, mul_assoc]
  rfl

/-- **`Π_{g,r+1}` is free** on `a₁, b₁, …, a_g, b_g, c₁, …, c_r`. -/
def freeEquiv : SurfaceGroup g (r + 1) ≃* FreeGroup (SurfaceGen g r) :=
  MonoidHom.toMulEquiv toFree ofFree
    (hom_ext
      (fun i ↦ by
        change ofFree (toFree (genA i)) = genA i
        rw [toFree, lift_genA]
        rfl)
      (fun i ↦ by
        change ofFree (toFree (genB i)) = genB i
        rw [toFree, lift_genB]
        rfl)
      (fun j ↦ by
        change ofFree (toFree (cusp j)) = cusp j
        rw [toFree, lift_cusp]
        refine Fin.lastCases ?_ (fun j ↦ ?_) j
        · rw [Fin.lastCases_last]
          exact ofFree_lastCuspWord
        · rw [Fin.lastCases_castSucc]
          rfl))
    (FreeGroup.ext_hom _ _ fun s ↦ by
      change toFree (ofFree (FreeGroup.of s)) = FreeGroup.of s
      rw [ofFree, FreeGroup.lift_apply_of]
      cases s with
      | a i => exact lift_genA _ _ _ _ i
      | b i => exact lift_genB _ _ _ _ i
      | c j =>
        change toFree (cusp j.castSucc) = _
        rw [toFree, lift_cusp, Fin.lastCases_castSucc])

lemma freeEquiv_apply (x : SurfaceGroup g (r + 1)) : freeEquiv x = toFree x := rfl

@[simp] lemma freeEquiv_genA (i : Fin g) :
    freeEquiv (genA (r := r + 1) i) = FreeGroup.of (.a i) := by
  rw [freeEquiv_apply, toFree, lift_genA]

@[simp] lemma freeEquiv_genB (i : Fin g) :
    freeEquiv (genB (r := r + 1) i) = FreeGroup.of (.b i) := by
  rw [freeEquiv_apply, toFree, lift_genB]

@[simp] lemma freeEquiv_cusp_castSucc (j : Fin r) :
    freeEquiv (cusp (g := g) j.castSucc) = FreeGroup.of (.c j) := by
  rw [freeEquiv_apply, toFree, lift_cusp, Fin.lastCases_castSucc]

@[simp] lemma freeEquiv_cusp_last :
    freeEquiv (cusp (g := g) (Fin.last r)) = lastCuspWord g r := by
  rw [freeEquiv_apply, toFree, lift_cusp, Fin.lastCases_last]

end SurfaceGroup

end Pi1
