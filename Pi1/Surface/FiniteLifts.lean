/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.Profinite
public import Pi1.Profinite.FiniteLifts
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Proper surface groups are not open subgroups of free profinite groups

For `g ≥ 1` the profinite surface group `Π̂_{g,0}` of a *proper* curve of genus `g` does **not**
have finite lifts (`Pi1.SurfaceGroup.not_hasFiniteLifts`): the embedding problem
`D₄ ↠ D₄/Z(D₄) ≅ (ℤ/2)²` for `φ : Π̂_{g,0} → (ℤ/2)²`, `a₁ ↦ r`, `b₁ ↦ s`, `aᵢ, bᵢ ↦ 1` (`i ≥ 2`)
has no solution, because for any lifts `âᵢ, b̂ᵢ ∈ D₄` the product `∏ᵢ [âᵢ, b̂ᵢ]` equals the central
involution `r²` (the commutators with `i ≥ 2` vanish since `âᵢ, b̂ᵢ` are central), while the
surface relation forces it to be `1`. (Cohomologically: the class of the extension `D₄` pulls
back to a nonzero element of `H²(Π̂_{g,0}, ℤ/2)`, whereas `cd ≤ 1` for open subgroups of free
profinite groups, [NSW] (3.5.6), (3.5.15).)

On the other hand, open subgroups of the profinite completion of a free group have finite lifts
(`Pi1.Profinite.FreeHat.hasFiniteLifts_of_isOpen`). Hence:

* `Pi1.SurfaceGroup.isEmpty_continuousMulEquiv_of_isOpen_freeHat`: **no open subgroup of a group
  isomorphic to `F̂(α)` is isomorphic to `Π̂_{g',0}` with `g' ≥ 1`**;
* `Pi1.SurfaceGroup.isEmpty_continuousMulEquiv_of_isOpen`: the same for open subgroups of a group
  isomorphic to `Π̂_{g,r}` with `r ≥ 1` (which is free, `profiniteFreeEquiv`): an open subgroup of
  the geometric fundamental group `Δ_X` of an affine hyperbolic curve is never the geometric
  fundamental group of a proper curve of positive genus.
-/

@[expose] public section

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology

namespace Pi1

open Profinite SurfaceGen

namespace SurfaceGroup

/-- The reduction `D₄ → D₂ = (ℤ/2)²`, `r i ↦ r (i mod 2)`, `sr i ↦ sr (i mod 2)`; its kernel is
the centre `{1, r²}` of `D₄`. -/
def dihedralRed : DihedralGroup 4 →* DihedralGroup 2 where
  toFun
    | .r i => .r (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) i)
    | .sr i => .sr (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) i)
  map_one' := by
    change DihedralGroup.r (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) 0) = DihedralGroup.r 0
    rw [map_zero]
  map_mul' := by
    rintro (i | i) (j | j) <;> simp [map_add, map_sub]

lemma dihedralRed_surjective : Function.Surjective dihedralRed := by decide

/-- Elements of `D₄` over `1 ∈ D₂` are central. -/
lemma commutator_eq_one_of_dihedralRed_eq_one :
    ∀ a b : DihedralGroup 4, dihedralRed a = 1 → a * b * a⁻¹ * b⁻¹ = 1 := by decide

/-- Lifts of `r, s ∈ D₂` to `D₄` have commutator `r²`. -/
lemma commutator_eq_of_dihedralRed :
    ∀ a b : DihedralGroup 4, dihedralRed a = .r 1 → dihedralRed b = .sr 0 →
      a * b * a⁻¹ * b⁻¹ = .r 2 := by decide

lemma dihedral_two_commutator : ∀ a b : DihedralGroup 2, a * b * a⁻¹ * b⁻¹ = 1 := by decide

/-- A product `∏ᵢ fᵢ` (in order) all of whose factors except `f i₀` are trivial is `f i₀`. -/
lemma prod_ofFn_eq_of_eq_one {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (f : Fin n → M) (i₀ : Fin n), (∀ i, i ≠ i₀ → f i = 1) → (List.ofFn f).prod = f i₀
  | 0, _, i₀, _ => i₀.elim0
  | n + 1, f, i₀, h => by
    rw [List.ofFn_succ, List.prod_cons]
    cases i₀ using Fin.cases with
    | zero =>
      have h1 : (List.ofFn fun i : Fin n ↦ f i.succ).prod = 1 := by
        refine List.prod_eq_one ?_
        simp only [List.mem_ofFn, forall_exists_index]
        rintro _ i rfl
        exact h _ (Fin.succ_ne_zero i)
      rw [h1, mul_one]
    | succ i₀ =>
      rw [h 0 (Fin.succ_ne_zero i₀).symm, one_mul,
        prod_ofFn_eq_of_eq_one (fun i ↦ f i.succ) i₀ fun i hi ↦ h _ (by simpa using hi)]

variable {g : ℕ}

/-- The images `a₁ ↦ r`, `aᵢ ↦ 1` (`i ≥ 2`) in `D₂`. -/
def kleinA (hg : 0 < g) (i : Fin g) : DihedralGroup 2 := if i = ⟨0, hg⟩ then .r 1 else 1

/-- The images `b₁ ↦ s`, `bᵢ ↦ 1` (`i ≥ 2`) in `D₂`. -/
def kleinB (hg : 0 < g) (i : Fin g) : DihedralGroup 2 := if i = ⟨0, hg⟩ then .sr 0 else 1

lemma kleinA_relation (hg : 0 < g) :
    commProd (kleinA hg) (kleinB hg) * ordProd (Fin.elim0 : Fin 0 → DihedralGroup 2) = 1 := by
  rw [ordProd, List.ofFn_zero, List.prod_nil, mul_one, commProd,
    List.prod_eq_one]
  simp only [List.mem_ofFn, forall_exists_index]
  rintro _ i rfl
  exact dihedral_two_commutator _ _

/-- The homomorphism `Π_{g,0} → D₂`, `a₁ ↦ r`, `b₁ ↦ s`, all other generators `↦ 1`. -/
def kleinHom (hg : 0 < g) : SurfaceGroup g 0 →* DihedralGroup 2 :=
  lift (kleinA hg) (kleinB hg) Fin.elim0 (kleinA_relation hg)

/-- **`Π̂_{g,0}` does not have finite lifts for `g ≥ 1`**: the embedding problem
`D₄ ↠ D₂` for `Π̂_{g,0} → D₂`, `a₁ ↦ r`, `b₁ ↦ s`, is not solvable. -/
theorem not_hasFiniteLifts (hg : 0 < g) : ¬ HasFiniteLifts.{0} (ProfiniteSurfaceGroup g 0) := by
  intro h
  obtain ⟨ψ, -, hψ⟩ := h (DihedralGroup 4) (DihedralGroup 2) dihedralRed dihedralRed_surjective
    (liftFinite (kleinHom hg)) (isOpen_liftFinite_fiber _)
  let ψd : SurfaceGroup g 0 →* DihedralGroup 4 := ψ.comp (eta (GrpCat.of (SurfaceGroup g 0))).hom
  have hred (x : SurfaceGroup g 0) : dihedralRed (ψd x) = kleinHom hg x := by
    have := DFunLike.congr_fun hψ (etaFn (GrpCat.of (SurfaceGroup g 0)) x)
    rw [MonoidHom.comp_apply, liftFinite_eta] at this
    exact this
  have hrel := congrArg ψd (relation (g := g) (r := 0))
  rw [map_one, map_mul, map_commProd, map_ordProd, ordProd, List.ofFn_zero, List.prod_nil,
    mul_one, commProd, prod_ofFn_eq_of_eq_one _ ⟨0, hg⟩] at hrel
  · rw [commutator_eq_of_dihedralRed _ _ (by simp [hred, kleinHom, kleinA])
      (by simp [hred, kleinHom, kleinB])] at hrel
    exact absurd hrel (by decide)
  · intro i hi
    exact commutator_eq_one_of_dihedralRed_eq_one _ _ (by simp [hred, kleinHom, kleinA, hi])

/-- **No group with finite lifts is isomorphic to `Π̂_{g,0}`, `g ≥ 1`.** -/
theorem isEmpty_continuousMulEquiv_of_hasFiniteLifts {P : Type*} [Group P] [TopologicalSpace P]
    (hP : HasFiniteLifts.{0} P) (hg : 0 < g) : IsEmpty (P ≃ₜ* ProfiniteSurfaceGroup g 0) :=
  ⟨fun e ↦ not_hasFiniteLifts hg (hP.of_continuousMulEquiv e)⟩

/-- **No open subgroup of a group isomorphic to a free profinite group `F̂(α)` is isomorphic to
`Π̂_{g,0}` with `g ≥ 1`.** -/
theorem isEmpty_continuousMulEquiv_of_isOpen_freeHat {α : Type*} {P : Type*} [Group P]
    [TopologicalSpace P] (e : P ≃ₜ* FreeHat α) (H : Subgroup P) (hH : IsOpen (H : Set P))
    (hg : 0 < g) : IsEmpty (H ≃ₜ* ProfiniteSurfaceGroup g 0) :=
  isEmpty_continuousMulEquiv_of_hasFiniteLifts
    (HasFiniteLifts.of_isOpen_of_continuousMulEquiv α e H hH : HasFiniteLifts.{0} H) hg

/-- **No open subgroup of a group isomorphic to `Π̂_{g,r}` with `r ≥ 1` is isomorphic to
`Π̂_{g',0}` with `g' ≥ 1`**: an open subgroup of the geometric fundamental group of an affine
hyperbolic curve (in characteristic `0`) is never the geometric fundamental group of a proper curve
of positive genus. -/
theorem isEmpty_continuousMulEquiv_of_isOpen {g' r : ℕ} {P : Type*} [Group P]
    [TopologicalSpace P] (hr : 0 < r) (e : P ≃ₜ* ProfiniteSurfaceGroup g r) (H : Subgroup P)
    (hH : IsOpen (H : Set P)) (hg' : 0 < g') : IsEmpty (H ≃ₜ* ProfiniteSurfaceGroup g' 0) := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  exact isEmpty_continuousMulEquiv_of_isOpen_freeHat (e.trans profiniteFreeEquiv) H hH hg'

end SurfaceGroup

end Pi1
