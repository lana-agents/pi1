/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.Commensurator
public import Pi1.Surface.ReidemeisterSchreier

/-!
# The cuspidal inertia group of `Π̂_{g,1}` is commensurably terminal

For `g ≥ 1` the once-punctured surface group `Π_{g,1}` is free on `a₁, b₁, …, a_g, b_g`, with
cusp `c = (∏ᵢ [aᵢ, bᵢ])⁻¹`, which is *not* a basis element. We prove:

* `Pi1.SurfaceGroup.commensurator_inertia_one`: the cuspidal inertia group `I = ⟨c⟩‾` of
  `Π̂_{g,1}` (`g ≥ 1`) is **commensurably terminal**;
* `Pi1.SurfaceGroup.commensurator_inertia'`: for `(g, r)` hyperbolic with `r ≥ 1`, **every**
  cuspidal inertia group of `Π̂_{g,r}` is commensurably terminal (combining the above with
  `Pi1.SurfaceGroup.commensurator_inertia` for `r ≥ 2`).

This is the group-theoretic content of [AbsTopI] Lemma 4.1 (i)
(`Topics in Absolute Anabelian Geometry I.txt` l.2741–2745) for the once-punctured case.

## The argument

Let `F = F(a₁, b₁, …)`, `w = ∏ᵢ [aᵢ, bᵢ]` and let `F` act on `ℤ/3` through `a₁ ↦ +1`, the
other generators acting trivially; let `N` be the stabiliser of `0` (index `3`).

* **Schreier basis.** With the transversal `1, a₁, a₁²` (`sheetTransversal`), `N` is free on the
  Schreier generators `s(ω, x)` (`Pi1.ReidemeisterSchreier.Transversal.basis`), and the
  Reidemeister rewriting of `w` is `A₂ B₂ A₂⁻¹ B₀⁻¹ R` (`rewrite_cuspWord`), where `A₂ = s(2, a₁)`,
  `B_ω = s(ω, b₁)` and `R = ∏_{i ≥ 2} [s(0, aᵢ), s(0, bᵢ)]`. The Nielsen transformation
  `B₂ ↦ A₂ B₂ A₂⁻¹ B₀⁻¹ R` (`nielsenEquiv`) gives a basis of `N` containing `w`
  (`cuspBasisEquiv`).
* **`N̂ ⊆ F̂` is free profinite.** The closure of a finite-index subgroup is its profinite
  completion (`Pi1.Profinite.completionMap_subtype_injective`), so we get a continuous injective
  homomorphism `ι : F̂(gens) → F̂` with `ι(B₂) = w` (`cuspEmb`), whose image contains every
  element of `F̂` in the kernel of the character `F̂ → ℤ/3` (`mem_range_cuspEmb`).
* **The commensurator lies in `N̂`.** If `σ` commensurates `⟨w⟩‾`, then `σ⁻¹ wⁿ σ ∈ ⟨w⟩‾` for
  some `n ≥ 1`. In the finite quotient `F → Perm(ℤ/3 × ℤ/(n+1))` given by the cocycle counting
  `s(1, b₁)` (`ReidemeisterSchreier.extAction`), `w` acts trivially on the fibre over the sheet
  `0` but by `∓1` on the fibres over `1, 2` (`coc_countLab`), which forces `σ ↦ 0` in `ℤ/3`
  (`chiThree_eq_one_of_mem_commensurator`).
* **Conclusion.** Pulling back along `ι`, `σ` commensurates the inertia group of the basis
  element `B₂` of `F̂(gens)`, which is commensurably terminal
  (`Pi1.Profinite.commensurator_basisInertia`).
-/

@[expose] public section

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology
open scoped Pointwise

universe u

namespace Pi1

/-! ### Completions of finite-index subgroups -/

namespace Profinite

variable {G : Type u} [Group G]

/-- **The completion of a finite-index subgroup embeds**: for `H ≤ G` of finite index, the map
`Ĥ → Ĝ` induced by the inclusion is injective. -/
theorem completionMap_subtype_injective (H : Subgroup G) [H.FiniteIndex] :
    Function.Injective (completionMap H.subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  refine eq_one_of_forall_liftFinite fun P _ _ f ↦ ?_
  haveI : f.ker.FiniteIndex := Subgroup.finiteIndex_ker f
  haveI : (f.ker.map H.subtype).FiniteIndex := ⟨by
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩
  set K := (f.ker.map H.subtype).normalCore
  haveI : K.FiniteIndex := Subgroup.finiteIndex_normalCore _
  set ρ : H →* G ⧸ K := (QuotientGroup.mk' K).comp H.subtype
  have h1 : liftFinite ρ x = 1 := by
    rw [← liftFinite_completionMap, hx, map_one]
  have h2 : liftFinite ρ.rangeRestrict x = 1 := by
    apply Subtype.val_injective
    have := liftFinite_comp ρ.rangeRestrict ρ.range.subtype x
    rw [MonoidHom.subtype_comp_rangeRestrict, h1] at this
    exact this.symm
  have hle : ρ.rangeRestrict.ker ≤ f.ker := by
    intro h hh
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hh
    have hK : (h : G) ∈ K := by
      simpa [ρ, QuotientGroup.eq_one_iff] using hh
    obtain ⟨h', hh', he⟩ := Subgroup.normalCore_le _ hK
    rw [← Subtype.val_injective he]
    exact hh'
  let e := QuotientGroup.quotientKerEquivOfSurjective _ ρ.rangeRestrict_surjective
  let φ : ρ.range →* P := (QuotientGroup.lift _ f hle).comp e.symm.toMonoidHom
  have hφ : φ.comp ρ.rangeRestrict = f := by
    ext h
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [show e.symm (ρ.rangeRestrict h) = QuotientGroup.mk h from
      e.symm_apply_eq.2 rfl]
    rfl
  rw [← hφ, liftFinite_comp, h2, map_one]

/-- Elements of `⟨y⟩‾` map into `⟨f y⟩` in every finite quotient. -/
theorem liftFinite_mem_zpowers_of_mem {P : Type u} [Group P] [Finite P] (f : G →* P) {y : G}
    {z : completion (GrpCat.of G)}
    (hz : z ∈ (Subgroup.zpowers (etaFn (GrpCat.of G) y)).topologicalClosure) :
    liftFinite f z ∈ Subgroup.zpowers (f y) := by
  have hle : (Subgroup.zpowers (etaFn (GrpCat.of G) y)).topologicalClosure ≤
      (Subgroup.zpowers (f y)).comap (liftFinite f) := by
    refine Subgroup.topologicalClosure_minimal _ ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, liftFinite_eta]
      exact Subgroup.mem_zpowers _
    · exact Subgroup.isClosed_of_isOpen _ (by
        rw [Subgroup.coe_comap]
        exact isOpen_liftFinite_preimage f _)
  exact hle hz

end Profinite

/-! ### Nielsen transformations -/

namespace FreeGroupNielsen

open FreeGroup

variable {β : Type*}

/-- The endomorphism `e ↦ P e P⁻¹ Q` of `F(β)`, fixing the other generators. -/
def nielsen [DecidableEq β] (e : β) (P Q : FreeGroup β) : FreeGroup β →* FreeGroup β :=
  FreeGroup.lift fun e' ↦ if e' = e then P * of e * P⁻¹ * Q else of e'

lemma nielsen_of_self [DecidableEq β] (e : β) (P Q : FreeGroup β) :
    nielsen e P Q (of e) = P * of e * P⁻¹ * Q := by
  simp [nielsen]

lemma nielsen_of_ne [DecidableEq β] {e e' : β} (h : e' ≠ e) (P Q : FreeGroup β) :
    nielsen e P Q (of e') = of e' := by
  simp [nielsen, h]

/-- A word *not involving* `e`: fixed by every endomorphism fixing the other generators. -/
def Avoids (e : β) (P : FreeGroup β) : Prop :=
  ∀ φ : FreeGroup β →* FreeGroup β, (∀ e' ≠ e, φ (of e') = of e') → φ P = P

lemma Avoids.of {e e' : β} (h : e' ≠ e) : Avoids e (of e') := fun _ hφ ↦ hφ e' h

lemma Avoids.inv {e : β} {P : FreeGroup β} (h : Avoids e P) : Avoids e P⁻¹ :=
  fun φ hφ ↦ by rw [_root_.map_inv, h φ hφ]

lemma Avoids.mul {e : β} {P Q : FreeGroup β} (hP : Avoids e P) (hQ : Avoids e Q) :
    Avoids e (P * Q) :=
  fun φ hφ ↦ by rw [_root_.map_mul, hP φ hφ, hQ φ hφ]

lemma Avoids.commProd {e : β} {n : ℕ} {x y : Fin n → FreeGroup β} (hx : ∀ i, Avoids e (x i))
    (hy : ∀ i, Avoids e (y i)) : Avoids e (SurfaceGen.commProd x y) :=
  fun φ hφ ↦ by
    rw [SurfaceGen.map_commProd]
    congr 1
    · funext i; exact hx i φ hφ
    · funext i; exact hy i φ hφ

/-- **Nielsen transformation**: for words `P, Q` not involving `e`, `e ↦ P e P⁻¹ Q` (other
generators fixed) is an automorphism of `F(β)`. -/
def nielsenEquiv [DecidableEq β] (e : β) {P Q : FreeGroup β} (hP : Avoids e P) (hQ : Avoids e Q) :
    FreeGroup β ≃* FreeGroup β :=
  MonoidHom.toMulEquiv (nielsen e P Q) (nielsen e P⁻¹ (P⁻¹ * Q⁻¹ * P))
    (FreeGroup.ext_hom _ _ fun e' ↦ by
      have hfix : ∀ e'' ≠ e, (nielsen e P⁻¹ (P⁻¹ * Q⁻¹ * P)) (of e'') = of e'' :=
        fun _ h ↦ nielsen_of_ne h _ _
      by_cases h : e' = e
      · subst h
        simp only [MonoidHom.coe_comp, Function.comp_apply, nielsen_of_self, _root_.map_mul,
          _root_.map_inv,
          hP _ hfix, hQ _ hfix, MonoidHom.id_apply]
        group
      · simp [nielsen_of_ne h])
    (FreeGroup.ext_hom _ _ fun e' ↦ by
      have hfix : ∀ e'' ≠ e, (nielsen e P Q) (of e'') = of e'' :=
        fun _ h ↦ nielsen_of_ne h _ _
      by_cases h : e' = e
      · subst h
        simp only [MonoidHom.coe_comp, Function.comp_apply, nielsen_of_self, _root_.map_mul,
          _root_.map_inv,
          hP _ hfix, hQ _ hfix, MonoidHom.id_apply]
        group
      · simp [nielsen_of_ne h])

lemma nielsenEquiv_of_self [DecidableEq β] (e : β) {P Q : FreeGroup β} (hP : Avoids e P)
    (hQ : Avoids e Q) :
    nielsenEquiv e hP hQ (of e) = P * of e * P⁻¹ * Q :=
  nielsen_of_self e P Q

end FreeGroupNielsen

/-! ### Transport lemmas -/

section Transport

variable {G H : Type*} [Group G] [Group H] (f : G →* H)

/-- Conjugation commutes with `comap` along a homomorphism. -/
lemma conjAct_smul_comap_hom (A : Subgroup H) (σ : G) :
    ConjAct.toConjAct σ • A.comap f = (ConjAct.toConjAct (f σ) • A).comap f := by
  ext x
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_comap, ConjAct.smul_def,
    map_inv, ConjAct.ofConjAct_toConjAct, map_mul]

/-- Commensurability of subgroups of the range is detected after `comap`. -/
lemma commensurable_comap_iff_of_le_range {A B : Subgroup H} (hA : A ≤ f.range)
    (hB : B ≤ f.range) : (A.comap f).Commensurable (B.comap f) ↔ A.Commensurable B := by
  have h : ∀ A B : Subgroup H, B ≤ f.range → (A.comap f).relIndex (B.comap f) = A.relIndex B :=
    fun A B hB ↦ by rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq, inf_of_le_right hB]
  simp only [Subgroup.Commensurable, h _ _ hA, h _ _ hB]

/-- A subgroup lies in its commensurator. -/
lemma le_commensurator (A : Subgroup G) : A ≤ Subgroup.Commensurable.commensurator A := by
  intro σ hσ
  rw [Subgroup.Commensurable.commensurator_mem_iff]
  have : ConjAct.toConjAct σ • A = A := by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    constructor
    · intro hx
      simpa [mul_assoc] using mul_mem (mul_mem hσ hx) (inv_mem hσ)
    · intro hx
      exact mul_mem (mul_mem (inv_mem hσ) hx) hσ
  rw [this]

end Transport

/-! ### Cocycles of the Reidemeister rewriting -/

namespace ReidemeisterSchreier

open FreeGroup

variable {α Ω G : Type*} [MulAction (FreeGroup α) Ω] [Group G]

lemma coc_of_inv (lab : Ω → α → G) (s : α) (ω : Ω) :
    coc lab (of s)⁻¹ ω = (lab ((of s)⁻¹ • ω) s)⁻¹ := by
  have h := coc_inv lab (of s) ((of s)⁻¹ • ω)
  rwa [smul_inv_smul, coc_of] at h

lemma coc_pow {lab : Ω → α → G} {x : FreeGroup α} {ω : Ω} (hx : x • ω = ω) (n : ℕ) :
    coc lab (x ^ n) ω = coc lab x ω ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, coc_mul, hx, ih, pow_succ]

/-- On words fixing `ω`, the cocycle is multiplicative; in particular on products of
commutators. -/
lemma coc_commProd (lab : Ω → α → G) {n : ℕ} (x y : Fin n → FreeGroup α) (ω : Ω)
    (hx : ∀ i, x i • ω = ω) (hy : ∀ i, y i • ω = ω) :
    coc lab (SurfaceGen.commProd x y) ω =
      SurfaceGen.commProd (fun i ↦ coc lab (x i) ω) (fun i ↦ coc lab (y i) ω) := by
  let S := MulAction.stabilizer (FreeGroup α) ω
  let x' : Fin n → S := fun i ↦ ⟨x i, hx i⟩
  let y' : Fin n → S := fun i ↦ ⟨y i, hy i⟩
  have h1 := SurfaceGen.map_commProd S.subtype x' y'
  have h2 := SurfaceGen.map_commProd (cocHom lab ω) x' y'
  simp only [Subgroup.coe_subtype, x', y'] at h1
  rw [← h1]
  exact h2

/-- The Reidemeister rewriting inverts the Schreier generators. -/
lemma Transversal.toStab_rewrite {ω₀ : Ω} (T : Transversal α ω₀)
    (y : MulAction.stabilizer (FreeGroup α) ω₀) : T.toStab (T.rewrite y) = y := by
  obtain ⟨z, rfl⟩ := T.toStab_surjective y
  rw [show T.rewrite (T.toStab z) = z from DFunLike.congr_fun T.rewrite_comp_toStab z]

lemma Transversal.lab_eq {ω₀ : Ω} (T : Transversal α ω₀) {ω : Ω} {s : α} (h : (ω, s) ∉ T.E) :
    T.lab ω s = of ⟨(ω, s), h⟩ :=
  T.lab_of_notMem ⟨(ω, s), h⟩

end ReidemeisterSchreier

/-! ### The index-`3` subgroup `N` -/

namespace SurfaceGroup

open FreeGroup Profinite ReidemeisterSchreier FreeGroupNielsen

variable {g : ℕ}

lemma commProd_eq_one_of_comm {G : Type*} [CommGroup G] {n : ℕ} (x y : Fin n → G) :
    SurfaceGen.commProd x y = 1 := by
  simp [SurfaceGen.commProd]

lemma commProd_succ {G : Type*} [Group G] {n : ℕ} (x y : Fin (n + 1) → G) :
    SurfaceGen.commProd x y = x 0 * y 0 * (x 0)⁻¹ * (y 0)⁻¹ *
      SurfaceGen.commProd (fun i ↦ x i.succ) (fun i ↦ y i.succ) := by
  simp [SurfaceGen.commProd, List.ofFn_succ]

/-- The cusp word `w = ∏ᵢ [aᵢ, bᵢ]` of `F(a₁, b₁, …, a_g, b_g)`; the cusp of `Π_{g,1}` is
`w⁻¹`. -/
def cuspWord (g : ℕ) : FreeGroup (SurfaceGen g 0) :=
  SurfaceGen.commProd (fun i ↦ of (.a i)) (fun i ↦ of (.b i))

lemma lastCuspWord_zero : lastCuspWord g 0 = (cuspWord g)⁻¹ := by
  simp [lastCuspWord, cuspWord, SurfaceGen.ordProd]

/-- The character `χ₃ : F(a₁, b₁, …) → ℤ/3`, `a₁ ↦ 1`, the other generators `↦ 0`. -/
noncomputable def chiThree : FreeGroup (SurfaceGen (g + 1) 0) →* Multiplicative (ZMod 3) :=
  FreeGroup.lift fun s ↦ if s = .a 0 then Multiplicative.ofAdd 1 else 1

/-- `F(a₁, b₁, …)` acts on the three sheets `ℤ/3` through `χ₃`. -/
@[reducible] noncomputable def sheetAction :
    MulAction (FreeGroup (SurfaceGen (g + 1) 0)) (ZMod 3) :=
  MulAction.compHom _ chiThree

attribute [local instance] sheetAction

lemma smul_def (x : FreeGroup (SurfaceGen (g + 1) 0)) (ω : ZMod 3) :
    x • ω = Multiplicative.toAdd (chiThree x) + ω := rfl

lemma of_a0_smul (ω : ZMod 3) : (of (.a 0) : FreeGroup (SurfaceGen (g + 1) 0)) • ω = ω + 1 := by
  rw [smul_def, chiThree, FreeGroup.lift_apply_of, if_pos rfl, toAdd_ofAdd, add_comm]

lemma inv_of_a0_smul (ω : ZMod 3) :
    (of (.a 0) : FreeGroup (SurfaceGen (g + 1) 0))⁻¹ • ω = ω - 1 := by
  rw [inv_smul_eq_iff, of_a0_smul, sub_add_cancel]

lemma of_smul_of_ne {s : SurfaceGen (g + 1) 0} (h : s ≠ .a 0) (ω : ZMod 3) :
    (of s : FreeGroup (SurfaceGen (g + 1) 0)) • ω = ω := by
  rw [smul_def, chiThree, FreeGroup.lift_apply_of, if_neg h, toAdd_one, zero_add]

lemma of_b_smul (i : Fin (g + 1)) (ω : ZMod 3) :
    (of (.b i) : FreeGroup (SurfaceGen (g + 1) 0)) • ω = ω :=
  of_smul_of_ne (by simp) ω

lemma inv_of_b_smul (i : Fin (g + 1)) (ω : ZMod 3) :
    (of (.b i) : FreeGroup (SurfaceGen (g + 1) 0))⁻¹ • ω = ω := by
  rw [inv_smul_eq_iff, of_b_smul]

lemma of_a_succ_smul (i : Fin g) (ω : ZMod 3) :
    (of (.a i.succ) : FreeGroup (SurfaceGen (g + 1) 0)) • ω = ω :=
  of_smul_of_ne (by simp [Fin.succ_ne_zero]) ω

lemma of_a0_pow_smul (n : ℕ) (ω : ZMod 3) :
    (of (.a 0) ^ n : FreeGroup (SurfaceGen (g + 1) 0)) • ω = ω + n := by
  induction n generalizing ω with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, of_a0_smul, ih]
    push_cast
    ring

lemma commProd_smul {n : ℕ} (x y : Fin n → FreeGroup (SurfaceGen (g + 1) 0)) (ω : ZMod 3) :
    SurfaceGen.commProd x y • ω = ω := by
  rw [smul_def, SurfaceGen.map_commProd, commProd_eq_one_of_comm, toAdd_one, zero_add]

lemma cuspWord_pow_smul (n : ℕ) (ω : ZMod 3) : cuspWord (g + 1) ^ n • ω = ω := by
  rw [smul_def, map_pow, cuspWord, SurfaceGen.map_commProd, commProd_eq_one_of_comm, one_pow,
    toAdd_one, zero_add]

/-- **The rewriting of the cusp word** for an arbitrary labelling: starting from the sheet `ω`,
`w` reads `x(ω-1, a₁) x(ω-1, b₁) x(ω-1, a₁)⁻¹ x(ω, b₁)⁻¹ ∏_{i ≥ 2} [x(ω, aᵢ), x(ω, bᵢ)]`. -/
theorem coc_cuspWord {G : Type*} [Group G] (lab : ZMod 3 → SurfaceGen (g + 1) 0 → G)
    (ω : ZMod 3) :
    coc lab (cuspWord (g + 1)) ω =
      lab (ω - 1) (.a 0) * lab (ω - 1) (.b 0) * (lab (ω - 1) (.a 0))⁻¹ * (lab ω (.b 0))⁻¹ *
        SurfaceGen.commProd (fun i ↦ lab ω (.a i.succ)) (fun i ↦ lab ω (.b i.succ)) := by
  rw [cuspWord, commProd_succ, coc_mul, commProd_smul,
    coc_commProd _ _ _ _ (fun i ↦ of_a_succ_smul i ω) (fun i ↦ of_b_smul _ ω)]
  simp only [coc_mul, coc_of, coc_of_inv, inv_of_b_smul, inv_of_a0_smul, of_b_smul]

/-- The Schreier transversal `1, a₁, a₁²` of the stabiliser of the sheet `0`, with tree edges
`(0, a₁)` and `(1, a₁)`. -/
noncomputable def sheetTransversal : Transversal (SurfaceGen (g + 1) 0) (0 : ZMod 3) where
  t ω := of (.a 0) ^ ω.val
  E := {(0, .a 0), (1, .a 0)}
  t_smul ω := by rw [of_a0_pow_smul, zero_add, ZMod.natCast_zmod_val]
  t_base := by simp
  schreierGen_eq_one e he := by
    obtain rfl | rfl := he
    · simp only [schreierGen, of_a0_smul]
      rw [show ((0 : ZMod 3) + 1).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl]
      group
    · simp only [schreierGen, of_a0_smul]
      rw [show ((1 : ZMod 3) + 1).val = 2 from rfl, show (1 : ZMod 3).val = 1 from rfl]
      group
  depth ω := ω.val
  exists_edge ω hω := by
    fin_cases ω
    · exact absurd rfl hω
    · exact ⟨(0, .a 0), Or.inl rfl, Or.inr ⟨by rw [of_a0_smul]; rfl,
      (by decide : (0 : ZMod 3).val < (1 : ZMod 3).val)⟩⟩
    · exact ⟨(1, .a 0), Or.inr rfl, Or.inr ⟨by rw [of_a0_smul]; rfl,
      (by decide : (1 : ZMod 3).val < (2 : ZMod 3).val)⟩⟩

/-- The free generators of `N` (the non-tree edges of `sheetTransversal`). -/
abbrev Gens (g : ℕ) := (sheetTransversal (g := g)).Gens

/-- The Schreier generator `A₂ = s(2, a₁) = a₁³`. -/
noncomputable def sheetA2 : Gens g := ⟨(2, .a 0), by simp [sheetTransversal]; decide⟩

/-- The Schreier generator `B_ω = s(ω, b₁)`. -/
noncomputable def sheetB (ω : ZMod 3) : Gens g := ⟨(ω, .b 0), by simp [sheetTransversal]⟩

/-- The Schreier generator `s(0, aᵢ) = aᵢ` (`i ≥ 2`). -/
noncomputable def sheetA0 (i : Fin g) : Gens g :=
  ⟨(0, .a i.succ), by simp [sheetTransversal, Fin.succ_ne_zero]⟩

/-- The Schreier generator `s(0, bᵢ) = bᵢ` (`i ≥ 2`). -/
noncomputable def sheetB0 (i : Fin g) : Gens g := ⟨(0, .b i.succ), by simp [sheetTransversal]⟩

/-- The word `R = ∏_{i ≥ 2} [s(0, aᵢ), s(0, bᵢ)]`. -/
noncomputable def restWord (g : ℕ) : FreeGroup (Gens g) :=
  SurfaceGen.commProd (fun i ↦ of (sheetA0 i)) (fun i ↦ of (sheetB0 i))

/-- The stabiliser `N` of the sheet `0`, of index `3`. -/
noncomputable abbrev sheetStab (g : ℕ) : Subgroup (FreeGroup (SurfaceGen (g + 1) 0)) :=
  MulAction.stabilizer (FreeGroup (SurfaceGen (g + 1) 0)) (0 : ZMod 3)

instance : (sheetStab g).FiniteIndex := by
  haveI : Finite (FreeGroup (SurfaceGen (g + 1) 0) ⧸ sheetStab g) :=
    Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer _ _)
  exact Subgroup.finiteIndex_of_finite_quotient

lemma cuspWord_mem : cuspWord (g + 1) ∈ sheetStab g := by
  simpa using cuspWord_pow_smul (g := g) 1 0

/-- **The rewriting of the cusp word**: `w ↦ A₂ B₂ A₂⁻¹ B₀⁻¹ R`. -/
theorem rewrite_cuspWord :
    (sheetTransversal (g := g)).rewrite ⟨cuspWord (g + 1), cuspWord_mem⟩ =
      of sheetA2 * of (sheetB 2) * (of sheetA2)⁻¹ * ((of (sheetB 0))⁻¹ * restWord g) := by
  set T := sheetTransversal (g := g)
  have e1 : T.lab 2 (.a 0) = of sheetA2 := T.lab_of_notMem sheetA2
  have e2 : ∀ ω, T.lab ω (.b 0) = of (sheetB ω) := fun ω ↦ T.lab_of_notMem (sheetB ω)
  have e4 : ∀ i, T.lab 0 (.a i.succ) = of (sheetA0 i) := fun i ↦ T.lab_of_notMem (sheetA0 i)
  have e5 : ∀ i, T.lab 0 (.b i.succ) = of (sheetB0 i) := fun i ↦ T.lab_of_notMem (sheetB0 i)
  change coc T.lab (cuspWord (g + 1)) 0 = _
  rw [coc_cuspWord, show (0 : ZMod 3) - 1 = 2 from rfl]
  simp only [e1, e2, e4, e5, restWord, mul_assoc]

lemma sheetA2_ne : (sheetA2 : Gens g) ≠ sheetB 2 := by
  simp [sheetA2, sheetB]

lemma avoids_restWord : Avoids (sheetB 2) (restWord g) :=
  Avoids.commProd (fun i ↦ Avoids.of (by simp [sheetA0, sheetB]))
    (fun i ↦ Avoids.of (by simp [sheetB0, sheetB]))

lemma avoids_Q : Avoids (sheetB 2) ((of (sheetB 0))⁻¹ * restWord g) :=
  (Avoids.of (by simp [sheetB]; decide)).inv.mul avoids_restWord

/-- **A free basis of `N` containing the cusp word**: `F(gens) ≃* N`, `B₂ ↦ w`. -/
noncomputable def cuspBasisEquiv : FreeGroup (Gens g) ≃* sheetStab g :=
  (nielsenEquiv (sheetB 2) (Avoids.of sheetA2_ne) avoids_Q).trans
    (MulEquiv.ofBijective (sheetTransversal (g := g)).toStab
      ⟨(sheetTransversal (g := g)).toStab_injective,
        (sheetTransversal (g := g)).toStab_surjective⟩)

lemma cuspBasisEquiv_sheetB_two :
    cuspBasisEquiv (g := g) (of (sheetB 2)) = ⟨cuspWord (g + 1), cuspWord_mem⟩ := by
  simp only [cuspBasisEquiv, MulEquiv.trans_apply, nielsenEquiv_of_self,
    MulEquiv.ofBijective_apply]
  rw [← rewrite_cuspWord, Transversal.toStab_rewrite]

/-! ### `N̂` inside `F̂` -/

/-- The embedding `ι : F̂(gens) → F̂`, an isomorphism onto the closure `N̂` of `N`. -/
noncomputable def cuspEmb :
    completion (GrpCat.of (FreeGroup (Gens g))) →*
      completion (GrpCat.of (FreeGroup (SurfaceGen (g + 1) 0))) :=
  (completionMap (sheetStab g).subtype).comp (completionMap (cuspBasisEquiv (g := g)).toMonoidHom)

lemma continuous_cuspEmb : Continuous (cuspEmb (g := g)) :=
  (continuous_completionMap (sheetStab g).subtype).comp
    (continuous_completionMap (cuspBasisEquiv (g := g)).toMonoidHom)

lemma cuspEmb_injective : Function.Injective (cuspEmb (g := g)) :=
  (completionMap_subtype_injective _).comp (completionCongr (cuspBasisEquiv (g := g))).injective

lemma cuspEmb_gen_sheetB_two :
    cuspEmb (g := g) (gen (sheetB 2)) =
      etaFn (GrpCat.of (FreeGroup (SurfaceGen (g + 1) 0))) (cuspWord (g + 1)) := by
  simp [cuspEmb, completionMap_eta, cuspBasisEquiv_sheetB_two]

/-- Every element of `F̂` in the kernel of `χ₃` lies in `N̂ = ι(F̂(gens))`. -/
theorem mem_range_cuspEmb {z : FreeHat (SurfaceGen (g + 1) 0)} (hz : liftFinite chiThree z = 1) :
    z ∈ (cuspEmb (g := g)).range := by
  have hcl : IsClosed (Set.range (cuspEmb (g := g))) :=
    (isCompact_range continuous_cuspEmb).isClosed
  rw [MonoidHom.mem_range, ← Set.mem_range, ← hcl.closure_eq, mem_closure_iff_nhds]
  intro U hU
  obtain ⟨V, hVU, hVo, hzV⟩ := mem_nhds_iff.1 hU
  obtain ⟨x, hxV, hx⟩ := exists_etaFn_eq chiThree hVo hzV
  have hxN : x ∈ sheetStab g := by
    rw [MulAction.mem_stabilizer_iff, smul_def, hx, hz, toAdd_one, zero_add]
  refine ⟨_, hVU hxV, etaFn _ ((cuspBasisEquiv (g := g)).symm ⟨x, hxN⟩), ?_⟩
  simp [cuspEmb, completionMap_eta]

/-- The closed subgroup `⟨w⟩‾ ⊆ F̂` (the cuspidal inertia group, `w = c⁻¹`). -/
noncomputable def cuspInertiaF (g : ℕ) : Subgroup (FreeHat (SurfaceGen (g + 1) 0)) :=
  (Subgroup.zpowers
    (etaFn (GrpCat.of (FreeGroup (SurfaceGen (g + 1) 0))) (cuspWord (g + 1)))).topologicalClosure

lemma le_map_cuspEmb : cuspInertiaF g ≤ (basisInertia (sheetB 2)).map (cuspEmb (g := g)) := by
  refine Subgroup.topologicalClosure_minimal _ ?_ ?_
  · rw [Subgroup.zpowers_le, ← cuspEmb_gen_sheetB_two]
    exact Subgroup.mem_map_of_mem _ (gen_mem_basisInertia _)
  · rw [Subgroup.coe_map]
    exact ((Subgroup.isClosed_topologicalClosure _).isCompact.image continuous_cuspEmb).isClosed

lemma comap_cuspEmb : (cuspInertiaF g).comap (cuspEmb (g := g)) = basisInertia (sheetB 2) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := le_map_cuspEmb hx
    rwa [← cuspEmb_injective hyx]
  · refine Subgroup.topologicalClosure_minimal _ ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, cuspEmb_gen_sheetB_two]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)
    · exact (Subgroup.isClosed_topologicalClosure _).preimage continuous_cuspEmb

/-! ### The commensurator lies in `N̂` -/

/-- The labelling counting the Schreier generator `s(1, b₁)`, with values in `ℤ/M`. -/
noncomputable def countLab (M : ℕ) : ZMod 3 → SurfaceGen (g + 1) 0 → Multiplicative (ZMod M) :=
  fun ω s ↦ if ω = 1 ∧ s = .b 0 then Multiplicative.ofAdd 1 else 1

lemma countLab_one (M : ℕ) : countLab (g := g) M 1 (.b 0) = Multiplicative.ofAdd 1 := by
  simp [countLab]

lemma countLab_ne (M : ℕ) {ω : ZMod 3} (h : ω ≠ 1) : countLab (g := g) M ω (.b 0) = 1 := by
  simp [countLab, h]

lemma coc_countLab (M : ℕ) (ω : ZMod 3) :
    coc (countLab (g := g) M) (cuspWord (g + 1)) ω =
      countLab (g := g) M (ω - 1) (.b 0) * (countLab (g := g) M ω (.b 0))⁻¹ := by
  rw [coc_cuspWord, commProd_eq_one_of_comm]
  have : ∀ ω, countLab (g := g) M ω (.a 0) = 1 := fun ω ↦ by simp [countLab]
  simp only [this, one_mul, inv_one, mul_one]

lemma pow_ofAdd_one_ne_one {n : ℕ} (hn : 0 < n) :
    Multiplicative.ofAdd (1 : ZMod (n + 1)) ^ n ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [orderOf_ofAdd_one] at this
  have := Nat.le_of_dvd hn this
  omega

/-- **The commensurator of `⟨w⟩‾` lies in `N̂`.** -/
theorem chiThree_eq_one_of_mem_commensurator {σ : FreeHat (SurfaceGen (g + 1) 0)}
    (hσ : σ ∈ Subgroup.Commensurable.commensurator (cuspInertiaF g)) :
    liftFinite chiThree σ = 1 := by
  rw [Subgroup.Commensurable.commensurator_mem_iff] at hσ
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hσ.1
    (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _) :
      etaFn (GrpCat.of (FreeGroup (SurfaceGen (g + 1) 0))) (cuspWord (g + 1)) ∈ cuspInertiaF g)
  have h1 : σ⁻¹ * etaFn (GrpCat.of (FreeGroup (SurfaceGen (g + 1) 0))) (cuspWord (g + 1)) ^ n * σ ∈
      cuspInertiaF g := by
    have := (Subgroup.mem_inf.1 hmem).1
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv] at this
    exact this
  set φ := extAction (countLab (g := g) (n + 1))
  obtain ⟨x, -, hφx, hχx⟩ := exists_etaFn_eq₂ φ chiThree isOpen_univ (Set.mem_univ σ)
  have h2 := liftFinite_mem_zpowers_of_mem φ h1
  rw [_root_.map_mul, _root_.map_mul, _root_.map_inv, map_pow, liftFinite_eta, ← hφx] at h2
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h2
  rw [← map_zpow, ← map_pow, ← _root_.map_inv, ← _root_.map_mul, ← _root_.map_mul] at hj
  have h3 := congrArg (fun p ↦ (p ((0 : ZMod 3), (1 : Multiplicative (ZMod (n + 1))))).2) hj
  simp only [φ, extAction_apply, mul_one] at h3
  rw [coc_zpow_eq_one (by simpa using cuspWord_pow_smul (g := g) 1 0)
    (by rw [coc_countLab, show (0 : ZMod 3) - 1 = 2 from rfl,
      countLab_ne _ (show (2 : ZMod 3) ≠ 1 by decide),
      countLab_ne _ (show (0 : ZMod 3) ≠ 1 by decide), inv_one, mul_one]), coc_mul, coc_mul,
    cuspWord_pow_smul,
    coc_inv, coc_pow (by simpa using cuspWord_pow_smul (g := g) 1 _), mul_comm _ (coc _ x 0),
    ← mul_assoc, mul_inv_cancel, one_mul, coc_countLab] at h3
  rw [smul_def, add_zero] at h3
  have key : Multiplicative.toAdd (chiThree x) = 0 := by
    generalize Multiplicative.toAdd (chiThree x) = k at h3
    have hk : ∀ k : ZMod 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    rcases hk k with rfl | rfl | rfl
    · rfl
    · rw [show (1 : ZMod 3) - 1 = 0 from rfl, countLab_ne _ (show (0 : ZMod 3) ≠ 1 by decide),
        countLab_one, one_mul,
        inv_pow] at h3
      exact absurd (inv_eq_one.1 h3.symm) (pow_ofAdd_one_ne_one hn)
    · rw [show (2 : ZMod 3) - 1 = 1 from rfl, countLab_ne _ (show (2 : ZMod 3) ≠ 1 by decide),
        countLab_one, inv_one,
        mul_one] at h3
      exact absurd h3.symm (pow_ofAdd_one_ne_one hn)
  rw [← hχx, ← ofAdd_toAdd (chiThree x), key, ofAdd_zero]

/-- **`⟨w⟩‾ ⊆ F̂(a₁, b₁, …, a_g, b_g)` is commensurably terminal** (`g ≥ 1`). -/
theorem commensurator_cuspInertiaF :
    Subgroup.Commensurable.commensurator (cuspInertiaF g) = cuspInertiaF g := by
  refine le_antisymm (fun σ hσ ↦ ?_) (le_commensurator _)
  obtain ⟨δ, rfl⟩ := mem_range_cuspEmb (chiThree_eq_one_of_mem_commensurator hσ)
  have hK : cuspInertiaF g ≤ (cuspEmb (g := g)).range := fun x hx ↦ by
    obtain ⟨y, -, rfl⟩ := le_map_cuspEmb hx
    exact ⟨y, rfl⟩
  have hK' : ConjAct.toConjAct (cuspEmb δ) • cuspInertiaF g ≤ (cuspEmb (g := g)).range :=
    fun x hx ↦ by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
        ConjAct.ofConjAct_toConjAct, inv_inv] at hx
      obtain ⟨y, hy⟩ := hK hx
      exact ⟨δ * y * δ⁻¹, by rw [_root_.map_mul, _root_.map_mul, _root_.map_inv, hy]; group⟩
  have hδ : δ ∈ basisInertia (sheetB 2) := by
    rw [← commensurator_basisInertia, Subgroup.Commensurable.commensurator_mem_iff,
      ← comap_cuspEmb, conjAct_smul_comap_hom, commensurable_comap_iff_of_le_range _ hK' hK]
    exact (Subgroup.Commensurable.commensurator_mem_iff _ _).1 hσ
  rw [← comap_cuspEmb] at hδ
  exact hδ

/-! ### The cusp of `Π̂_{g,1}` -/

/-- The cuspidal inertia group of `Π̂_{g+1,1}` is the preimage of `⟨w⟩‾ ⊆ F̂`. -/
theorem inertia_one_eq_comap :
    inertia (g := g + 1) (r := 1) 0 =
      (cuspInertiaF g).comap (profiniteFreeEquiv (g := g + 1) (r := 0)).toMulEquiv.toMonoidHom := by
  rw [inertia, ← comap_topologicalClosure_zpowers profiniteFreeEquiv]
  congr 1
  rw [cuspInertiaF, ← Subgroup.zpowers_inv]
  congr 2
  simp only [profiniteFreeEquiv, completionCongr_apply, completionMap_eta,
    MulEquiv.coe_toMonoidHom]
  rw [show (0 : Fin 1) = Fin.last 0 from rfl, freeEquiv_cusp_last, lastCuspWord_zero]
  change ((eta (GrpCat.of (FreeGroup (SurfaceGen (g + 1) 0)))).hom (cuspWord (g + 1))⁻¹)⁻¹ =
    (eta (GrpCat.of (FreeGroup (SurfaceGen (g + 1) 0)))).hom (cuspWord (g + 1))
  rw [_root_.map_inv, inv_inv]

/-- **The cuspidal inertia group of `Π̂_{g,1}` (`g ≥ 1`) is commensurably terminal.** -/
theorem commensurator_inertia_one {g : ℕ} (hg : 0 < g) :
    Subgroup.Commensurable.commensurator (inertia (g := g) (r := 1) 0) = inertia 0 := by
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  rw [inertia_one_eq_comap, commensurator_comap, commensurator_cuspInertiaF]

/-- **Every cuspidal inertia group of `Π̂_{g,r}` is commensurably terminal**, for `(g, r)`
hyperbolic with `r ≥ 1`. -/
theorem commensurator_inertia' {g r : ℕ} (hr : 0 < r) (h : IsHyperbolic g r) (k : Fin r) :
    Subgroup.Commensurable.commensurator (inertia (g := g) k) = inertia k := by
  rcases r with _ | _ | r
  · omega
  · obtain rfl : k = 0 := Fin.fin_one_eq_zero k
    exact commensurator_inertia_one (by unfold IsHyperbolic at h; omega)
  · exact commensurator_inertia k

end SurfaceGroup

end Pi1
