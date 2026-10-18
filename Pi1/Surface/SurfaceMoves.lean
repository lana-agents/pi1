/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.Basic
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.Group

/-!
# Moves on surface groups

Three isomorphisms used to build geometric bases of `π₁` of ribbon graphs
(`Pi1.Surface.RibbonGraph`), all elementary Tietze/Nielsen moves on the presentation
`Π_{g,r} = ⟨a, b, c | ∏ [aᵢ, bᵢ] ∏ cⱼ⟩`:

* `SurfaceGroup.exists_cusp_last`: any cusp can be moved to the last position, the other cusps
  being permuted up to conjugacy (Hurwitz moves `cⱼ, cⱼ₊₁ ↦ cⱼ cⱼ₊₁ cⱼ⁻¹, cⱼ`);
* `SurfaceGroup.splitCusp`: if `Π_{g,r+1} ≃* F(L)` with last cusp `p q`, then
  `Π_{g,r+2} ≃* F(L ⊔ {e})` with the last two cusps `p e r`, `r⁻¹ e⁻¹ q` (a new free generator
  splits a cusp into two);
* `SurfaceGroup.addHandle`: if `Π_{g,r+2} ≃* F(L)` with last two cusps `C₁, C₂`, then
  `Π_{g+1,r+1} ≃* F(L ⊔ {e})` with last cusp conjugate to `C₁ E C₂ E⁻¹`, `E = s e t` (a new free
  generator joins two cusps into a handle).
-/

@[expose] public section

namespace Pi1

open SurfaceGen FreeGroup

namespace SurfaceGen

variable {G : Type*} [Group G]

lemma ordProd_cons {r : ℕ} (z : Fin (r + 1) → G) :
    ordProd z = z 0 * ordProd (fun i : Fin r ↦ z i.succ) := by
  rw [ordProd, ordProd, List.ofFn_succ, List.prod_cons]

lemma commProd_succ {g : ℕ} (x y : Fin (g + 1) → G) :
    commProd x y = commProd (fun i : Fin g ↦ x i.castSucc) (fun i ↦ y i.castSucc) *
      (x (Fin.last g) * y (Fin.last g) * (x (Fin.last g))⁻¹ * (y (Fin.last g))⁻¹) := by
  rw [commProd, commProd, List.ofFn_succ', List.prod_concat]

/-- Changing two adjacent entries without changing their product does not change `ordProd`. -/
lemma ordProd_adjacent {r : ℕ} (j : Fin r) (z c : Fin (r + 1) → G)
    (h : ∀ k, k ≠ j.castSucc → k ≠ j.succ → z k = c k)
    (hj : z j.castSucc * z j.succ = c j.castSucc * c j.succ) : ordProd z = ordProd c := by
  induction r with
  | zero => exact j.elim0
  | succ r ih =>
    rw [ordProd_cons z, ordProd_cons c]
    induction j using Fin.cases with
    | zero =>
      rw [ordProd_cons (fun i : Fin (r + 1) ↦ z i.succ), ordProd_cons (fun i ↦ c i.succ),
        ← mul_assoc, ← mul_assoc]
      simp only [Fin.castSucc_zero] at hj
      rw [hj]
      congr 2
      funext i
      exact h _ (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    | succ j =>
      rw [h 0 (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
      congr 1
      exact ih j _ _ (fun k hk hk' ↦ h _ (fun e ↦ hk (by simpa using e))
        (fun e ↦ hk' (by simpa using e))) (by simpa using hj)

lemma map_commProd' {H F : Type*} [Group H] [FunLike F G H] [MonoidHomClass F G H] (φ : F)
    {g : ℕ} (x y : Fin g → G) :
    φ (commProd x y) = commProd (fun i ↦ φ (x i)) (fun i ↦ φ (y i)) := by
  simp [commProd, map_list_prod, List.map_ofFn, Function.comp_def]

lemma map_ordProd' {H F : Type*} [Group H] [FunLike F G H] [MonoidHomClass F G H] (φ : F)
    {r : ℕ} (z : Fin r → G) : φ (ordProd z) = ordProd (fun j ↦ φ (z j)) := by
  simp [ordProd, map_list_prod, List.map_ofFn, Function.comp_def]

end SurfaceGen

namespace SurfaceGroup

variable {g r : ℕ}

/-! ### Hurwitz moves -/

/-- The cusps after the Hurwitz move at `j`: `cⱼ ↦ cⱼ cⱼ₊₁ cⱼ⁻¹`, `cⱼ₊₁ ↦ cⱼ`. -/
def hurwitzTuple {G : Type*} [Group G] (c : Fin (r + 1) → G) (j : Fin r) (k : Fin (r + 1)) : G :=
  if k = j.castSucc then c j.castSucc * c j.succ * (c j.castSucc)⁻¹
  else if k = j.succ then c j.castSucc else c k

/-- The cusps after the inverse Hurwitz move at `j`. -/
def hurwitzTuple' {G : Type*} [Group G] (c : Fin (r + 1) → G) (j : Fin r) (k : Fin (r + 1)) :
    G :=
  if k = j.castSucc then c j.succ
  else if k = j.succ then (c j.succ)⁻¹ * c j.castSucc * c j.succ else c k

lemma castSucc_ne_succ (j : Fin r) : j.castSucc ≠ j.succ :=
  (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne

/-- The Hurwitz move at `j` as an endomorphism. -/
def hurwitz (j : Fin r) : SurfaceGroup g (r + 1) →* SurfaceGroup g (r + 1) :=
  lift genA genB (hurwitzTuple cusp j) (by
    rw [ordProd_adjacent j _ cusp (fun k hk hk' ↦ by simp [hurwitzTuple, hk, hk'])
      (by simp [hurwitzTuple, (castSucc_ne_succ j).symm])]
    exact relation)

/-- The inverse Hurwitz move at `j`. -/
def hurwitzInv (j : Fin r) : SurfaceGroup g (r + 1) →* SurfaceGroup g (r + 1) :=
  lift genA genB (hurwitzTuple' cusp j) (by
    rw [ordProd_adjacent j _ cusp (fun k hk hk' ↦ by simp [hurwitzTuple', hk, hk'])
      (by simp [hurwitzTuple', (castSucc_ne_succ j).symm]; group)]
    exact relation)

/-- The Hurwitz move as an automorphism. -/
def hurwitzEquiv (j : Fin r) : SurfaceGroup g (r + 1) ≃* SurfaceGroup g (r + 1) :=
  MonoidHom.toMulEquiv (hurwitz j) (hurwitzInv j)
    (hom_ext (fun i ↦ by simp [hurwitz, hurwitzInv]) (fun i ↦ by simp [hurwitz, hurwitzInv])
      fun k ↦ by
        by_cases h1 : k = j.castSucc
        · subst h1
          simp [hurwitz, hurwitzInv, hurwitzTuple, hurwitzTuple', (castSucc_ne_succ j).symm]
          group
        by_cases h2 : k = j.succ
        · subst h2
          simp [hurwitz, hurwitzInv, hurwitzTuple, hurwitzTuple', (castSucc_ne_succ j).symm]
        · simp [hurwitz, hurwitzInv, hurwitzTuple, hurwitzTuple', h1, h2])
    (hom_ext (fun i ↦ by simp [hurwitz, hurwitzInv]) (fun i ↦ by simp [hurwitz, hurwitzInv])
      fun k ↦ by
        by_cases h1 : k = j.castSucc
        · subst h1
          simp [hurwitz, hurwitzInv, hurwitzTuple, hurwitzTuple', (castSucc_ne_succ j).symm]
        by_cases h2 : k = j.succ
        · subst h2
          simp [hurwitz, hurwitzInv, hurwitzTuple, hurwitzTuple', (castSucc_ne_succ j).symm]
          group
        · simp [hurwitz, hurwitzInv, hurwitzTuple, hurwitzTuple', h1, h2])

lemma isConj_hurwitzEquiv_cusp (j : Fin r) (k : Fin (r + 1)) :
    IsConj (hurwitzEquiv (g := g) j (cusp k)) (cusp (Equiv.swap j.castSucc j.succ k)) := by
  change IsConj (hurwitz j (cusp k)) _
  rw [hurwitz, lift_cusp, hurwitzTuple]
  by_cases h1 : k = j.castSucc
  · subst h1
    rw [if_pos rfl, Equiv.swap_apply_left]
    exact isConj_iff.2 ⟨(cusp j.castSucc)⁻¹, by group⟩
  by_cases h2 : k = j.succ
  · subst h2
    rw [if_neg (castSucc_ne_succ j).symm, if_pos rfl, Equiv.swap_apply_right]
  · rw [if_neg h1, if_neg h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma isConj_map {G H F : Type*} [Group G] [Group H] [FunLike F G H] [MonoidHomClass F G H]
    (f : F) {x y : G} (h : IsConj x y) : IsConj (f x) (f y) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨f c, by simp⟩

/-- **Moving a cusp to the end**: for any `j₀` there is a re-indexing `π` of the cusps with
`π (last) = j₀`, fixing the cusps before `j₀` and shifting those after it down by one, and an
isomorphism sending each cusp `cₖ` to a conjugate of `c_{π k}`. -/
theorem exists_cusp_last {G : Type*} [Group G] (ψ : SurfaceGroup g (r + 1) ≃* G)
    (j₀ : Fin (r + 1)) :
    ∃ (ψ' : SurfaceGroup g (r + 1) ≃* G) (π : Equiv.Perm (Fin (r + 1))),
      π (Fin.last r) = j₀ ∧ (∀ k, k < j₀ → π k = k) ∧
      (∀ k : Fin r, j₀ ≤ k.castSucc → π k.castSucc = k.succ) ∧
      ∀ k, IsConj (ψ' (cusp k)) (ψ (cusp (π k))) := by
  induction hd : r - (j₀ : ℕ) generalizing j₀ ψ with
  | zero =>
    have : j₀ = Fin.last r := Fin.ext (by have := j₀.2; simp; omega)
    subst this
    refine ⟨ψ, 1, by simp, fun k _ ↦ rfl, fun k hk ↦ ?_, fun k ↦ IsConj.refl _⟩
    exact absurd hk (not_le.2 (Fin.castSucc_lt_last k))
  | succ d ih =>
    have hj : (j₀ : ℕ) < r := by omega
    set j : Fin r := ⟨j₀, hj⟩
    have hj₀ : j.castSucc = j₀ := Fin.ext rfl
    obtain ⟨ψ', π, hπ, hlt, hge, hconj⟩ :=
      ih ((hurwitzEquiv j).trans ψ) j.succ (by simp [j]; omega)
    refine ⟨ψ', π.trans (Equiv.swap j.castSucc j.succ), ?_, fun k hk ↦ ?_, fun k hk ↦ ?_,
      fun k ↦ (hconj k).trans ?_⟩
    · simp [hπ, hj₀]
    · rw [← hj₀] at hk
      have hk' : k < j.succ := lt_trans hk (Fin.castSucc_lt_succ)
      simp only [Equiv.trans_apply, hlt k hk']
      exact Equiv.swap_apply_of_ne_of_ne hk.ne (by
        intro h; rw [h] at hk; exact absurd hk (not_lt.2 (Fin.castSucc_lt_succ).le))
    · rw [← hj₀] at hk
      simp only [Equiv.trans_apply]
      by_cases hkj : k = j
      · subst hkj
        rw [hlt _ Fin.castSucc_lt_succ, Equiv.swap_apply_left]
      · have hk' : j.succ ≤ k.castSucc := by
          rw [Fin.le_def] at hk ⊢
          have : (k : ℕ) ≠ j := fun h ↦ hkj (Fin.ext h)
          simp only [Fin.val_succ, Fin.val_castSucc] at hk ⊢
          omega
        rw [hge k hk']
        refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
        · intro h
          have h1 := congrArg Fin.val h
          have h2 := Fin.le_def.1 hk'
          simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
          omega
        · intro h; exact hkj (Fin.succ_injective _ h)
    · simp only [MulEquiv.trans_apply, Equiv.trans_apply]
      exact isConj_map ψ (isConj_hurwitzEquiv_cusp j (π k))

/-- Moving two distinct cusps `j₁`, `j₂` to the last two positions. -/
theorem exists_cusp_last₂ {G : Type*} [Group G] (ψ : SurfaceGroup g (r + 2) ≃* G)
    {j₁ j₂ : Fin (r + 2)} (h : j₁ ≠ j₂) :
    ∃ (ψ' : SurfaceGroup g (r + 2) ≃* G) (π : Equiv.Perm (Fin (r + 2))),
      π (Fin.last (r + 1)) = j₂ ∧ π (Fin.last r).castSucc = j₁ ∧
      ∀ k, IsConj (ψ' (cusp k)) (ψ (cusp (π k))) := by
  obtain ⟨ψ₁, π₁, h₁, -, -, hc₁⟩ := exists_cusp_last ψ j₁
  obtain ⟨ψ₂, π₂, h₂, -, hge₂, hc₂⟩ := exists_cusp_last ψ₁ (π₁.symm j₂)
  refine ⟨ψ₂, π₂.trans π₁, by simp [h₂], ?_, fun k ↦ (hc₂ k).trans (hc₁ _)⟩
  have hne : π₁.symm j₂ ≠ Fin.last (r + 1) := by
    intro he
    rw [Equiv.symm_apply_eq] at he
    exact h (h₁.symm.trans he.symm)
  have hle : π₁.symm j₂ ≤ (Fin.last r).castSucc := by
    rw [Fin.le_def]
    have := Fin.val_lt_last hne
    simp only [Fin.val_last, Fin.val_castSucc] at this ⊢
    omega
  simp only [Equiv.trans_apply, hge₂ _ hle, Fin.succ_last, h₁]

/-! ### Splitting a cusp by a new free generator -/

/-- `μ : Π_{g,r+1} → Π_{g,r+2}`, `c_r ↦ c_r c_{r+1}`. -/
def mergeHom : SurfaceGroup g (r + 1) →* SurfaceGroup g (r + 2) :=
  lift genA genB (Fin.lastCases (cusp (Fin.last r).castSucc * cusp (Fin.last (r + 1)))
    fun k ↦ cusp k.castSucc.castSucc) (by
      have h := relation (g := g) (r := r + 2)
      rw [ordProd_succ, ordProd_succ] at h
      rw [ordProd_succ]
      simpa [mul_assoc] using h)

section split

variable {L : Type*}

/-- The forward map of `splitCusp`. -/
def splitFwd (ψ : SurfaceGroup g (r + 1) ≃* FreeGroup L) (p q t : FreeGroup L)
    (hpq : ψ (cusp (Fin.last r)) = p * q) : SurfaceGroup g (r + 2) →* FreeGroup (Option L) :=
  lift (fun i ↦ FreeGroup.map some (ψ (genA i))) (fun i ↦ FreeGroup.map some (ψ (genB i)))
    (Fin.lastCases ((FreeGroup.map some t)⁻¹ * (of none)⁻¹ * FreeGroup.map some q)
      (Fin.lastCases (FreeGroup.map some p * of none * FreeGroup.map some t)
        fun k ↦ FreeGroup.map some (ψ (cusp k.castSucc)))) (by
      rw [ordProd_succ, ordProd_succ]
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      have h := congrArg (fun x ↦ FreeGroup.map some (ψ x)) (relation (g := g) (r := r + 1))
      simp only [ordProd_succ, _root_.map_mul, _root_.map_one, map_commProd', map_ordProd',
        hpq] at h
      rw [← h]
      group)

/-- The backward map of `splitCusp`. -/
def splitBwd (ψ : SurfaceGroup g (r + 1) ≃* FreeGroup L) (p t : FreeGroup L) :
    FreeGroup (Option L) →* SurfaceGroup g (r + 2) :=
  FreeGroup.lift fun o ↦ match o with
    | some l => mergeHom (ψ.symm (of l))
    | none => (mergeHom (ψ.symm p))⁻¹ * cusp (Fin.last r).castSucc * (mergeHom (ψ.symm t))⁻¹

lemma splitBwd_map (ψ : SurfaceGroup g (r + 1) ≃* FreeGroup L) (p t : FreeGroup L)
    (x : FreeGroup L) : splitBwd ψ p t (FreeGroup.map some x) = mergeHom (ψ.symm x) := by
  have : (splitBwd ψ p t).comp (FreeGroup.map some) = mergeHom.comp ψ.symm.toMonoidHom :=
    FreeGroup.ext_hom _ _ fun l ↦ by simp [splitBwd]
  exact DFunLike.congr_fun this x

lemma splitFwd_mergeHom (ψ : SurfaceGroup g (r + 1) ≃* FreeGroup L) (p q t : FreeGroup L)
    (hpq : ψ (cusp (Fin.last r)) = p * q) (x : SurfaceGroup g (r + 1)) :
    splitFwd ψ p q t hpq (mergeHom x) = FreeGroup.map some (ψ x) := by
  have : (splitFwd ψ p q t hpq).comp mergeHom = (FreeGroup.map some).comp ψ.toMonoidHom := by
    refine hom_ext (fun i ↦ by simp [splitFwd, mergeHom]) (fun i ↦ by simp [splitFwd, mergeHom])
      fun k ↦ ?_
    induction k using Fin.lastCases with
    | last =>
      simp only [MonoidHom.comp_apply, mergeHom, lift_cusp, Fin.lastCases_last, _root_.map_mul,
        splitFwd, Fin.lastCases_castSucc, MulEquiv.coe_toMonoidHom, hpq]
      group
    | cast k => simp [splitFwd, mergeHom]
  exact DFunLike.congr_fun this x

/-- **Splitting a cusp**: from `Π_{g,r+1} ≃* F(L)` with last cusp `p q`, an isomorphism
`Π_{g,r+2} ≃* F(Option L)` with the same images of the first `r` cusps and last two cusps
`p e t` and `t⁻¹ e⁻¹ q` (`e = none`). -/
def splitCusp (ψ : SurfaceGroup g (r + 1) ≃* FreeGroup L) (p q t : FreeGroup L)
    (hpq : ψ (cusp (Fin.last r)) = p * q) : SurfaceGroup g (r + 2) ≃* FreeGroup (Option L) :=
  MonoidHom.toMulEquiv (splitFwd ψ p q t hpq) (splitBwd ψ p t)
    (hom_ext (fun i ↦ by simp [splitFwd, splitBwd_map, mergeHom])
      (fun i ↦ by simp [splitFwd, splitBwd_map, mergeHom]) fun k ↦ by
        induction k using Fin.lastCases with
        | last =>
          simp only [MonoidHom.comp_apply, splitFwd, lift_cusp, Fin.lastCases_last, _root_.map_mul,
            _root_.map_inv, splitBwd_map, MonoidHom.id_apply]
          simp only [splitBwd, FreeGroup.lift_apply_of]
          have h : mergeHom (ψ.symm p) * mergeHom (ψ.symm q) =
              cusp (Fin.last r).castSucc * cusp (Fin.last (r + 1)) := by
            rw [← _root_.map_mul, ← _root_.map_mul, ← hpq, MulEquiv.symm_apply_apply, mergeHom,
              lift_cusp, Fin.lastCases_last]
          have h' : mergeHom (ψ.symm q) = (mergeHom (ψ.symm p))⁻¹ *
              (cusp (Fin.last r).castSucc * cusp (Fin.last (r + 1))) := eq_inv_mul_of_mul_eq h
          rw [h']
          group
        | cast k =>
          induction k using Fin.lastCases with
          | last =>
            simp only [MonoidHom.comp_apply, splitFwd, lift_cusp, Fin.lastCases_castSucc,
              Fin.lastCases_last, _root_.map_mul, splitBwd_map, MonoidHom.id_apply]
            simp only [splitBwd, FreeGroup.lift_apply_of]
            group
          | cast k => simp [splitFwd, splitBwd_map, mergeHom])
    (FreeGroup.ext_hom _ _ fun o ↦ by
      cases o with
      | some l => simp [splitBwd, splitFwd_mergeHom]
      | none =>
        simp only [MonoidHom.comp_apply, splitBwd, FreeGroup.lift_apply_of, _root_.map_mul,
          _root_.map_inv, MonoidHom.id_apply]
        rw [splitFwd_mergeHom, splitFwd_mergeHom]
        simp only [splitFwd, lift_cusp, Fin.lastCases_castSucc, Fin.lastCases_last,
          MulEquiv.apply_symm_apply]
        group)

variable (ψ : SurfaceGroup g (r + 1) ≃* FreeGroup L) (p q t : FreeGroup L)
  (hpq : ψ (cusp (Fin.last r)) = p * q)

lemma splitCusp_cusp (k : Fin r) :
    splitCusp ψ p q t hpq (cusp k.castSucc.castSucc) = FreeGroup.map some (ψ (cusp k.castSucc)) :=
  by simp [splitCusp, splitFwd]

lemma splitCusp_cusp_castSucc_last :
    splitCusp ψ p q t hpq (cusp (Fin.last r).castSucc) =
      FreeGroup.map some p * of none * FreeGroup.map some t := by
  simp [splitCusp, splitFwd]

lemma splitCusp_cusp_last :
    splitCusp ψ p q t hpq (cusp (Fin.last (r + 1))) =
      (FreeGroup.map some t)⁻¹ * (of none)⁻¹ * FreeGroup.map some q := by
  simp [splitCusp, splitFwd]

end split

/-! ### Joining two cusps into a handle -/

section handle

variable {L : Type*}

/-- `η : Π_{g,r+2} → Π_{g+1,r+1}`: `c_r ↦ Q⁻¹ a_g Q`, `c_{r+1} ↦ Q⁻¹ a_g⁻¹ P⁻¹` with
`P = ∏_{i<g} [aᵢ, bᵢ]`, `Q = ∏_{k<r} c_k`. -/
def handleHom : SurfaceGroup g (r + 2) →* SurfaceGroup (g + 1) (r + 1) :=
  lift (fun i ↦ genA i.castSucc) (fun i ↦ genB i.castSucc)
    (Fin.lastCases ((ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc)⁻¹ *
        (genA (Fin.last g))⁻¹ *
        (commProd (fun i : Fin g ↦ genA (r := r + 1) i.castSucc) fun i ↦ genB i.castSucc)⁻¹)
      (Fin.lastCases ((ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc)⁻¹ *
          genA (Fin.last g) * ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc)
        fun k ↦ cusp k.castSucc)) (by
      rw [ordProd_succ, ordProd_succ]
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      group)

variable (ψ : SurfaceGroup g (r + 2) ≃* FreeGroup L) (s t : FreeGroup L)

/-- The images `P'`, `Q'`, `C₁`, `C₂`, `E` used by `addHandle`. -/
def hP : FreeGroup (Option L) := FreeGroup.map some (ψ (commProd genA genB))
/-- `Q'`. -/
def hQ : FreeGroup (Option L) :=
  FreeGroup.map some (ψ (ordProd fun k : Fin r ↦ cusp k.castSucc.castSucc))
/-- `C₁`. -/
def hC₁ : FreeGroup (Option L) := FreeGroup.map some (ψ (cusp (Fin.last r).castSucc))
/-- `C₂`. -/
def hC₂ : FreeGroup (Option L) := FreeGroup.map some (ψ (cusp (Fin.last (r + 1))))
/-- `E = s e t`. -/
def hE : FreeGroup (Option L) := FreeGroup.map some s * of none * FreeGroup.map some t

lemma hC₂_eq : hC₂ ψ = (hP ψ * hQ ψ * hC₁ ψ)⁻¹ := by
  have h := congrArg (fun x ↦ FreeGroup.map some (ψ x)) (relation (g := g) (r := r + 2))
  simp only [ordProd_succ, _root_.map_mul, _root_.map_one] at h
  rw [eq_comm, inv_eq_iff_mul_eq_one, ← h, hP, hQ, hC₁, hC₂]
  group

/-- The forward map of `addHandle`. -/
def handleFwd : SurfaceGroup (g + 1) (r + 1) →* FreeGroup (Option L) :=
  lift (Fin.lastCases (hQ ψ * hC₁ ψ * (hQ ψ)⁻¹) fun i ↦ FreeGroup.map some (ψ (genA i)))
    (Fin.lastCases (hQ ψ * (hE s t)⁻¹ * (hQ ψ)⁻¹) fun i ↦ FreeGroup.map some (ψ (genB i)))
    (Fin.lastCases (hP ψ * ((hQ ψ * hC₁ ψ * (hQ ψ)⁻¹) * (hQ ψ * (hE s t)⁻¹ * (hQ ψ)⁻¹) *
        (hQ ψ * hC₁ ψ * (hQ ψ)⁻¹)⁻¹ * (hQ ψ * (hE s t)⁻¹ * (hQ ψ)⁻¹)⁻¹) * hQ ψ)⁻¹
      fun k ↦ FreeGroup.map some (ψ (cusp k.castSucc.castSucc))) (by
      rw [commProd_succ, ordProd_succ]
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      have hP' : commProd (fun i : Fin g ↦ FreeGroup.map some (ψ (genA i)))
          (fun i ↦ FreeGroup.map some (ψ (genB i))) = hP ψ := by
        rw [hP, map_commProd', map_commProd']
      have hQ' : ordProd (fun k : Fin r ↦ FreeGroup.map some (ψ (cusp k.castSucc.castSucc))) =
          hQ ψ := by
        rw [hQ, map_ordProd', map_ordProd']
      rw [hP', hQ']
      group)

/-- The backward map of `addHandle`. -/
def handleBwd : FreeGroup (Option L) →* SurfaceGroup (g + 1) (r + 1) :=
  FreeGroup.lift fun o ↦ match o with
    | some l => handleHom (ψ.symm (of l))
    | none => (handleHom (ψ.symm s))⁻¹ *
        (ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc)⁻¹ * (genB (Fin.last g))⁻¹ *
        (ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc) * (handleHom (ψ.symm t))⁻¹

lemma handleBwd_map (x : FreeGroup L) :
    handleBwd ψ s t (FreeGroup.map some x) = handleHom (ψ.symm x) := by
  have : (handleBwd ψ s t).comp (FreeGroup.map some) = handleHom.comp ψ.symm.toMonoidHom :=
    FreeGroup.ext_hom _ _ fun l ↦ by simp [handleBwd]
  exact DFunLike.congr_fun this x

lemma handleHom_Q : handleHom (ordProd fun k : Fin r ↦ cusp (g := g) k.castSucc.castSucc) =
    ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc := by
  rw [map_ordProd']
  simp [handleHom]

lemma handleHom_P : handleHom (commProd (genA (g := g) (r := r + 2)) genB) =
    commProd (fun i : Fin g ↦ genA (r := r + 1) i.castSucc) fun i ↦ genB i.castSucc := by
  rw [map_commProd']
  simp [handleHom]

lemma handleFwd_Q : handleFwd ψ s t (ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc) =
    hQ ψ := by
  rw [map_ordProd', hQ, map_ordProd', map_ordProd']
  simp [handleFwd]

lemma handleFwd_P : handleFwd ψ s t
    (commProd (fun i : Fin g ↦ genA (r := r + 1) i.castSucc) fun i ↦ genB i.castSucc) =
    hP ψ := by
  rw [map_commProd', hP, map_commProd', map_commProd']
  simp [handleFwd]

lemma handleHom_c₁ : handleHom (cusp (g := g) (Fin.last r).castSucc) =
    (ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc)⁻¹ * genA (Fin.last g) *
      ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc := by
  simp [handleHom]

lemma handleHom_c₂ : handleHom (cusp (g := g) (Fin.last (r + 1))) =
    (ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc)⁻¹ * (genA (Fin.last g))⁻¹ *
      (commProd (fun i : Fin g ↦ genA (r := r + 1) i.castSucc) fun i ↦ genB i.castSucc)⁻¹ := by
  simp [handleHom]

lemma handleFwd_a : handleFwd ψ s t (genA (Fin.last g)) = hQ ψ * hC₁ ψ * (hQ ψ)⁻¹ := by
  simp [handleFwd]

lemma handleFwd_b : handleFwd ψ s t (genB (Fin.last g)) = hQ ψ * (hE s t)⁻¹ * (hQ ψ)⁻¹ := by
  simp [handleFwd]

lemma handleFwd_c : handleFwd ψ s t (cusp (Fin.last r)) =
    (hP ψ * ((hQ ψ * hC₁ ψ * (hQ ψ)⁻¹) * (hQ ψ * (hE s t)⁻¹ * (hQ ψ)⁻¹) *
        (hQ ψ * hC₁ ψ * (hQ ψ)⁻¹)⁻¹ * (hQ ψ * (hE s t)⁻¹ * (hQ ψ)⁻¹)⁻¹) * hQ ψ)⁻¹ := by
  simp [handleFwd]

lemma handleFwd_handleHom (x : SurfaceGroup g (r + 2)) :
    handleFwd ψ s t (handleHom x) = FreeGroup.map some (ψ x) := by
  have : (handleFwd ψ s t).comp handleHom = (FreeGroup.map some).comp ψ.toMonoidHom := by
    refine hom_ext (fun i ↦ by simp [handleFwd, handleHom])
      (fun i ↦ by simp [handleFwd, handleHom]) fun k ↦ ?_
    induction k using Fin.lastCases with
    | last =>
      rw [MonoidHom.comp_apply, handleHom_c₂, _root_.map_mul, _root_.map_mul, _root_.map_inv,
        _root_.map_inv, _root_.map_inv, handleFwd_Q, handleFwd_a, handleFwd_P]
      change _ = hC₂ ψ
      rw [hC₂_eq]
      group
    | cast k =>
      induction k using Fin.lastCases with
      | last =>
        rw [MonoidHom.comp_apply, handleHom_c₁, _root_.map_mul, _root_.map_mul,
          _root_.map_inv, handleFwd_Q, handleFwd_a]
        change _ = hC₁ ψ
        group
      | cast k => simp [handleFwd, handleHom]
  exact DFunLike.congr_fun this x

/-- **Adding a handle**: from `Π_{g,r+2} ≃* F(L)` with last two cusps `C₁`, `C₂`, an isomorphism
`Π_{g+1,r+1} ≃* F(Option L)` with the same images of the first `r` cusps and last cusp conjugate
to `C₁ E C₂ E⁻¹`, `E = s e t` (`e = none`). -/
def addHandle : SurfaceGroup (g + 1) (r + 1) ≃* FreeGroup (Option L) :=
  MonoidHom.toMulEquiv (handleFwd ψ s t) (handleBwd ψ s t)
    (by
      have hS : handleBwd ψ s t (hE s t) =
          (ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc)⁻¹ * (genB (Fin.last g))⁻¹ *
            (ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc) := by
        simp only [hE, _root_.map_mul, handleBwd_map]
        simp only [handleBwd, FreeGroup.lift_apply_of]
        group
      have hQb : handleBwd ψ s t (hQ ψ) = ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc :=
        by rw [hQ, handleBwd_map, MulEquiv.symm_apply_apply, handleHom_Q]
      have hPb : handleBwd ψ s t (hP ψ) =
          commProd (fun i : Fin g ↦ genA (r := r + 1) i.castSucc) fun i ↦ genB i.castSucc := by
        rw [hP, handleBwd_map, MulEquiv.symm_apply_apply, handleHom_P]
      have hC₁b : handleBwd ψ s t (hC₁ ψ) =
          (ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc)⁻¹ * genA (Fin.last g) *
            ordProd fun k : Fin r ↦ cusp (g := g + 1) k.castSucc := by
        rw [hC₁, handleBwd_map, MulEquiv.symm_apply_apply]
        simp [handleHom]
      refine hom_ext (fun i ↦ ?_) (fun i ↦ ?_) fun k ↦ ?_
      · induction i using Fin.lastCases with
        | last =>
          rw [MonoidHom.comp_apply, handleFwd_a, _root_.map_mul, _root_.map_mul, _root_.map_inv,
            hQb, hC₁b, MonoidHom.id_apply]
          group
        | cast i => simp [handleFwd, handleBwd_map, handleHom]
      · induction i using Fin.lastCases with
        | last =>
          rw [MonoidHom.comp_apply, handleFwd_b, _root_.map_mul, _root_.map_mul, _root_.map_inv,
            _root_.map_inv, hQb, hS, MonoidHom.id_apply]
          group
        | cast i => simp [handleFwd, handleBwd_map, handleHom]
      · induction k using Fin.lastCases with
        | last =>
          rw [MonoidHom.comp_apply, handleFwd_c, MonoidHom.id_apply]
          simp only [_root_.map_mul, _root_.map_inv, hQb, hS, hPb, hC₁b]
          have h := relation (g := g + 1) (r := r + 1)
          rw [commProd_succ, ordProd_succ] at h
          refine inv_eq_of_mul_eq_one_right ?_
          rw [← h]
          group
        | cast k => simp [handleFwd, handleBwd_map, handleHom])
    (FreeGroup.ext_hom _ _ fun o ↦ by
      cases o with
      | some l => simp [handleBwd, handleFwd_handleHom]
      | none =>
        simp only [MonoidHom.comp_apply, handleBwd, FreeGroup.lift_apply_of, _root_.map_mul,
          _root_.map_inv, MonoidHom.id_apply]
        rw [handleFwd_handleHom, handleFwd_handleHom, handleFwd_Q, handleFwd_b,
          MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hE]
        group)

lemma addHandle_cusp (k : Fin r) :
    addHandle ψ s t (cusp k.castSucc) = FreeGroup.map some (ψ (cusp k.castSucc.castSucc)) := by
  simp [addHandle, handleFwd]

lemma isConj_addHandle_cusp_last :
    IsConj (addHandle ψ s t (cusp (Fin.last r)))
      (hC₁ ψ * hE s t * hC₂ ψ * (hE s t)⁻¹) := by
  refine isConj_iff.2 ⟨hE s t, ?_⟩
  change hE s t * handleFwd ψ s t (cusp (Fin.last r)) * (hE s t)⁻¹ = _
  rw [handleFwd_c, hC₂_eq]
  group

end handle

end SurfaceGroup

end Pi1
