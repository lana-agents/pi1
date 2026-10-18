/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.SchreierRibbon

/-!
# Filling cusps of a finite covering of a punctured sphere: a surface group

Let `F = F(x₀, …, xₙ)` act transitively on a finite set `Ω`, `H` the stabiliser of `ω₀`, and
`x_∞ = (x₀ ⋯ xₙ)⁻¹` (`Pi1.ReidemeisterSchreier.xInf`).

**Theorem** (`Pi1.ReidemeisterSchreier.exists_quotient_cuspSubgroup_mulEquiv_surfaceGroup`).
There are `g, r` and an isomorphism `Θ : H ⧸ cuspSubgroup univ ω₀ ≃* Π_{g,r}` together with a
bijection `μ` from the `⟨x_∞⟩`-orbits on `Ω` to `Fin r` such that for every `γ ∈ F` the cusp loop
`γ⁻¹ x_∞^m γ ∈ H` (`m` the length of the `⟨x_∞⟩`-orbit of `γ ω₀`) is sent to a conjugate of the
cusp `c_{μ [γ ω₀]}`, and
`2g + r + ∑ₐ #(⟨xₐ⟩-orbits) + |Ω| = |Ω| (n + 1) + 2`.

Topologically (`n = 1`, `Ω` the monodromy of a Belyi map `f : X → ℙ¹` restricted to
`ℙ¹ ∖ {0, 1, ∞}`): `π₁(X ∖ f⁻¹(∞)) ≃ Π_{g,r}` with the cusps going to the loops around the
points over `∞`, and `2 - 2g = |Ω| (1 - (n + 1)) + ∑ₐ #f⁻¹(aₐ) + #f⁻¹(∞)` is Riemann–Hurwitz.

## Proof

The Schreier transversal of a breadth-first search gives a free basis of `H` indexed by the
non-tree edges (`Transversal.basis`); the Schreier ribbon graph (`SchreierRibbon.ribbon`) has
face words the rewritings of the cusp loops (`rewrite_cj`, `ribbon_faceWord_true`,
`ribbon_faceWord_false`), so the surface normal form of ribbon graphs
(`Pi1.Ribbon.RibbonData.isGeom`) identifies `H` with `Π_{g,R}`, the cusps going to conjugates of
the cusp loops of all faces. The cusp subgroup is the normal closure of the cusp loops of the
`⟨xₐ⟩`-orbits (`cuspSubgroup_eq_normalClosure`), and killing the corresponding cusps of
`Π_{g,R}` (`SurfaceGroup.exists_quotient_normalClosure_cusp_mulEquiv`) leaves `Π_{g,r}`.
-/

@[expose] public section

namespace Pi1.ReidemeisterSchreier

open FreeGroup Equiv Function SchreierRibbon

namespace Transversal

variable {α Ω : Type*} [MulAction (FreeGroup α) Ω] {ω₀ : Ω} (T : Transversal α ω₀)

/-- The Reidemeister rewriting of `t (g ω)⁻¹ g t ω` is the cocycle of `g` at `ω`. -/
lemma rewrite_cj (g : FreeGroup α) (ω : Ω) : T.rewrite (T.cj g ω) = coc T.lab g ω := by
  change coc T.lab ((T.t (g • ω))⁻¹ * g * T.t ω) ω₀ = _
  have h1 := coc_inv T.lab (T.t (g • ω)) ω₀
  rw [T.t_smul, T.coc_t, inv_one] at h1
  rw [coc_mul, coc_mul, T.coc_t, mul_one, T.t_smul, h1, one_mul]

lemma rewrite_surjective : Surjective T.rewrite := fun x ↦
  ⟨T.toStab x, DFunLike.congr_fun T.rewrite_comp_toStab x⟩

/-- The Reidemeister rewriting as an isomorphism `H ≃* F(non-tree edges)`. -/
noncomputable def rewriteEquiv :
    MulAction.stabilizer (FreeGroup α) ω₀ ≃* FreeGroup T.Gens :=
  MulEquiv.ofBijective T.rewrite ⟨T.rewrite_injective, T.rewrite_surjective⟩

@[simp] lemma rewriteEquiv_apply (h : MulAction.stabilizer (FreeGroup α) ω₀) :
    T.rewriteEquiv h = T.rewrite h := rfl

lemma cj_coe_of_smul {g : FreeGroup α} {ω : Ω} (h : g • ω = ω) :
    (T.cj g ω : FreeGroup α) = (T.t ω)⁻¹ * g * T.t ω := by
  simp [cj, h]

/-- The cusp subgroup is the normal closure of the cusp loops `t ω⁻¹ aᵐ t ω` (`m` the length of
the `⟨a⟩`-orbit of `ω`). -/
theorem cuspSubgroup_eq_normalClosure [Finite Ω] (A : Set α) :
    cuspSubgroup A ω₀ =
      Subgroup.normalClosure {h | ∃ a ∈ A, ∃ ω, T.cj ((of a) ^ per a ω) ω = h} := by
  apply le_antisymm
  · refine Subgroup.normalClosure_le_normal ?_
    rintro h ⟨a, ha, g, k, hk⟩
    set ω := g⁻¹ • ω₀ with hω
    have hfix : (of a) ^ k • ω = ω := by
      have h0 := MulAction.mem_stabilizer_iff.1 h.2
      rw [hk, mul_smul, mul_smul] at h0
      exact (smul_eq_iff_eq_inv_smul g).1 h0
    obtain ⟨m, hm⟩ := MulAction.zpow_smul_eq_iff_minimalPeriod_dvd.1 hfix
    have hc : T.cj ((of a) ^ per a ω) ω ∈
        Subgroup.normalClosure {h | ∃ a ∈ A, ∃ ω, T.cj ((of a) ^ per a ω) ω = h} :=
      Subgroup.subset_normalClosure ⟨a, ha, ω, rfl⟩
    let h' : MulAction.stabilizer (FreeGroup α) ω₀ :=
      ⟨g * T.t ω, by rw [MulAction.mem_stabilizer_iff, mul_smul, T.t_smul, hω, smul_inv_smul]⟩
    have key : h = h' * T.cj ((of a) ^ per a ω) ω ^ m * h'⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, h',
        T.cj_coe_of_smul (pow_per_smul a ω), hk, hm]
      rw [show (T.t ω)⁻¹ * of a ^ per a ω * T.t ω =
          (T.t ω)⁻¹ * of a ^ per a ω * ((T.t ω)⁻¹)⁻¹ by rw [inv_inv], conj_zpow, zpow_mul,
        zpow_natCast]
      group
    rw [key]
    exact (Subgroup.normalClosure_normal).conj_mem _ (zpow_mem hc m) h'
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨a, ha, ω, rfl⟩
    apply Subgroup.subset_normalClosure
    refine ⟨a, ha, (T.t ω)⁻¹, per a ω, ?_⟩
    rw [T.cj_coe_of_smul (pow_per_smul a ω), inv_inv, zpow_natCast]

end Transversal

variable {n : ℕ} {Ω : Type*} [MulAction (FreeGroup (Fin (n + 1))) Ω] [Finite Ω] {ω₀ : Ω}

/-- **Filling the finite cusps of a covering of a punctured sphere.** For a transitive action of
`F(x₀, …, xₙ)` on a finite set `Ω`, the quotient of the stabiliser `H` of `ω₀` by the normal
closure of the cusp loops around `x₀, …, xₙ` is a surface group `Π_{g,r}`, `r` the number of
`⟨x_∞⟩`-orbits, with the cusp loops `γ⁻¹ x_∞^m γ` around `∞` going to conjugates of the cusp
generators, and `2g + r + ∑ₐ #(⟨xₐ⟩-orbits) + |Ω| = |Ω| (n + 1) + 2`. -/
theorem exists_quotient_cuspSubgroup_mulEquiv_surfaceGroup
    (htrans : ∀ ω, ∃ g : FreeGroup (Fin (n + 1)), g • ω₀ = ω) :
    ∃ (g r : ℕ)
      (Θ : MulAction.stabilizer (FreeGroup (Fin (n + 1))) ω₀ ⧸
        cuspSubgroup (Set.univ : Set (Fin (n + 1))) ω₀ ≃* SurfaceGroup g r)
      (μ : MulAction.orbitRel.Quotient (Subgroup.zpowers (xInf n)) Ω ≃ Fin r),
      (∀ (h : MulAction.stabilizer (FreeGroup (Fin (n + 1))) ω₀) (γ : FreeGroup (Fin (n + 1))),
        (h : FreeGroup (Fin (n + 1))) = γ⁻¹ * xInf n ^ perInf n (γ • ω₀) * γ →
          IsConj (Θ (QuotientGroup.mk h))
            (SurfaceGroup.cusp (μ (Quotient.mk _ (γ • ω₀))))) ∧
      2 * g + r + ∑ a : Fin (n + 1),
          Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (of a)) Ω) + Nat.card Ω =
        Nat.card Ω * (n + 1) + 2 := by
  classical
  set T := (Parent.bfs htrans).toTransversal with hT
  obtain ⟨g, R, Ψ, ν, hcard, hν, hsurj, hconj⟩ := (ribbon T).isGeom
  have hD : Nonempty (Ω × Fin (n + 1) × Bool) := ⟨(ω₀, 0, true)⟩
  have hsurj := hsurj hD
  let p : Fin R → Prop := fun j ↦ ∃ ω, ν (ω, 0, false) = j
  let Φ : MulAction.stabilizer (FreeGroup (Fin (n + 1))) ω₀ ≃* SurfaceGroup g R :=
    T.rewriteEquiv.trans Ψ.symm
  have hconjΦ (x : Ω × Fin (n + 1) × Bool) :
      IsConj (Ψ.symm (Ribbon.faceWord (ribbon T).φ (ribbon T).lab x))
        (SurfaceGroup.cusp (ν x)) := by
    have := SurfaceGroup.isConj_map Ψ.symm (hconj x)
    rw [MulEquiv.symm_apply_apply] at this
    exact this.symm
  have hΦtrue (ω : Ω) (a : Fin (n + 1)) :
      Φ (T.cj ((of a) ^ per a ω) ω) =
        Ψ.symm (Ribbon.faceWord (ribbon T).φ (ribbon T).lab (ω, a, true)) := by
    simp [Φ, Transversal.rewrite_cj, ribbon_faceWord_true]
  have hΦfalse (ω : Ω) :
      Φ (T.cj (xInf n ^ perInf n ω) ω) =
        Ψ.symm (Ribbon.faceWord (ribbon T).φ (ribbon T).lab (ω, 0, false)) := by
    simp [Φ, Transversal.rewrite_cj, ribbon_faceWord_false]
  have notp (ω : Ω) (a : Fin (n + 1)) : ¬ p (ν (ω, a, true)) := by
    rintro ⟨ω', h⟩
    exact ribbon_not_sameCycle_true_false T ω ω' a 0 ((hν _ _).1 h.symm)
  have hmap : (cuspSubgroup (Set.univ : Set (Fin (n + 1))) ω₀).map Φ.toMonoidHom =
      Subgroup.normalClosure {x | ∃ j, ¬ p j ∧ SurfaceGroup.cusp j = x} := by
    rw [T.cuspSubgroup_eq_normalClosure, Subgroup.map_normalClosure _ _ Φ.surjective]
    apply SurfaceGroup.normalClosure_eq_of_isConj
    · rintro _ ⟨_, ⟨a, -, ω, rfl⟩, rfl⟩
      refine ⟨SurfaceGroup.cusp (ν (ω, a, true)), ⟨_, notp ω a, rfl⟩, ?_⟩
      change IsConj (Φ (T.cj ((of a) ^ per a ω) ω)) _
      rw [hΦtrue]
      exact hconjΦ _
    · rintro _ ⟨j, hj, rfl⟩
      obtain ⟨⟨ω, a, b⟩, rfl⟩ := hsurj j
      cases b with
      | false =>
        exfalso
        obtain ⟨ω', h⟩ := ribbon_exists_sameCycle_false T ω a
        exact hj ⟨ω', ((hν _ _).2 h).symm⟩
      | true =>
        refine ⟨_, ⟨_, ⟨a, trivial, ω, rfl⟩, rfl⟩, ?_⟩
        change IsConj _ (Φ (T.cj ((of a) ^ per a ω) ω))
        rw [hΦtrue]
        exact (hconjΦ _).symm
  obtain ⟨Θ₀, μ₀, hΘ₀⟩ := SurfaceGroup.exists_quotient_normalClosure_cusp_mulEquiv (g := g) p
  -- the `⟨x_∞⟩`-orbits are the faces through the darts `(ω, 0, false)`
  let fInf : MulAction.orbitRel.Quotient (Subgroup.zpowers (xInf n)) Ω → {j // p j} :=
    Quotient.lift (fun ω ↦ ⟨ν (ω, 0, false), ω, rfl⟩) (by
      intro ω ω' hrel
      obtain ⟨k, hk⟩ := (exists_zpow_iff_exists_pow _).1
        ((mk_eq_mk_zpowers_iff (xInf n)).1 (Quotient.sound hrel))
      exact Subtype.ext ((hν _ _).2 ((ribbon_sameCycle_false_iff T ω' ω).2 ⟨k, hk⟩)).symm)
  have hfInf : Bijective fInf := by
    constructor
    · intro q q'
      induction q using Quotient.inductionOn with | h ω => ?_
      induction q' using Quotient.inductionOn with | h ω' => ?_
      intro h
      have h' := congrArg Subtype.val h
      obtain ⟨k, hk⟩ := (ribbon_sameCycle_false_iff T ω ω').1 ((hν _ _).1 h')
      exact ((mk_eq_mk_zpowers_iff (xInf n)).2 ⟨k, by rw [zpow_natCast]; exact hk⟩).symm
    · rintro ⟨j, ω, rfl⟩
      exact ⟨Quotient.mk _ ω, rfl⟩
  let eInf := Equiv.ofBijective fInf hfInf
  -- the `⟨xₐ⟩`-orbits are the faces through the darts `(ω, a, true)`
  let fFin : (Σ a : Fin (n + 1), MulAction.orbitRel.Quotient (Subgroup.zpowers (of a)) Ω) →
      {j // ¬ p j} := fun s ↦
    Quotient.lift (fun ω ↦ (⟨ν (ω, s.1, true), notp ω s.1⟩ : {j // ¬ p j})) (by
      intro ω ω' hrel
      obtain ⟨k, hk⟩ := (exists_zpow_iff_exists_pow _).1
        ((mk_eq_mk_zpowers_iff (of s.1)).1 (Quotient.sound hrel))
      exact Subtype.ext ((hν _ _).2 ((ribbon_sameCycle_true_iff T ω' s.1 _).2
        ⟨k, by rw [hk]⟩)).symm) s.2
  have hfFin : Bijective fFin := by
    constructor
    · rintro ⟨a, q⟩ ⟨a', q'⟩
      induction q using Quotient.inductionOn with | h ω => ?_
      induction q' using Quotient.inductionOn with | h ω' => ?_
      intro h
      have h' := congrArg Subtype.val h
      obtain ⟨k, hk⟩ := (ribbon_sameCycle_true_iff T ω a _).1 ((hν _ _).1 h')
      simp only [Prod.mk.injEq, and_true] at hk
      obtain ⟨hk, rfl⟩ := hk
      congr 1
      exact ((mk_eq_mk_zpowers_iff (of a)).2 ⟨k, by rw [zpow_natCast]; exact hk⟩).symm
    · rintro ⟨j, hj⟩
      obtain ⟨⟨ω, a, b⟩, rfl⟩ := hsurj j
      cases b with
      | false =>
        exfalso
        obtain ⟨ω', h⟩ := ribbon_exists_sameCycle_false T ω a
        exact hj ⟨ω', ((hν _ _).2 h).symm⟩
      | true => exact ⟨⟨a, Quotient.mk _ ω⟩, rfl⟩
  let eFin := Equiv.ofBijective fFin hfFin
  refine ⟨g, Fintype.card {j // p j}, (QuotientGroup.congr _ _ Φ hmap).trans Θ₀,
    eInf.trans μ₀, ?_, ?_⟩
  · intro h γ hh
    set ω := γ • ω₀ with hω
    have hX : xInf n ^ perInf n ω • ω = ω :=
      MulAction.pow_smul_eq_iff_minimalPeriod_dvd.2 dvd_rfl
    have hc : IsConj h (T.cj (xInf n ^ perInf n ω) ω) := by
      refine isConj_iff.2 ⟨⟨(T.t ω)⁻¹ * γ, ?_⟩, ?_⟩
      · rw [MulAction.mem_stabilizer_iff, mul_smul, ← hω, inv_smul_eq_iff, T.t_smul]
      · apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hh, T.cj_coe_of_smul hX]
        group
    have h1 := SurfaceGroup.isConj_map ((QuotientGroup.congr _ _ Φ hmap).trans Θ₀)
      (SurfaceGroup.isConj_map (QuotientGroup.mk' (cuspSubgroup (Set.univ : Set (Fin (n + 1))) ω₀))
        hc)
    simp only [QuotientGroup.mk'_apply, MulEquiv.trans_apply, QuotientGroup.congr_mk] at h1
    refine h1.trans ?_
    rw [show Φ (T.cj (xInf n ^ perInf n ω) ω) = _ from hΦfalse ω]
    have h2 := SurfaceGroup.isConj_map Θ₀
      (SurfaceGroup.isConj_map (QuotientGroup.mk' _) (hconjΦ (ω, 0, false)))
    simp only [QuotientGroup.mk'_apply] at h2
    refine h2.trans ?_
    exact hΘ₀ ⟨ν (ω, 0, false), ω, rfl⟩
  · have hgens := (Parent.bfs htrans).card_gens
    rw [Nat.card_fin] at hgens
    have hR : R = Fintype.card {j // p j} + Nat.card {j // ¬ p j} := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_sum, Nat.card_congr (Equiv.sumCompl p),
        Nat.card_fin]
    have hfin : Nat.card {j // ¬ p j} = ∑ a : Fin (n + 1),
        Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (of a)) Ω) := by
      rw [← Nat.card_congr eFin, Nat.card_sigma]
    rw [← hfin]
    change Nat.card T.Gens + Nat.card Ω = Nat.card Ω * (n + 1) + 1 at hgens
    omega

end Pi1.ReidemeisterSchreier
