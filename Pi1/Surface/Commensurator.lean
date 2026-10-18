/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.Profinite
public import Pi1.Profinite.Commensurator

/-!
# Cuspidal inertia groups of `Π̂_{g,r+1}` are commensurably terminal

For the cuspidal generators `c₁, …, c_r` of `Π̂_{g,r+1}` other than the last one (which is
eliminated by the surface relation, so that `Π̂_{g,r+1} ≅ F̂(a₁, b₁, …, a_g, b_g, c₁, …, c_r)`
with `cⱼ` basis elements):

* `Pi1.SurfaceGroup.commensurator_inertia_castSucc`: the cuspidal inertia group `Iⱼ = ⟨cⱼ⟩‾`
  is **commensurably terminal**;
* `Pi1.SurfaceGroup.inertia_inf_conj_eq_bot`: for `i ≠ j`, `Iᵢ ∩ σ Iⱼ σ⁻¹ = 1`.

This is the group-theoretic content of [AbsTopI] Lemma 4.1 (i)
(`Topics in Absolute Anabelian Geometry I.txt` l.2741–2745) for these cusps (the decomposition
group of a cusp over an algebraically closed field is its inertia group); it is the condition
`ChainObj.IsCuspidal` (commensurator of a cuspidal inertia group) of the `•` step.
The last cusp needs another free basis (a Nielsen transformation), not done here.
-/

@[expose] public section

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology
open scoped Pointwise

namespace Pi1

section Transport

variable {G H : Type*} [Group G] [Group H] (e : G ≃* H)

/-- Conjugation commutes with `comap` along an isomorphism. -/
lemma conjAct_smul_comap (A : Subgroup H) (σ : G) :
    ConjAct.toConjAct σ • A.comap e.toMonoidHom =
      (ConjAct.toConjAct (e σ) • A).comap e.toMonoidHom := by
  ext x
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_comap, ConjAct.smul_def,
    map_inv, ConjAct.ofConjAct_toConjAct, MulEquiv.coe_toMonoidHom, map_mul]

/-- Commensurability is invariant under `comap` along an isomorphism. -/
lemma commensurable_comap_iff (A B : Subgroup H) :
    (A.comap e.toMonoidHom).Commensurable (B.comap e.toMonoidHom) ↔ A.Commensurable B := by
  have h : ∀ A B : Subgroup H,
      (A.comap e.toMonoidHom).relIndex (B.comap e.toMonoidHom) = A.relIndex B := fun A B ↦ by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective e.surjective]
  simp only [Subgroup.Commensurable, h]

/-- The commensurator of a `comap` along an isomorphism. -/
lemma commensurator_comap (A : Subgroup H) :
    Subgroup.Commensurable.commensurator (A.comap e.toMonoidHom) =
      (Subgroup.Commensurable.commensurator A).comap e.toMonoidHom := by
  ext σ
  simp only [Subgroup.Commensurable.commensurator_mem_iff, Subgroup.mem_comap,
    conjAct_smul_comap, commensurable_comap_iff, MulEquiv.coe_toMonoidHom]

end Transport

namespace SurfaceGroup

open Profinite

variable {g r : ℕ}

/-- `Iⱼ` for `j < r` is the preimage of the inertia group of the basis element `cⱼ` of
`F̂(a, b, c_{<r})`. -/
theorem inertia_castSucc_eq_comap (j : Fin r) :
    inertia (g := g) (r := r + 1) j.castSucc =
      (basisInertia (SurfaceGen.c j)).comap
        (profiniteFreeEquiv (g := g) (r := r)).toMulEquiv.toMonoidHom := by
  set e := profiniteFreeEquiv (g := g) (r := r)
  have hgen : e (etaFn (GrpCat.of (SurfaceGroup g (r + 1))) (cusp j.castSucc)) =
      gen (SurfaceGen.c j) := by
    simp only [e, profiniteFreeEquiv, completionCongr_apply, completionMap_eta,
      MulEquiv.coe_toMonoidHom, freeEquiv_cusp_castSucc]
  apply SetLike.coe_injective
  simp only [inertia, basisInertia, Subgroup.topologicalClosure_coe, Subgroup.coe_comap,
    MulEquiv.coe_toMonoidHom]
  change _ = e.toHomeomorph ⁻¹' _
  rw [Homeomorph.preimage_closure]
  congr 1
  ext x
  simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_preimage]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by rw [← hgen, ← map_zpow]; rfl⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, e.injective ?_⟩
    rw [map_zpow, hgen]
    exact hn

/-- **The cuspidal inertia group `Iⱼ ⊆ Π̂_{g,r+1}` (`j < r`) is commensurably terminal.** -/
theorem commensurator_inertia_castSucc (j : Fin r) :
    Subgroup.Commensurable.commensurator (inertia (g := g) (r := r + 1) j.castSucc) =
      inertia j.castSucc := by
  rw [inertia_castSucc_eq_comap, commensurator_comap, commensurator_basisInertia]

/-- **Distinct cuspidal inertia groups meet trivially**, also after conjugation (`i, j < r`). -/
theorem inertia_inf_conj_eq_bot {i j : Fin r} (hij : i ≠ j) (σ : ProfiniteSurfaceGroup g (r + 1)) :
    inertia (g := g) i.castSucc ⊓ (ConjAct.toConjAct σ • inertia (g := g) j.castSucc) = ⊥ := by
  rw [inertia_castSucc_eq_comap, inertia_castSucc_eq_comap, conjAct_smul_comap,
    ← Subgroup.comap_inf, basisInertia_inf_conj_eq_bot (by simpa using hij)]
  ext x
  simp

end SurfaceGroup

end Pi1
