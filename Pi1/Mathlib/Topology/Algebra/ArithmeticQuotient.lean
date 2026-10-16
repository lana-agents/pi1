/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Kernels of quotients of profinite groups detected by indices

Let `π : Π →* G` be a surjective homomorphism of groups with kernel `Δ`. For a subgroup `U` of
finite index, `[G : π U] = [Π : U]` holds if and only if `Δ ≤ U` (`Subgroup.index_map_eq_iff`).
If `Π` is profinite and `Δ` is closed, `Δ` is therefore the intersection of the open subgroups
`U` with `[G : π U] = [Π : U]` (`ProfiniteGrp.ker_eq_sInf_index_map_eq`).

This is the formal group-theoretic step of [AbsAnab] Lemma 1.1.4 (ii) (last sentence: "the
subgroup `Δ ⊆ Π` may be characterized as the intersection of those open subgroups `Π' ⊆ Π` such
that `[G : G'] = [Π : Π']`"), through which [AbsAnab] Lemma 1.3.8 (group-theoreticity of the
arithmetic quotient `Π_X ↠ G_K`) is deduced. The consequence for isomorphisms is
`ProfiniteGrp.map_ker_eq_ker_of_index_map_eq`: an isomorphism `α : Π₁ ≃ₜ* Π₂` of profinite
groups with surjections `πᵢ : Πᵢ ↠ Gᵢ` (closed kernels) that preserves the function
`U ↦ [Gᵢ : πᵢ U]` on open subgroups maps `ker π₁` onto `ker π₂`.

In [AbsAnab] the index function `U ↦ [Gᵢ : πᵢ U]` is shown to be group-theoretic (i.e. preserved
by every `α`) by expressing `[G : G'] · [F_𝔭 : ℚ_p]` through the abelianisation of `U`, using
local class field theory and Lemma 1.1.5 (Tate modules of semi-abelian varieties); that numerical
input is not part of this file.
-/

@[expose] public section

namespace Subgroup

variable {P G : Type*} [Group P] [Group G]

/-- For a surjection `π : Π →* G` and a subgroup `U` of finite index, `[G : π U] = [Π : U]` if and
only if `ker π ≤ U`. -/
@[to_additive /-- For a surjection `π : Π →+ G` and a subgroup `U` of finite index,
`[G : π U] = [Π : U]` if and only if `ker π ≤ U`. -/]
theorem index_map_eq_iff {π : P →* G} (hπ : Function.Surjective π) (U : Subgroup P)
    [U.FiniteIndex] : (U.map π).index = U.index ↔ π.ker ≤ U := by
  refine ⟨fun h ↦ ?_, index_map_eq U hπ⟩
  rw [index_map, π.range_eq_top_of_surjective hπ, index_top, mul_one,
    ← relIndex_mul_index (le_sup_left : U ≤ U ⊔ π.ker)] at h
  have hne : (U ⊔ π.ker).index ≠ 0 :=
    (FiniteIndex.index_ne_zero (H := U)) ∘ fun h0 ↦ by
      rw [← relIndex_mul_index (le_sup_left : U ≤ U ⊔ π.ker), h0, mul_zero]
  have h1 : U.relIndex (U ⊔ π.ker) = 1 :=
    (Nat.mul_eq_right hne).mp h.symm
  exact le_sup_right.trans (relIndex_eq_one.mp h1)

end Subgroup

namespace ProfiniteGrp

variable {P G : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P] [Group G]

/-- **The kernel of `Π ↠ G` is detected by indices** ([AbsAnab] Lemma 1.1.4 (ii), formal part):
for a surjection `π : Π →* G` from a profinite group with closed kernel, `ker π` is the
intersection of the open subgroups `U` with `[G : π U] = [Π : U]`. -/
theorem ker_eq_sInf_index_map_eq {π : P →* G} (hπ : Function.Surjective π)
    (hc : IsClosed (π.ker : Set P)) :
    π.ker = sInf {U : Subgroup P | IsOpen (U : Set P) ∧ (U.map π).index = U.index} := by
  have key := closedSubgroup_eq_sInf_open ⟨π.ker, hc⟩
  change π.ker = _ at key
  rw [key]
  congr 1
  ext U
  refine and_congr_right fun hU ↦ ?_
  haveI := Subgroup.quotient_finite_of_isOpen U hU
  haveI : U.FiniteIndex := U.finiteIndex_of_finite_quotient
  exact (Subgroup.index_map_eq_iff hπ U).symm

variable {P₂ G₂ : Type*} [Group P₂] [TopologicalSpace P₂] [IsTopologicalGroup P₂]
  [CompactSpace P₂] [TotallyDisconnectedSpace P₂] [Group G₂]

/-- **Isomorphisms preserving the arithmetic indices preserve the geometric kernel** ([AbsAnab]
Lemma 1.3.8, formal part): let `πᵢ : Πᵢ ↠ Gᵢ` be surjections from profinite groups with closed
kernels and `α : Π₁ ≃ₜ* Π₂` an isomorphism with `[G₂ : π₂ (α U)] = [G₁ : π₁ U]` for every open
subgroup `U ⊆ Π₁`. Then `α (ker π₁) = ker π₂`, i.e. `α` is compatible with the quotients
`Πᵢ ↠ Gᵢ`. -/
theorem map_ker_eq_ker_of_index_map_eq {π₁ : P →* G} {π₂ : P₂ →* G₂}
    (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂)
    (hc₁ : IsClosed (π₁.ker : Set P)) (hc₂ : IsClosed (π₂.ker : Set P₂)) (α : P ≃ₜ* P₂)
    (hα : ∀ U : Subgroup P, IsOpen (U : Set P) →
      ((U.map (α : P →* P₂)).map π₂).index = (U.map π₁).index) :
    π₁.ker.map (α : P →* P₂) = π₂.ker := by
  rw [ker_eq_sInf_index_map_eq hπ₁ hc₁, ker_eq_sInf_index_map_eq hπ₂ hc₂]
  have hcomap (V : Subgroup P₂) : V = (V.comap (α : P →* P₂)).map (α : P →* P₂) :=
    (Subgroup.map_comap_eq_self_of_surjective α.surjective V).symm
  refine le_antisymm (le_sInf fun V ⟨hV, hVi⟩ ↦ ?_) ?_
  · rw [hcomap V]
    refine Subgroup.map_mono (sInf_le ⟨hV.preimage α.continuous, ?_⟩)
    rw [← hα _ (hV.preimage α.continuous), ← hcomap V, hVi,
      Subgroup.index_comap_of_surjective _ α.surjective]
  · intro y hy
    refine ⟨α.symm y, Subgroup.mem_sInf.mpr fun U ⟨hU, hUi⟩ ↦ ?_, α.apply_symm_apply y⟩
    have hU' : IsOpen ((U.map (α : P →* P₂) : Subgroup P₂) : Set P₂) := by
      rw [Subgroup.coe_map]
      exact α.toHomeomorph.isOpenMap _ hU
    have hmem := Subgroup.mem_sInf.mp hy _ ⟨hU', by
      rw [hα U hU, hUi]
      exact (Subgroup.index_map_of_bijective α.bijective U).symm⟩
    obtain ⟨x, hx, hxy⟩ := hmem
    rw [← hxy]
    exact (congrArg (· ∈ U) (α.symm_apply_apply x)).mpr hx

end ProfiniteGrp
