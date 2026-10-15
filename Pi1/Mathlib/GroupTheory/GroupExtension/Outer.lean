/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.Group

/-!
# Outer actions of group extensions

For an extension `1 → N → E → G → 1` (Mathlib's `GroupExtension N E G`), conjugation in `E`
induces the **outer action** `GroupExtension.outerAction : G →* Out(N)`, where
`Out(N) = Aut(N) ⧸ Inn(N)` (`MulAut.Out N`). If `N` is **centre-free**, the extension
is recovered from the outer action:

  `E ≃* Aut(N) ×_{Out(N)} G`   (`GroupExtension.equivFiberProd`).

This is the group-theoretic form of the statement that the arithmetic fundamental group
`Π_X` of a hyperbolic curve is determined by the geometric fundamental group `Δ_X` (which is
centre-free, `Pi1.SurfaceGroup.center_eq_bot`) and the outer Galois representation
`G_k → Out(Δ_X)` (Mochizuki, *Topics in absolute anabelian geometry I*, §0).
-/

@[expose] public section

namespace MulAut

variable (N : Type*) [Group N]

/-- The inner automorphisms of `N`. -/
def inner : Subgroup (MulAut N) := (MulAut.conj : N →* MulAut N).range

instance : (inner N).Normal where
  conj_mem := by
    rintro _ ⟨n, rfl⟩ φ
    refine ⟨φ n, ?_⟩
    ext x
    simp [MulAut.mul_apply]

/-- The outer automorphism group `Out(N) = Aut(N) ⧸ Inn(N)`. -/
abbrev Out : Type _ := MulAut N ⧸ inner N

end MulAut

namespace GroupExtension

open MulAut

variable {N E G : Type*} [Group N] [Group E] [Group G] (S : GroupExtension N E G)

lemma conjAct_inl (m : N) : S.conjAct (S.inl m) = MulAut.conj m := by
  ext n
  apply S.inl_injective
  rw [S.inl_conjAct_comm, MulAut.conj_apply, map_mul, map_mul, map_inv]

/-- The map `E → Out(N)`, `e ↦ [conjugation by e]`. -/
noncomputable def conjOut : E →* Out N := (QuotientGroup.mk' (inner N)).comp S.conjAct

lemma ker_rightHom_le_ker_conjOut : S.rightHom.ker ≤ S.conjOut.ker := by
  rw [← S.range_inl_eq_ker_rightHom]
  rintro _ ⟨m, rfl⟩
  simp only [MonoidHom.mem_ker, conjOut, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, conjAct_inl]
  exact ⟨m, rfl⟩

/-- **The outer action** `G → Out(N)` of the extension `1 → N → E → G → 1`. -/
noncomputable def outerAction : G →* Out N :=
  (QuotientGroup.lift _ S.conjOut S.ker_rightHom_le_ker_conjOut).comp
    (QuotientGroup.quotientKerEquivOfSurjective S.rightHom S.rightHom_surjective).symm.toMonoidHom

lemma outerAction_rightHom (e : E) :
    S.outerAction (S.rightHom e) = QuotientGroup.mk (S.conjAct e) := by
  simp only [outerAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have : (QuotientGroup.quotientKerEquivOfSurjective S.rightHom S.rightHom_surjective).symm
      (S.rightHom e) = QuotientGroup.mk e := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [this, QuotientGroup.lift_mk]
  rfl

/-- The fibre product `Aut(N) ×_{Out(N)} G`. -/
noncomputable def fiberProd : Subgroup (MulAut N × G) :=
  MonoidHom.eqLocus ((QuotientGroup.mk' (inner N)).comp (MonoidHom.fst _ _))
    (S.outerAction.comp (MonoidHom.snd _ _))

/-- The map `E → Aut(N) ×_{Out(N)} G`, `e ↦ (conjugation by e, image of e)`. -/
noncomputable def toFiberProd : E →* S.fiberProd :=
  (S.conjAct.prod S.rightHom).codRestrict _ fun e ↦ by
    change QuotientGroup.mk (S.conjAct e) = S.outerAction (S.rightHom e)
    rw [outerAction_rightHom]

/-- **A centre-free kernel determines the extension through its outer action**:
`E ≃* Aut(N) ×_{Out(N)} G`. -/
theorem toFiberProd_bijective (hN : Subgroup.center N = ⊥) :
    Function.Bijective S.toFiberProd := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro e he
    have h1 : S.conjAct e = 1 := congrArg (fun x ↦ (x.1 : MulAut N × G).1) he
    have h2 : S.rightHom e = 1 := congrArg (fun x ↦ (x.1 : MulAut N × G).2) he
    obtain ⟨m, rfl⟩ : e ∈ S.inl.range := by
      rw [S.range_inl_eq_ker_rightHom]; exact h2
    have hm : m ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro n
      have := congrArg (fun φ : MulAut N ↦ φ n) h1
      simp only [conjAct_inl, MulAut.conj_apply, MulAut.one_apply] at this
      calc n * m = m * n * m⁻¹ * m := by rw [this]
        _ = m * n := by group
    rw [hN, Subgroup.mem_bot] at hm
    rw [hm, map_one]
  · rintro ⟨⟨α, g⟩, hαg⟩
    obtain ⟨e, rfl⟩ := S.rightHom_surjective g
    have hαg' : (QuotientGroup.mk α : Out N) = QuotientGroup.mk (S.conjAct e) := by
      rw [← outerAction_rightHom]; exact hαg
    obtain ⟨m, hm⟩ : (S.conjAct e)⁻¹ * α ∈ inner N := QuotientGroup.eq.1 hαg'.symm
    refine ⟨e * S.inl m, Subtype.ext ?_⟩
    change (S.conjAct (e * S.inl m), S.rightHom (e * S.inl m)) = (α, S.rightHom e)
    rw [map_mul, map_mul, conjAct_inl, S.rightHom_inl, mul_one]
    congr 1
    rw [hm, mul_inv_cancel_left]

/-- **`E ≃* Aut(N) ×_{Out(N)} G` for a centre-free `N`.** -/
noncomputable def equivFiberProd (hN : Subgroup.center N = ⊥) : E ≃* S.fiberProd :=
  MulEquiv.ofBijective S.toFiberProd (S.toFiberProd_bijective hN)

end GroupExtension
