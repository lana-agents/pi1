/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.FundamentalGroup.DenseOpen

/-!
# Extending finite étale covers from an open subscheme

Let `U ⊆ X` be an open subscheme and `V` a finite étale `U`-scheme. The natural candidate for
an extension of `V` to `X` is the relative normalization `N` of `X` in `V` (along
`g : V ⟶ U ⟶ X`). Normalization commutes with restriction to opens (smooth base change), so:

* `AlgebraicGeometry.FiniteEtale.isFiniteEtale_fromNormalization_of_iSup`: `N ⟶ X` is finite
  étale as soon as the normalizations of the restrictions of `g` to the members of an open cover
  of `X` are finite étale;
* `AlgebraicGeometry.FiniteEtale.isFiniteEtale_normalization_of_sup`: for `X = U ∪ U'`, it
  suffices that the normalization of `U'` in `V ×_X U'` is finite étale (over `U` the
  normalization is `V` itself);
* `AlgebraicGeometry.FiniteEtale.extension`, `AlgebraicGeometry.FiniteEtale.extensionIso`:
  then `N` is a finite étale `X`-scheme whose restriction to `U` is isomorphic to `V`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.FiniteEtale

variable {X V : Scheme.{u}}

/-- The relative normalization of `g : V ⟶ X` is finite étale if it is so after restriction
to the members of an open cover of `X`. -/
theorem isFiniteEtale_fromNormalization_of_iSup (g : V ⟶ X) [QuasiCompact g]
    [QuasiSeparated g] {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, IsFiniteEtale (pullback.snd g (U i).ι).fromNormalization) :
    IsFiniteEtale g.fromNormalization := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i ↦ ?_
  change IsFiniteEtale ((pullbackRestrictIsoRestrict _ _).inv ≫ pullback.snd _ _)
  rw [MorphismProperty.cancel_left_of_respectsIso @IsFiniteEtale]
  have : pullback.snd g.fromNormalization (U i).ι =
      inv (g.normalizationPullback (U i).ι) ≫ (pullback.snd g (U i).ι).fromNormalization := by
    rw [← Scheme.Hom.normalizationPullback_snd, IsIso.inv_hom_id_assoc]
  rw [this, MorphismProperty.cancel_left_of_respectsIso @IsFiniteEtale]
  exact H i

variable (U : X.Opens) [QuasiCompact U.ι] (A : FiniteEtale U)

omit [QuasiCompact U.ι] in
/-- `V ×_X U ≅ V` for a `U`-scheme `V`, `U ⊆ X` open. -/
lemma isPullback_comp_ι : IsPullback (𝟙 A.left) A.hom (A.hom ≫ U.ι) U.ι :=
  IsPullback.of_horiz_isIso_mono ⟨by simp⟩

omit [QuasiCompact U.ι] in
lemma isFiniteEtale_pullback_snd_comp_ι : IsFiniteEtale (pullback.snd (A.hom ≫ U.ι) U.ι) := by
  have h := isPullback_comp_ι U A
  have hsnd : pullback.snd (A.hom ≫ U.ι) U.ι = h.isoPullback.inv ≫ A.hom := by
    rw [IsPullback.isoPullback_inv_snd]
  rw [hsnd]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsFiniteEtale _ _).mpr inferInstance

/-- Over `U`, the normalization of `X` in a finite étale `U`-scheme is finite étale. -/
lemma isFiniteEtale_fromNormalization_pullback_snd_self :
    IsFiniteEtale (pullback.snd (A.hom ≫ U.ι) U.ι).fromNormalization := by
  haveI := isFiniteEtale_pullback_snd_comp_ι U A
  have : (pullback.snd (A.hom ≫ U.ι) U.ι).fromNormalization =
      inv (pullback.snd (A.hom ≫ U.ι) U.ι).toNormalization ≫ pullback.snd (A.hom ≫ U.ι) U.ι := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toNormalization_fromNormalization]
  rw [this]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsFiniteEtale _ _).mpr inferInstance

/-- For `X = U ∪ U'`, the normalization of `X` in a finite étale `U`-scheme `A` is finite étale
over `X` as soon as the normalization of `U'` in `A ×_X U'` is finite étale. -/
theorem isFiniteEtale_normalization_of_sup (U' : X.Opens) (hUU' : U ⊔ U' = ⊤)
    (H : IsFiniteEtale (pullback.snd (A.hom ≫ U.ι) U'.ι).fromNormalization) :
    IsFiniteEtale (A.hom ≫ U.ι).fromNormalization := by
  refine isFiniteEtale_fromNormalization_of_iSup (A.hom ≫ U.ι)
    (fun b : Bool ↦ if b then U else U') (by simpa [iSup_bool_eq] using hUU') fun b ↦ ?_
  cases b
  · exact H
  · exact isFiniteEtale_fromNormalization_pullback_snd_self U A

/-- The extension of a finite étale `U`-scheme `A` to `X`: the normalization of `X` in `A`,
assuming it is finite étale. -/
noncomputable def extension [IsFiniteEtale (A.hom ≫ U.ι).fromNormalization] : FiniteEtale X :=
  mk (A.hom ≫ U.ι).fromNormalization

/-- The restriction of the extension to `U` is `A`. -/
noncomputable def extensionIso [IsFiniteEtale (A.hom ≫ U.ι).fromNormalization] :
    (pullback U.ι).obj (extension U A) ≅ A :=
  haveI := isFiniteEtale_pullback_snd_comp_ι U A
  MorphismProperty.Over.isoMk
    (asIso (inv ((A.hom ≫ U.ι).normalizationPullback U.ι) ≫
      inv (pullback.snd (A.hom ≫ U.ι) U.ι).toNormalization ≫
        (isPullback_comp_ι U A).isoPullback.inv)) (by
    change (inv _ ≫ inv _ ≫ (isPullback_comp_ι U A).isoPullback.inv) ≫ A.hom =
      pullback.snd (A.hom ≫ U.ι).fromNormalization U.ι
    simp only [Category.assoc, IsPullback.isoPullback_inv_snd]
    rw [IsIso.inv_comp_eq, IsIso.inv_comp_eq]
    simp only [Scheme.Hom.normalizationPullback_snd, Scheme.Hom.toNormalization_fromNormalization])

end AlgebraicGeometry.FiniteEtale
