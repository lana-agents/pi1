/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Pi1.Orbifold.EtaleProfinite

/-!
# Comparison with Mathlib's category of finite étale algebras

For a trivial group `A` (`Subsingleton A`, e.g. `A = PUnit` acting trivially on `R` through the
scoped instance `TrivialAction.punitMulSemiringAction`), the category `EquivEtale R A` of coded
finite étale `R`-algebras is equivalent to `(CommAlgCat.FiniteEtale R)ᵒᵖ`
(`EquivEtale.toFiniteEtale`; every finite étale algebra has a presentation
`R[x₁, …, xₙ] ⧸ I`), compatibly with the fibre functors. Hence `etalePi1 R A Ω` is isomorphic, as
a topological group, to Mathlib's `Aut (CommAlgCat.FiniteEtale.fiber R Ω)`
(`etalePi1EquivAutFiber`).

## Main results

* `FibreAut.restrict_bijective`: restriction along an equivalence of categories is bijective;
  `FibreAut.equivOfIsEquivalence` is the resulting isomorphism of topological groups (compact
  case).
* `FibreAut.equivAut`: for `F : C ⥤ FintypeCat`, `FibreAut (F ⋙ FintypeCat.incl) ≃ₜ* Aut F`,
  where `Aut F` carries Mathlib's topology (`CategoryTheory.PreGaloisCategory`).
* `etalePi1EquivAutFiber : etalePi1 R A Ω ≃ₜ* Aut (CommAlgCat.FiniteEtale.fiber R Ω)` for a
  trivial group `A`; `etalePi1EquivOfSubsingleton : etalePi1 R A Ω ≃ₜ* etalePi1 R A' Ω` for two
  trivial groups.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace Pi1.Orbifold

namespace FibreAut

section Equivalence

variable {C : Type u} [Category.{v} C] {C' : Type*} [Category* C'] {F : C ⥤ Type w}
  {F' : C' ⥤ Type w}

lemma restrict_eq_conjAut (G : C' ⥤ C) [G.IsEquivalence] (e : G ⋙ F ≅ F') (σ : FibreAut F) :
    restrict G e σ = e.conjAut
      (((Functor.FullyFaithful.ofFullyFaithful
        ((Functor.whiskeringLeft C' C (Type w)).obj G)).autMulEquivOfFullyFaithful F) σ) := by
  ext c x
  rw [Iso.conjAut_apply]
  rfl

lemma restrict_bijective (G : C' ⥤ C) [G.IsEquivalence] (e : G ⋙ F ≅ F') :
    Function.Bijective (restrict G e) := by
  have : ⇑(restrict G e) = ⇑(((Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringLeft C' C (Type w)).obj G)).autMulEquivOfFullyFaithful F).trans
        e.conjAut) := funext (restrict_eq_conjAut G e)
  rw [this]
  exact MulEquiv.bijective _

/-- An equivalence of categories `G : C' ⥤ C` compatible with fibre functors induces an
isomorphism of topological groups `FibreAut F ≃ₜ* FibreAut F'` (for `FibreAut F` compact). -/
noncomputable def equivOfIsEquivalence (G : C' ⥤ C) [G.IsEquivalence] (e : G ⋙ F ≅ F')
    [CompactSpace (FibreAut F)] : FibreAut F ≃ₜ* FibreAut F' where
  toMulEquiv := MulEquiv.ofBijective (restrict G e) (restrict_bijective G e)
  continuous_toFun := continuous_restrict G e
  continuous_invFun :=
    (continuous_restrict G e).continuous_symm_of_equiv_compact_to_t2
      (f := Equiv.ofBijective _ (restrict_bijective G e))

@[simp] lemma equivOfIsEquivalence_apply (G : C' ⥤ C) [G.IsEquivalence] (e : G ⋙ F ≅ F')
    [CompactSpace (FibreAut F)] (σ : FibreAut F) :
    equivOfIsEquivalence G e σ = restrict G e σ := rfl

end Equivalence

section FintypeCat

open PreGaloisCategory

variable {C : Type u} [Category.{v} C] (F : C ⥤ FintypeCat.{w})

instance (c : C) : Finite ((F ⋙ FintypeCat.incl).obj c) := (F.obj c).property

/-- For a functor `F` valued in finite types, the group `FibreAut (F ⋙ FintypeCat.incl)` with
the stabilizer topology is isomorphic, as a topological group, to Mathlib's `Aut F` (with the
topology induced from `∏ X, Aut (F.obj X)`, `CategoryTheory.PreGaloisCategory`). -/
noncomputable def equivAut : FibreAut (F ⋙ FintypeCat.incl) ≃ₜ* Aut F :=
  haveI : CompactSpace (FibreAut (F ⋙ FintypeCat.incl)) := compactSpace_of_finite _
  let e : FibreAut (F ⋙ FintypeCat.incl) ≃* Aut F :=
    (((Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl).whiskeringRight
      C).autMulEquivOfFullyFaithful F).symm
  have he : Continuous e := by
    rw [continuous_induced_rng]
    refine continuous_pi fun X => continuous_discrete_rng.2 fun τ => ?_
    have happ : ∀ σ x, (e σ).hom.app X x = σ.app X x := fun σ x => by
      conv_rhs => rw [← e.symm_apply_apply σ]
      rfl
    have : (fun σ => (⇑(autEmbedding F) ∘ ⇑e) σ X) ⁻¹' {τ} =
        ⋂ x : F.obj X, {σ : FibreAut (F ⋙ FintypeCat.incl) | σ.app X x = τ.hom x} := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · rintro h x
        rw [← happ, ← h]
        rfl
      · intro h
        apply Iso.ext
        ext x
        rw [← h x, ← happ]
        rfl
    rw [this]
    exact isOpen_iInter_of_finite fun x => isOpen_setOf_app_eq (F ⋙ FintypeCat.incl) X x (τ.hom x)
  { e with
    continuous_toFun := he
    continuous_invFun := he.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) }

lemma equivAut_symm_app (τ : Aut F) (c : C) (x : F.obj c) :
    ((equivAut F).symm τ).app c x = τ.hom.app c x :=
  rfl

lemma equivAut_hom_app (σ : FibreAut (F ⋙ FintypeCat.incl)) (c : C) (x : F.obj c) :
    ((equivAut F) σ).hom.app c x = σ.app c x := by
  rw [← equivAut_symm_app, ContinuousMulEquiv.symm_apply_apply]

end FintypeCat

end FibreAut

/-- The trivial action of `PUnit` on a semiring. -/
@[implicit_reducible]
def punitMulSemiringAction (R : Type*) [Semiring R] : MulSemiringAction PUnit.{u + 1} R :=
  MulSemiringAction.compHom R (1 : PUnit.{u + 1} →* RingAut R)

namespace TrivialAction

attribute [scoped instance] punitMulSemiringAction

end TrivialAction

open scoped TrivialAction

noncomputable section

variable (R : Type u) [CommRing R] (A : Type u) [Group A] [MulSemiringAction A R]
  [Subsingleton A] (Ω : Type u) [Field Ω] [Algebra R Ω]

namespace EquivEtale

variable {A} in
lemma act_σ_of_subsingleton (X : EquivEtale R A) (a : A) (y : X.B) :
    (X.act a).σ y = y := by
  obtain rfl : a = 1 := Subsingleton.elim _ _
  rw [map_one]
  rfl

/-- A coded finite étale algebra (with an action of a trivial group) as an object of Mathlib's
category of finite étale algebras. -/
def toFiniteEtale : EquivEtale R A ⥤ (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ where
  obj X :=
    letI := X.etale
    letI := X.finite
    Opposite.op (CommAlgCat.FiniteEtale.of R X.B)
  map {X Y} φ :=
    letI := X.etale; letI := X.finite; letI := Y.etale; letI := Y.finite
    (CommAlgCat.FiniteEtale.ofHom φ.f).op

namespace toFiniteEtale

instance : (toFiniteEtale R A).Faithful where
  map_injective {X Y} φ ψ h := by
    apply EquivEtale.Hom.ext
    ext y
    exact congrArg (fun g => g.unop.hom.hom y) h

instance : (toFiniteEtale R A).Full where
  map_surjective {X Y} g := ⟨⟨g.unop.hom.hom, fun a y => by
    rw [act_σ_of_subsingleton, act_σ_of_subsingleton]⟩, rfl⟩

/-- A presentation of a finite étale algebra: a coded finite étale algebra with trivial action
isomorphic to it. -/
def presentation (S : CommAlgCat.FiniteEtale.{u} R) : EquivEtale R A :=
  let h := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance :
    Algebra.FiniteType R S)
  let e := Ideal.quotientKerAlgEquivOfSurjective h.choose_spec.choose_spec
  { n := h.choose
    I := RingHom.ker h.choose_spec.choose
    etale := Algebra.Etale.of_equiv e.symm
    finite := Module.Finite.equiv e.symm.toLinearEquiv
    act := 1
    act_a := fun _ => Subsingleton.elim _ _ }

/-- The presentation is isomorphic to the given algebra. -/
def presentationIso (S : CommAlgCat.FiniteEtale.{u} R) :
    (toFiniteEtale R A).obj (presentation R A S) ≅ Opposite.op S :=
  let h := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance :
    Algebra.FiniteType R S)
  (CommAlgCat.FiniteEtale.isoMk
    (Ideal.quotientKerAlgEquivOfSurjective h.choose_spec.choose_spec)).op.symm

instance : (toFiniteEtale R A).EssSurj where
  mem_essImage S := ⟨presentation R A S.unop, ⟨presentationIso R A S.unop⟩⟩

instance : (toFiniteEtale R A).IsEquivalence where

end toFiniteEtale

end EquivEtale

/-- The fibre functor on coded finite étale algebras is the restriction of Mathlib's fibre
functor. -/
def toFiniteEtaleFiberIso :
    EquivEtale.toFiniteEtale R A ⋙ CommAlgCat.FiniteEtale.fiber.{u} R Ω ⋙ FintypeCat.incl ≅
      etaleFibre R A Ω :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **Comparison with Mathlib.** For a trivial group `A`, the étale fundamental group
`etalePi1 R A Ω` is isomorphic, as a topological group, to Mathlib's automorphism group of
the fibre functor `CommAlgCat.FiniteEtale.fiber R Ω` on finite étale `R`-algebras. -/
def etalePi1EquivAutFiber :
    etalePi1 R A Ω ≃ₜ* Aut (CommAlgCat.FiniteEtale.fiber.{u} R Ω) :=
  haveI : CompactSpace
      (FibreAut (CommAlgCat.FiniteEtale.fiber.{u} R Ω ⋙ FintypeCat.incl)) :=
    FibreAut.compactSpace_of_finite _
  (FibreAut.equivOfIsEquivalence (EquivEtale.toFiniteEtale R A)
    (toFiniteEtaleFiberIso R A Ω)).symm.trans (FibreAut.equivAut _)

/-- The automorphisms of `etalePi1EquivAutFiber` act on the fibre `X.B →ₐ[R] Ω` as the
corresponding automorphism of Mathlib's fibre functor. -/
lemma etalePi1EquivAutFiber_symm_app (σ : Aut (CommAlgCat.FiniteEtale.fiber.{u} R Ω))
    (X : EquivEtale R A) (f : X.B →ₐ[R] Ω) :
    ((etalePi1EquivAutFiber R A Ω).symm σ).app X f =
      σ.hom.app ((EquivEtale.toFiniteEtale R A).obj X) f :=
  rfl

/-- **The étale fundamental group does not see a trivial group**: for trivial groups `A` and
`A'` acting on `R`, `etalePi1 R A Ω ≃ₜ* etalePi1 R A' Ω`, compatibly with the fibres. -/
def etalePi1EquivOfSubsingleton (A' : Type u) [Group A'] [MulSemiringAction A' R]
    [Subsingleton A'] : etalePi1 R A Ω ≃ₜ* etalePi1 R A' Ω :=
  (etalePi1EquivAutFiber R A Ω).trans (etalePi1EquivAutFiber R A' Ω).symm

end

end Pi1.Orbifold
