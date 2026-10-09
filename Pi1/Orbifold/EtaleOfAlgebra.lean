/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Orbifold.Etale

/-!
# Coding equivariant finite étale algebras

Every finite étale `R`-algebra `B` (in `Type u`) with a lift `ρ : A →* SemilinearAut R A B` of
the action of `A` is isomorphic to an object of `EquivEtale R A` (`EquivEtale.ofAlgebra`): choose
a presentation `R[x₁, …, xₙ] ⧸ I ≃ₐ[R] B` and transport the action along it
(`SemilinearAut.congr`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace Pi1.Orbifold

noncomputable section

variable {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R]

namespace SemilinearAut

variable {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']

/-- Transport of semilinear automorphisms along an isomorphism of `R`-algebras. -/
def congr (e : B ≃ₐ[R] B') : SemilinearAut R A B →* SemilinearAut R A B' where
  toFun g := ⟨g.a, (e.symm.toRingEquiv.trans g.σ).trans e.toRingEquiv, fun r => by
    simp [g.map_algebraMap]⟩
  map_one' := SemilinearAut.ext rfl (by ext; simp)
  map_mul' g h := SemilinearAut.ext rfl (by ext; simp)

@[simp] lemma congr_a (e : B ≃ₐ[R] B') (g : SemilinearAut R A B) : (congr e g).a = g.a := rfl

@[simp] lemma congr_σ_apply (e : B ≃ₐ[R] B') (g : SemilinearAut R A B) (x : B') :
    (congr e g).σ x = e (g.σ (e.symm x)) := rfl

end SemilinearAut

namespace EquivEtale

variable (R) (B : Type u) [CommRing B] [Algebra R B]

lemma exists_presentation [Algebra.FiniteType R B] :
    ∃ n : ℕ, ∃ f : MvPolynomial (Fin n) R →ₐ[R] B, Function.Surjective f :=
  Algebra.FiniteType.iff_quotient_mvPolynomial''.1 inferInstance

variable [Algebra.FiniteType R B]

/-- The number of generators of the chosen presentation. -/
def presN : ℕ := (exists_presentation R B).choose

/-- The chosen presentation. -/
def presHom : MvPolynomial (Fin (presN R B)) R →ₐ[R] B :=
  (exists_presentation R B).choose_spec.choose

lemma presHom_surjective : Function.Surjective (presHom R B) :=
  (exists_presentation R B).choose_spec.choose_spec

/-- The isomorphism of the coded algebra with `B`. -/
def presEquiv : LevelRing R (presN R B) (RingHom.ker (presHom R B)) ≃ₐ[R] B :=
  Ideal.quotientKerAlgEquivOfSurjective (presHom_surjective R B)

variable {R B} [Algebra.Etale R B] [Module.Finite R B]

/-- **The coded object** of a finite étale `R`-algebra with a lift of the action of `A`. -/
def ofAlgebra (ρ : A →* SemilinearAut R A B) (hρ : ∀ a, (ρ a).a = a) : EquivEtale R A where
  n := presN R B
  I := RingHom.ker (presHom R B)
  etale := Algebra.Etale.of_equiv (presEquiv R B).symm
  finite := Module.Finite.equiv (presEquiv R B).symm.toLinearEquiv
  act := (SemilinearAut.congr (presEquiv R B).symm).comp ρ
  act_a a := hρ a

/-- The coded object is isomorphic to the given algebra. -/
def ofAlgebraEquiv (ρ : A →* SemilinearAut R A B) (hρ : ∀ a, (ρ a).a = a) :
    (ofAlgebra ρ hρ).B ≃ₐ[R] B :=
  presEquiv R B

lemma ofAlgebraEquiv_act (ρ : A →* SemilinearAut R A B) (hρ : ∀ a, (ρ a).a = a) (a : A)
    (x : (ofAlgebra ρ hρ).B) :
    ofAlgebraEquiv ρ hρ (((ofAlgebra ρ hρ).act a).σ x) = (ρ a).σ (ofAlgebraEquiv ρ hρ x) := by
  change presEquiv R B ((presEquiv R B).symm ((ρ a).σ (presEquiv R B x))) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

lemma ofAlgebraEquiv_symm_act (ρ : A →* SemilinearAut R A B) (hρ : ∀ a, (ρ a).a = a) (a : A)
    (y : B) :
    ((ofAlgebra ρ hρ).act a).σ ((ofAlgebraEquiv ρ hρ).symm y) =
      (ofAlgebraEquiv ρ hρ).symm ((ρ a).σ y) := by
  apply (ofAlgebraEquiv ρ hρ).injective
  rw [ofAlgebraEquiv_act, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

end EquivEtale

end

end Pi1.Orbifold
