/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib

/-!
# Semilinear automorphisms and coded finite étale algebras

Let `Y = Spec R` be an affine scheme with an action of a group `A` by ring automorphisms of `R`.
For an `R`-algebra `B`, the group
`G_B = {(a, σ) : a ∈ A, σ ∈ Aut_ring(B), σ ∘ (R → B) = (R → B) ∘ (a • ·)}`
of ring automorphisms of `B` semilinear over elements of `A` is `SemilinearAut R A B`. A lift of
the action of `A` to `B` is a section `A →* G_B` of `G_B → A`; this is how finite étale covers
of the orbifold `[Y/A]` are described.

Finite étale algebras are coded by presentations `B = R[x₁, …, xₙ] ⧸ I` (`EtaleCode`), so that
they form a `Type u`.

## Main definitions

* `SemilinearAut R A B`: the group `G_B`, with `SemilinearAut.toA : G_B →* A`.
* `EtaleCode R`: a coded finite étale `R`-algebra.
-/

@[expose] public section

universe u

open CategoryTheory

namespace Pi1.Orbifold

noncomputable section

variable (R : Type u) [CommRing R] (A : Type u) [Group A] [MulSemiringAction A R]

/-- The group `G_B` of ring automorphisms of an `R`-algebra `B` which are semilinear over an
element of `A`. -/
@[ext]
structure SemilinearAut (B : Type u) [CommRing B] [Algebra R B] : Type u where
  /-- The element of `A` over which the automorphism lies. -/
  a : A
  /-- The ring automorphism. -/
  σ : B ≃+* B
  /-- Semilinearity. -/
  map_algebraMap : ∀ r : R, σ (algebraMap R B r) = algebraMap R B (a • r)

namespace SemilinearAut

variable {R A} {B : Type u} [CommRing B] [Algebra R B]

instance : One (SemilinearAut R A B) := ⟨⟨1, RingEquiv.refl B, fun r => by simp⟩⟩

instance : Mul (SemilinearAut R A B) :=
  ⟨fun g h => ⟨g.a * h.a, h.σ.trans g.σ, fun r => by
    simp [h.map_algebraMap, g.map_algebraMap, mul_smul]⟩⟩

instance : Inv (SemilinearAut R A B) :=
  ⟨fun g => ⟨g.a⁻¹, g.σ.symm, fun r => by
    apply g.σ.injective
    simp [g.map_algebraMap, smul_smul]⟩⟩

@[simp] lemma one_a : (1 : SemilinearAut R A B).a = 1 := rfl
@[simp] lemma one_σ : (1 : SemilinearAut R A B).σ = RingEquiv.refl B := rfl
@[simp] lemma mul_a (g h : SemilinearAut R A B) : (g * h).a = g.a * h.a := rfl
@[simp] lemma mul_σ (g h : SemilinearAut R A B) : (g * h).σ = h.σ.trans g.σ := rfl
@[simp] lemma inv_a (g : SemilinearAut R A B) : g⁻¹.a = g.a⁻¹ := rfl
@[simp] lemma inv_σ (g : SemilinearAut R A B) : g⁻¹.σ = g.σ.symm := rfl

instance : Group (SemilinearAut R A B) where
  mul_assoc g h k := SemilinearAut.ext (mul_assoc _ _ _) (by ext; rfl)
  one_mul g := SemilinearAut.ext (one_mul _) (by ext; rfl)
  mul_one g := SemilinearAut.ext (mul_one _) (by ext; rfl)
  inv_mul_cancel g := SemilinearAut.ext (inv_mul_cancel _) (by ext; simp)

/-- The projection `G_B →* A`. -/
def toA : SemilinearAut R A B →* A where
  toFun g := g.a
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma toA_apply (g : SemilinearAut R A B) : toA g = g.a := rfl

/-- An element of `G_B⁰ = ker (G_B → A)` is `R`-linear. -/
lemma σ_algebraMap_of_a_eq_one {g : SemilinearAut R A B} (hg : g.a = 1) (r : R) :
    g.σ (algebraMap R B r) = algebraMap R B r := by
  rw [g.map_algebraMap, hg, one_smul]

end SemilinearAut

/-- The coordinate ring `R[x₁, …, xₙ] ⧸ I` of a coded finite étale cover. -/
abbrev LevelRing (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)) : Type u :=
  MvPolynomial (Fin n) R ⧸ I

/-- **A coded finite étale `R`-algebra** `R[x₁, …, xₙ] ⧸ I`. -/
structure EtaleCode : Type u where
  /-- The number of generators. -/
  n : ℕ
  /-- The ideal of relations. -/
  I : Ideal (MvPolynomial (Fin n) R)
  /-- The algebra is étale over `R`. -/
  etale : Algebra.Etale R (LevelRing R n I)
  /-- The algebra is finite over `R`. -/
  finite : Module.Finite R (LevelRing R n I)

/-- The algebra of a coded finite étale `R`-algebra. -/
abbrev EtaleCode.B {R : Type u} [CommRing R] (c : EtaleCode R) : Type u := LevelRing R c.n c.I

end

end Pi1.Orbifold
