/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Finiteness.Defs

@[expose] public section

universe u

lemma RingHom.finite_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] : (algebraMap R S).Finite ↔ Module.Finite R S := by
  simp only [RingHom.Finite]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl
