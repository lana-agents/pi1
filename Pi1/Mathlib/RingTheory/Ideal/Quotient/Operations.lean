/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

@[simp]
lemma Ideal.quotientInfRingEquivPiQuotient_mk {R ι : Type*} [Finite ι] [CommRing R]
    (I : ι → Ideal R) (hI : Pairwise (Function.onFun IsCoprime I)) (x : R) :
    Ideal.quotientInfRingEquivPiQuotient I hI x = fun _ ↦ Ideal.Quotient.mk _ x := rfl
