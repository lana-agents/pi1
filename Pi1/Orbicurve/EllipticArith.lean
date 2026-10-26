/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Orbicurve.Elliptic

/-!
# The arithmetic part of [CanLift], Proposition 2.7, split by complex multiplication

`AffOrbicurve.CanLift27Arith` (the converse part of [CanLift], Proposition 2.7: for an exceptional
`j(E)`, the once-punctured elliptic curve `E ∖ {0}` is `k`-arithmetic) is split into two named
statements according to the four exceptional `j`-invariants `excJ`:

* `AffOrbicurve.excJCM = {0, 1728}`: the two exceptional values with complex multiplication
  (by `ℤ[ζ₃]` resp. `ℤ[i]`; Sijsling's models `y² = x³ − 1728` and `y² = x(x² − 256)`);
* `AffOrbicurve.excJNonCM = {2¹⁴·31³/5³, 2²·73³/3⁴}`: the two exceptional values without complex
  multiplication (these `j` are not algebraic integers, while CM `j`-invariants are);
* `AffOrbicurve.CanLift27ArithCM`, `AffOrbicurve.CanLift27ArithNonCM`: the converse of
  [CanLift], Proposition 2.7 for `j(E) ∈ excJCM` resp. `j(E) ∈ excJNonCM`;
* `AffOrbicurve.canLift27Arith_iff`: `CanLift27Arith ↔ CanLift27ArithCM ∧ CanLift27ArithNonCM`.

The statements are not proved here.
-/

@[expose] public section

universe u

namespace AffOrbicurve

/-- **The exceptional `j`-invariants with complex multiplication**: `0` and `1728`. -/
def excJCM : Finset ℚ := {0, 1728}

/-- **The exceptional `j`-invariants without complex multiplication**:
`2¹⁴·31³/5³ = 488095744/125` and `2²·73³/3⁴ = 1556068/81` (Sijsling's curves `20.a1`, `24.a3`). -/
def excJNonCM : Finset ℚ := {488095744 / 125, 1556068 / 81}

lemma excJ_eq_union : excJ = excJCM ∪ excJNonCM := by
  ext c
  simp only [excJ, excJCM, excJNonCM, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
    or_assoc]

lemma mem_excJ_iff (c : ℚ) : c ∈ excJ ↔ c ∈ excJCM ∨ c ∈ excJNonCM := by
  rw [excJ_eq_union, Finset.mem_union]

/-- **[CanLift], Proposition 2.7, arithmetic case with complex multiplication**: if
`j(E) ∈ {0, 1728}`, then `E ∖ {0}` is `k`-arithmetic: it has no `k`-core. -/
def CanLift27ArithCM : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic],
    (∃ c ∈ excJCM, E.j = (c : k)) → IsArithmetic (punctured E)

/-- **[CanLift], Proposition 2.7, arithmetic case without complex multiplication**: if
`j(E) ∈ {2¹⁴·31³/5³, 2²·73³/3⁴}`, then `E ∖ {0}` is `k`-arithmetic: it has no `k`-core. -/
def CanLift27ArithNonCM : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic],
    (∃ c ∈ excJNonCM, E.j = (c : k)) → IsArithmetic (punctured E)

/-- The arithmetic part of [CanLift], Proposition 2.7 is the conjunction of its CM and non-CM
parts. -/
theorem canLift27Arith_iff :
    CanLift27Arith.{u} ↔ CanLift27ArithCM.{u} ∧ CanLift27ArithNonCM.{u} := by
  refine ⟨fun h => ⟨fun k _ _ E _ ⟨c, hc, hj⟩ => h k E ⟨c, ?_, hj⟩,
    fun k _ _ E _ ⟨c, hc, hj⟩ => h k E ⟨c, ?_, hj⟩⟩, fun ⟨hCM, hN⟩ k _ _ E _ ⟨c, hc, hj⟩ => ?_⟩
  · exact (mem_excJ_iff c).2 (Or.inl hc)
  · exact (mem_excJ_iff c).2 (Or.inr hc)
  · rcases (mem_excJ_iff c).1 hc with hc | hc
    · exact hCM k E ⟨c, hc, hj⟩
    · exact hN k E ⟨c, hc, hj⟩

lemma CanLift27ArithNonCM.of_canLift27Arith (h : CanLift27Arith.{u}) :
    CanLift27ArithNonCM.{u} :=
  (canLift27Arith_iff.1 h).2

lemma CanLift27ArithCM.of_canLift27Arith (h : CanLift27Arith.{u}) : CanLift27ArithCM.{u} :=
  (canLift27Arith_iff.1 h).1

end AffOrbicurve
