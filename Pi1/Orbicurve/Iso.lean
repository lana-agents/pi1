/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Orbicurve.Pullback

/-!
# Isomorphisms of affine orbicurves from ring isomorphisms

* `AffOrbicurve.Iso.ofAlgEquiv`: a `k`-algebra isomorphism of coordinate rings matching the
  stabilizer orders is an isomorphism of affine orbicurves.
* `AffOrbicurve.ramificationIdx_congr`: ramification indices are invariant under compatible
  ring isomorphisms.
* `AffOrbicurve.integralClosureEquiv`: integral closures correspond under compatible ring
  isomorphisms.
-/

@[expose] public section

universe u

open Ideal Polynomial

namespace AffOrbicurve

variable {k : Type u} [Field k]

lemma comap_comap_symm {A B : Type*} [CommRing A] [CommRing B] (ψ : A ≃+* B) (w : Ideal A) :
    (w.comap ψ.symm.toRingHom).comap ψ.toRingHom = w := by
  ext x
  simp only [Ideal.mem_comap]
  change ψ.symm (ψ x) ∈ w ↔ x ∈ w
  rw [RingEquiv.symm_apply_apply]

/-- **An isomorphism of coordinate rings matching the stabilizer orders** is an isomorphism of
affine orbicurves. -/
def Iso.ofAlgEquiv {X Y : AffOrbicurve k} (ψ : X.A ≃ₐ[k] Y.A)
    (hm : ∀ w : Ideal Y.A, w.IsMaximal → Y.mult w = X.mult (w.comap ψ)) : Iso X Y where
  hom :=
    { f := ψ.symm.toAlgHom
      injective := ψ.symm.injective
      isIntegral := RingHom.IsIntegral.of_finite (RingHom.Finite.of_surjective _ ψ.symm.surjective)
      etale := fun w hw => by
        have h1 := @ramificationIdx_ringEquiv Y.A X.A _ _ _ _ ψ.symm.toRingEquiv w hw.isPrime
        have hmax : (w.comap ψ.symm.toRingEquiv.toRingHom).IsMaximal :=
          Ideal.comap_isMaximal_of_surjective _ ψ.symm.surjective
        have h2 := hm _ hmax
        have h3 := comap_comap_symm ψ.toRingEquiv w
        refine (congrArg (· * X.mult w) h1).trans ((one_mul _).trans ?_)
        refine Eq.trans ?_ h2.symm
        exact congrArg X.mult h3.symm }
  inv :=
    { f := ψ.toAlgHom
      injective := ψ.injective
      isIntegral := RingHom.IsIntegral.of_finite (RingHom.Finite.of_surjective _ ψ.surjective)
      etale := fun w hw => by
        have h1 := @ramificationIdx_ringEquiv X.A Y.A _ _ _ _ ψ.toRingEquiv w hw.isPrime
        exact (congrArg (· * Y.mult w) h1).trans ((one_mul _).trans (hm w hw)) }
  hom_inv := AlgHom.ext fun x => ψ.symm_apply_apply x
  inv_hom := AlgHom.ext fun x => ψ.apply_symm_apply x

/-- **Ramification indices are invariant under compatible ring isomorphisms.** -/
lemma ramificationIdx_congr {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [CommRing S'] [IsDedekindDomain R] [IsDedekindDomain S] [IsDedekindDomain R']
    [IsDedekindDomain S'] (f : R →+* S) (f' : R' →+* S') (α : R ≃+* R') (β : S ≃+* S')
    (h : ∀ r, β (f r) = f' (α r)) (hf' : Function.Injective f') (P : Ideal S) [P.IsPrime] :
    (letI := f.toAlgebra; P.ramificationIdx R) =
      (letI := f'.toAlgebra; (P.comap β.symm.toRingHom).ramificationIdx R') := by
  set P' := P.comap β.symm.toRingHom
  haveI : P'.IsPrime := Ideal.comap_isPrime _ _
  haveI : (P'.comap f').IsPrime := Ideal.comap_isPrime _ _
  have t1 := ramificationIdx_comp f β.toRingHom β.injective P'
  have t2 := ramificationIdx_comp α.toRingHom f' hf' P'
  have hc : β.toRingHom.comp f = f'.comp α.toRingHom := RingHom.ext h
  rw [hc, t2, comap_comap_symm] at t1
  have e1 := ramificationIdx_ringEquiv β P'
  have e2 := ramificationIdx_ringEquiv α (P'.comap f')
  rw [e1, e2, one_mul, mul_one] at t1
  exact t1.symm

section IntegralClosure

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S]
  [Algebra R' S'] (α : R ≃+* R') (β : S ≃+* S')
  (h : ∀ r, β (algebraMap R S r) = algebraMap R' S' (α r))

include h in
lemma isIntegral_map_equiv {x : S} (hx : IsIntegral R x) : IsIntegral R' (β x) := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map α.toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hc : (algebraMap R' S').comp α.toRingHom = β.toRingHom.comp (algebraMap R S) :=
    RingHom.ext fun r => (h r).symm
  rw [hc]
  have := Polynomial.hom_eval₂ p (algebraMap R S) β.toRingHom x
  rw [hpx, map_zero] at this
  exact this.symm

include h in
lemma isIntegral_map_equiv_iff {x : S} : IsIntegral R' (β x) ↔ IsIntegral R x := by
  refine ⟨fun hx => ?_, isIntegral_map_equiv α β h⟩
  have h' : ∀ r', β.symm (algebraMap R' S' r') = algebraMap R S (α.symm r') := by
    intro r'
    apply β.injective
    rw [RingEquiv.apply_symm_apply, h, RingEquiv.apply_symm_apply]
  have := isIntegral_map_equiv α.symm β.symm h' hx
  rwa [RingEquiv.symm_apply_apply] at this

/-- **Integral closures correspond under compatible ring isomorphisms.** -/
def integralClosureEquiv : integralClosure R S ≃+* integralClosure R' S' where
  toFun x := ⟨β x, isIntegral_map_equiv α β h x.2⟩
  invFun y := ⟨β.symm y, by
    have : IsIntegral R' (β (β.symm y)) := by rw [RingEquiv.apply_symm_apply]; exact y.2
    exact (isIntegral_map_equiv_iff α β h).mp this⟩
  left_inv x := Subtype.ext (β.symm_apply_apply x)
  right_inv y := Subtype.ext (β.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul β (x : S) y)
  map_add' x y := Subtype.ext (map_add β (x : S) y)

@[simp] lemma coe_integralClosureEquiv (x : integralClosure R S) :
    ((integralClosureEquiv α β h x : integralClosure R' S') : S') = β x := rfl

end IntegralClosure

end AffOrbicurve
