/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.RingHom.Etale

/-!
# Transporting integral closure across an equivalent base ring

An equivalence of base rings does not change which elements of a common
ambient ring are integral.  This file packages that observation as an
algebra equivalence between the two literal `integralClosure` subrings and
uses it to transport etaleness.  A second version simultaneously transports
the ambient ring, which is the form needed when two canonical completed
fraction fields have first been identified.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uS uA uB

section CommonAmbient

variable {R : Type uR} {S : Type uS} {A : Type uA}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R A] [Algebra S A]

/-- The `R`-algebra structure on the `S`-integral closure obtained by
restricting scalars along a base-ring equivalence. -/
@[reducible]
noncomputable def integralClosureBaseRingAlgebra (e : R ≃+* S) :
    Algebra R (integralClosure S A) :=
  ((algebraMap S (integralClosure S A)).comp e.toRingHom).toAlgebra

/-- Equivalent base rings define canonically equivalent integral closures
inside a common ambient ring, provided their maps to the ambient ring agree.

The target is read as an `R`-algebra through
`integralClosureBaseRingAlgebra`. -/
noncomputable def integralClosureBaseRingAlgEquiv
    (e : R ≃+* S)
    (h : (algebraMap S A).comp e.toRingHom = algebraMap R A) :
    letI : Algebra R (integralClosure S A) :=
      integralClosureBaseRingAlgebra e
    integralClosure R A ≃ₐ[R] integralClosure S A := by
  letI : Algebra R (integralClosure S A) :=
    integralClosureBaseRingAlgebra e
  let f : integralClosure R A →+* integralClosure S A :=
    { toFun := fun x ↦
        ⟨x.1, (e.isIntegral_iff h x.1).mp x.2⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  let g : integralClosure S A →+* integralClosure R A :=
    { toFun := fun x ↦
        ⟨x.1, (e.isIntegral_iff h x.1).mpr x.2⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  let er : integralClosure R A ≃+* integralClosure S A :=
    { toFun := f
      invFun := g
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := f.map_add
      map_mul' := f.map_mul }
  exact AlgEquiv.ofRingEquiv (f := er) fun r ↦ by
    apply Subtype.ext
    exact (congrArg (fun k : R →+* A ↦ k r) h).symm

/-- Etaleness of a normalization is invariant under replacing its base ring
by an equivalent ring with the same map to the ambient ring. -/
theorem integralClosure_etale_of_baseRingEquiv
    (e : R ≃+* S)
    (h : (algebraMap S A).comp e.toRingHom = algebraMap R A)
    (hEtale : Algebra.Etale S (integralClosure S A)) :
    Algebra.Etale R (integralClosure R A) := by
  let : Algebra R (integralClosure S A) :=
    integralClosureBaseRingAlgebra e
  let : Algebra.Etale S (integralClosure S A) := hEtale
  let : Algebra R S := e.toRingHom.toAlgebra
  let eAlg : R ≃ₐ[R] S :=
    AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl
  let : Algebra.Etale R S := Algebra.Etale.of_equiv eAlg
  let : IsScalarTower R S (integralClosure S A) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra.Etale R (integralClosure S A) :=
    Algebra.Etale.comp R S (integralClosure S A)
  exact Algebra.Etale.of_equiv
    (integralClosureBaseRingAlgEquiv e h).symm

end CommonAmbient

section VaryingAmbient

variable {R : Type uR} {S : Type uS}
variable {A : Type uA} {B : Type uB}
variable [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra S B]

/-- Simultaneously changing an equivalent base ring and an equivalent
ambient ring gives an equivalence of the corresponding normalizations.

Compatibility is required only for the two concrete structure maps.  The
intermediate `R`-algebra structures are constructed internally. -/
noncomputable def integralClosureAlgEquivOfBaseAndAmbientEquiv
    (eBase : R ≃+* S) (eAmbient : A ≃+* B)
    (h : eAmbient.toRingHom.comp (algebraMap R A) =
      (algebraMap S B).comp eBase.toRingHom) :
    letI : Algebra R (integralClosure S B) :=
      integralClosureBaseRingAlgebra eBase
    integralClosure R A ≃ₐ[R] integralClosure S B := by
  letI : Algebra R B :=
    ((algebraMap S B).comp eBase.toRingHom).toAlgebra
  let eAmbientR : A ≃ₐ[R] B :=
    AlgEquiv.ofRingEquiv (f := eAmbient) fun r ↦ by
      exact congrArg (fun k : R →+* B ↦ k r) h
  letI : Algebra R (integralClosure S B) :=
    integralClosureBaseRingAlgebra eBase
  have hBase :
      (algebraMap S B).comp eBase.toRingHom = algebraMap R B := rfl
  exact eAmbientR.mapIntegralClosure |>.trans
    (integralClosureBaseRingAlgEquiv eBase hBase)

/-- Etaleness of a normalization is invariant under simultaneous compatible
equivalences of its base and ambient rings. -/
theorem integralClosure_etale_of_baseAndAmbientEquiv
    (eBase : R ≃+* S) (eAmbient : A ≃+* B)
    (h : eAmbient.toRingHom.comp (algebraMap R A) =
      (algebraMap S B).comp eBase.toRingHom)
    (hEtale : Algebra.Etale S (integralClosure S B)) :
    Algebra.Etale R (integralClosure R A) := by
  let : Algebra R B :=
    ((algebraMap S B).comp eBase.toRingHom).toAlgebra
  let : Algebra R (integralClosure S B) :=
    integralClosureBaseRingAlgebra eBase
  let : Algebra.Etale S (integralClosure S B) := hEtale
  let : Algebra R S := eBase.toRingHom.toAlgebra
  let eBaseAlg : R ≃ₐ[R] S :=
    AlgEquiv.ofRingEquiv (f := eBase) fun _ ↦ rfl
  let : Algebra.Etale R S := Algebra.Etale.of_equiv eBaseAlg
  let : IsScalarTower R S (integralClosure S B) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra.Etale R (integralClosure S B) :=
    Algebra.Etale.comp R S (integralClosure S B)
  exact Algebra.Etale.of_equiv
    (integralClosureAlgEquivOfBaseAndAmbientEquiv
      eBase eAmbient h).symm

end VaryingAmbient

end EtaleFundamentalGroups

end
