/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NativeSeparableResidueGroup
import EtaleFundamentalGroups.Inertia.NormalizationAbsoluteResidueClosure
import SchemeTheory.RingTheory.Ramification.NativeAlgebraResidueCoefficient

/-!
# Absolute normalization residue Galois groups

Identifies the literal normalization residue as an algebraic closure of the base residue field
and constructs the restriction isomorphism to its separable residue Galois group.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory SchemeTheory

universe u v w

/-- The existing residue target is precisely the automorphism group of the
two stored literal fields with their constructed coefficient action. -/
theorem normalizationResidueAutomorphisms_eq_fieldObject
    (A : Type u) (Ω : Type w) [CommRing A] [IsLocalRing A]
    [Field Ω] [Algebra A Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal] :
    normalizationResidueAutomorphisms A Ω Q =
      nativeFieldAutomorphisms (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A Ω Q)
        (normalizationResidueFieldAlgebra A Ω Q) :=
  normalizationResidueAutomorphisms_eq_overResidueField A Ω Q

/-- The proved field-object identification retains the literal quotient
automorphism, including its value on every coefficient. -/
theorem normalizationResidueAutomorphisms_fieldObject_apply
    (A : Type u) (Ω : Type w) [CommRing A] [IsLocalRing A]
    [Field Ω] [Algebra A Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]
    (σ : (normalizationResidueAutomorphisms A Ω Q).carrier)
    (z : (normalizationResidueFieldObject A Ω Q).α) :
    nativeFieldResidueActionScalar (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)
        ((eqToIso (normalizationResidueAutomorphisms_eq_fieldObject A Ω Q)).hom.hom'.toFun σ)
        z =
      normalizationResidueActionScalar A Ω Q σ z := by
  have : Q.LiesOver (nativeAlgebraResidueBaseIdeal (normalizationCommAlgCat A Ω) Q) := by
    change Q.LiesOver (Q.under A)
    infer_instance
  let := normalizationResidueFieldAlgebra A Ω Q
  have hring :
      (show (normalizationResidueFieldObject A Ω Q).α ≃ₐ[IsLocalRing.ResidueField A]
          (normalizationResidueFieldObject A Ω Q).α from
        (eqToIso (normalizationResidueAutomorphisms_eq_fieldObject A Ω Q)).hom.hom'.toFun σ
        ).toRingEquiv =
      nativeAlgebraResidueAutomorphismRingEquiv (normalizationCommAlgCat A Ω) Q σ :=
    nativeResidueAutomorphisms_eq_overResidueField_ringEquiv A (normalizationCommAlgCat A Ω).carrier
      (nativeAlgebraResidueBaseIdeal (normalizationCommAlgCat A Ω) Q) Q
      (normalizationResidueBaseIdeal_eq_maximalIdeal A Ω Q) σ
  exact congrArg
    (fun e : (normalizationResidueFieldObject A Ω Q).α ≃+*
      (normalizationResidueFieldObject A Ω Q).α => e.toRingHom.toFun z) hring

/-- The actual Galois group of the relative separable closure of the base
residue field inside the literal normalization quotient. -/
def normalizationResidueSeparableGroup
    (A : Type u) (Ω : Type w) [CommRing A] [IsLocalRing A]
    [CommRing Ω] [Algebra A Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal] : GrpCat.{w} :=
  nativeSeparableResidueGroup (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A Ω Q)
    (normalizationResidueFieldAlgebra A Ω Q)

/-- Once algebraic closedness of the literal quotient is supplied, the
actual integral residue extension and actual restriction equivalence give
the comparison of residue automorphism groups. -/
private def normalizationResidueSeparableIso_of_isAlgClosed
    (A : Type u) (Ω : Type w) [CommRing A] [IsLocalRing A]
    [Field Ω] [Algebra A Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
    [IsAlgClosed (normalizationResidueFieldObject A Ω Q)] :
    normalizationResidueAutomorphisms A Ω Q ≅ normalizationResidueSeparableGroup A Ω Q := by
  have hclosure : letI := normalizationResidueFieldAlgebra A Ω Q
      IsAlgClosure (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A Ω Q) := by
    let := normalizationResidueFieldAlgebra A Ω Q
    exact ⟨inferInstance, normalizationResidueFieldAlgebra_isAlgebraic A Ω Q⟩
  exact eqToIso (normalizationResidueAutomorphisms_eq_fieldObject A Ω Q) ≪≫
    nativeSeparableResidueIso (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A Ω Q)
      (normalizationResidueFieldAlgebra A Ω Q) hclosure

/-- The private closed-residue construction computes the original quotient
action through its actual separable coefficient inclusion. -/
private theorem normalizationResidueSeparableIso_of_isAlgClosed_commutes
    (A : Type u) (Ω : Type w) [CommRing A] [IsLocalRing A]
    [Field Ω] [Algebra A Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]
    [IsAlgClosed (normalizationResidueFieldObject A Ω Q).α]
    (σ : (normalizationResidueAutomorphisms A Ω Q).carrier)
    (z : (nativeSeparableResidueField (IsLocalRing.ResidueField A)
      (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)).α) :
    nativeSeparableResidueActionScalar (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)
        ((normalizationResidueSeparableIso_of_isAlgClosed A Ω Q).hom.hom'.toFun σ) z =
      normalizationResidueActionScalar A Ω Q σ
        (nativeSeparableResidueScalar (IsLocalRing.ResidueField A)
          (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q) z) := by
  have hclosure : let := normalizationResidueFieldAlgebra A Ω Q
      IsAlgClosure (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A Ω Q).α := by
    intro a
    exact ⟨inferInstance, normalizationResidueFieldAlgebra_isAlgebraic A Ω Q⟩
  exact (nativeSeparableResidueIso_commutes (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q) hclosure
    ((eqToIso (normalizationResidueAutomorphisms_eq_fieldObject A Ω Q)).hom.hom'.toFun σ) z).trans
      (normalizationResidueAutomorphisms_fieldObject_apply A Ω Q σ
        (nativeSeparableResidueScalar (IsLocalRing.ResidueField A)
          (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q) z))

/-- The literal quotient residue is an algebraic closure of the actual
base residue field, derived solely from the original absolute DVR data. -/
theorem normalizationAbsoluteResidue_isAlgClosure
    (A : Type u) (K : Type v) (Ω : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal] :
    letI := normalizationResidueFieldAlgebra A Ω Q
    IsAlgClosure (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A Ω Q) := by
  let := normalizationResidueFieldAlgebra A Ω Q
  exact ⟨normalizationAbsoluteResidue_isAlgClosed A K Ω Q,
    normalizationResidueFieldAlgebra_isAlgebraic A Ω Q⟩

/-- Original-input restriction from the actual residue automorphisms to
the actual separable residue Galois group. No residue comparison is assumed. -/
def normalizationAbsoluteResidueIso
    (A : Type u) (K : Type v) (Ω : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal] :
    normalizationResidueAutomorphisms A Ω Q ≅ normalizationResidueSeparableGroup A Ω Q := by
  have : IsAlgClosed (normalizationResidueFieldObject A Ω Q) :=
    normalizationAbsoluteResidue_isAlgClosed A K Ω Q
  exact normalizationResidueSeparableIso_of_isAlgClosed A Ω Q

/-- The public absolute isomorphism has the actual quotient coefficient square.
The separable-field dictionaries remain inside the lower coefficient maps. -/
theorem normalizationAbsoluteResidueIso_commutes
    (A : Type u) (K : Type v) (Ω : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]
    (σ : (normalizationResidueAutomorphisms A Ω Q).carrier)
    (z : (nativeSeparableResidueField (IsLocalRing.ResidueField A)
      (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)).α) :
    nativeSeparableResidueActionScalar (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)
        ((normalizationAbsoluteResidueIso A K Ω Q).hom.hom'.toFun σ) z =
      normalizationResidueActionScalar A Ω Q σ
        (nativeSeparableResidueScalar (IsLocalRing.ResidueField A)
          (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q) z) := by
  have : IsAlgClosed (normalizationResidueFieldObject A Ω Q).α :=
    normalizationAbsoluteResidue_isAlgClosed A K Ω Q
  exact normalizationResidueSeparableIso_of_isAlgClosed_commutes A Ω Q σ z

end EtaleFundamentalGroups.Inertia

end
