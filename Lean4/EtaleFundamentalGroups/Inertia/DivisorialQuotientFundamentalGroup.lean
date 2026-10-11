/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.DivisorialQuotientFieldSource
import EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality
import EtaleFundamentalGroups.Inertia.FieldPointedQuotient

/-!
# Divisorial inertia as a finite quotient of a field fundamental group

The inertia fixed field constructed from a normalization prime has an actual
absolute Galois group.  Via the geometric fiber functor of its spectrum, its
canonical finite quotient has image exactly the selected ideal inertia.
-/

noncomputable section

universe uA u

open CategoryTheory

namespace EtaleFundamentalGroups.Inertia

open AlgebraicGeometry.FiniteEtale

variable {A : Type uA} {K L : Type u}
variable [CommRing A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [FiniteDimensional K L] [_root_.IsGalois K L]

/-- A separable closure remains one over a separable subfield when the
algebra map to the closure is the actual composite.  The tower witness is
passed explicitly so an intermediate-field action cannot compete with the
action stored in the chosen composite algebra. -/
private theorem composite_isSepClosure
    (F E Omega : Type u)
    [Field F] [Field E] [Field Omega]
    [Algebra F E] [Algebra E Omega] [hFOmega : Algebra F Omega]
    [Algebra.IsSeparable F E] [IsSepClosure E Omega]
    (hcomp : algebraMap F Omega =
      (algebraMap E Omega).comp (algebraMap F E)) :
    IsSepClosure F Omega := by
  let : IsScalarTower F E Omega := IsScalarTower.of_algebraMap_eq' hcomp
  exact ⟨IsSepClosure.sep_closed E, Algebra.IsSeparable.trans F E Omega⟩

/-- The finite Galois quotient of the geometric-fiber fundamental group of
`Spec K`, using the separable closure of `L` as geometric point. -/
noncomputable def finiteGaloisSeparableClosureQuotientHom :
    let Omega := SeparableClosure L
    let : CommRing Omega := (inferInstance : Field Omega).toCommRing
    let : CommSemiring Omega := (inferInstance : Field Omega).toSemifield.toCommSemiring
    let : Algebra K Omega :=
      ((algebraMap L Omega).comp (algebraMap K L)).toAlgebra
    Aut (fib K Omega) →* Gal(L/K) := by
  intro Omega hOmegaCommRing hOmegaCommSemiring hKOmega
  let : IsScalarTower K L Omega :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsSepClosure K Omega :=
    composite_isSepClosure K L Omega rfl
  exact fieldFiniteGaloisRestrictionHom K L Omega

/-- The finite quotient of the fundamental group of the inertia fixed field
obtained by restricting its absolute Galois group to `L` and then to `K`. -/
noncomputable def localizedNormalizationInertiaFieldFundamentalGroupHom
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
    let Omega := SeparableClosure L
    let : CommRing F := (inferInstance : Field F).toCommRing
    let : CommSemiring F := (inferInstance : Field F).toSemifield.toCommSemiring
    let : CommRing Omega := (inferInstance : Field Omega).toCommRing
    let : CommSemiring Omega := (inferInstance : Field Omega).toSemifield.toCommSemiring
    let : Algebra F Omega :=
      ((algebraMap L Omega).comp (algebraMap F L)).toAlgebra
    Aut (fib F Omega) →* Gal(L/K) := by
  intro F Omega hFCommRing hFCommSemiring hOmegaCommRing hOmegaCommSemiring hFOmega
  let : IsSepClosure F Omega :=
    composite_isSepClosure F L Omega rfl
  exact
    (localizedNormalizationInertiaFieldSeparableClosureRestrictionHom
      (K := K) (L := L) P Q).comp
        (absoluteGaloisToFiberAutMulEquiv F Omega inferInstance).symm.toMonoidHom

/-- The geometric-fiber quotient of the inertia fixed field has image
exactly normalization-prime ideal inertia. -/
theorem localizedNormalizationInertiaFieldFundamentalGroupHom_range
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
    let Omega := SeparableClosure L
    let : CommRing F := (inferInstance : Field F).toCommRing
    let : CommSemiring F := (inferInstance : Field F).toSemifield.toCommSemiring
    let : CommRing Omega := (inferInstance : Field Omega).toCommRing
    let : CommSemiring Omega := (inferInstance : Field Omega).toSemifield.toCommSemiring
    let : Algebra F Omega :=
      ((algebraMap L Omega).comp (algebraMap F L)).toAlgebra
    (localizedNormalizationInertiaFieldFundamentalGroupHom
      (K := K) (L := L) P Q).range =
        localizedNormalizationInertia (K := K) (L := L) P Q := by
  intro F Omega hFCommRing hFCommSemiring hOmegaCommRing hOmegaCommSemiring hFOmega
  let : IsSepClosure F Omega :=
    composite_isSepClosure F L Omega rfl
  change ((localizedNormalizationInertiaFieldSeparableClosureRestrictionHom
      (K := K) (L := L) P Q).comp
        (absoluteGaloisToFiberAutMulEquiv F Omega
          inferInstance).symm.toMonoidHom).range = _
  rw [MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr
      (absoluteGaloisToFiberAutMulEquiv F Omega inferInstance).symm.surjective,
    ← MonoidHom.range_eq_map,
    localizedNormalizationInertiaFieldSeparableClosureRestrictionHom_range]

/-- The quotient from the inertia fixed field factors through the
fundamental-group homomorphism induced by `Spec F ⟶ Spec K` and the usual
finite Galois quotient over `K`. -/
theorem localizedNormalizationInertiaFieldFundamentalGroupHom_eq_comp
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
    let Omega := SeparableClosure L
    let : CommRing F := (inferInstance : Field F).toCommRing
    let : CommSemiring F := (inferInstance : Field F).toSemifield.toCommSemiring
    let : CommRing Omega := (inferInstance : Field Omega).toCommRing
    let : CommSemiring Omega := (inferInstance : Field Omega).toSemifield.toCommSemiring
    let hKOmega : Algebra K Omega :=
      ((algebraMap L Omega).comp (algebraMap K L)).toAlgebra
    let hFOmega : Algebra F Omega :=
      ((algebraMap L Omega).comp (algebraMap F L)).toAlgebra
    let : @IsScalarTower K F Omega
      (@Algebra.toSMul K F _ _ inferInstance)
      (@Algebra.toSMul F Omega _ _ hFOmega)
      (@Algebra.toSMul K Omega _ _ hKOmega) :=
      IsScalarTower.of_algebraMap_eq' (R := K) (S := F) (A := Omega) rfl
    localizedNormalizationInertiaFieldFundamentalGroupHom
        (K := K) (L := L) P Q =
      (finiteGaloisSeparableClosureQuotientHom (K := K) (L := L)).comp
        (fieldFundamentalGroupHom K F Omega inferInstance).toMonoidHom := by
  intro F Omega hFCommRing hFCommSemiring hOmegaCommRing hOmegaCommSemiring hKOmega hFOmega hKFOmega
  apply MonoidHom.ext
  intro a
  let eF : Gal(Omega/F) ≃* Aut (fib F Omega) := by
    let : IsSepClosure F Omega :=
      composite_isSepClosure F L Omega rfl
    exact absoluteGaloisToFiberAutMulEquiv F Omega inferInstance
  let eK : Gal(Omega/K) ≃* Aut (fib K Omega) := by
    let : IsSepClosure K Omega :=
      composite_isSepClosure K L Omega rfl
    exact absoluteGaloisToFiberAutMulEquiv K Omega inferInstance
  let sigma : Gal(Omega/F) := eF.symm a
  have hfield :
      fieldFundamentalGroupHom K F Omega inferInstance (eF sigma) =
        eK (sigma.restrictScalars K) := by
    let : IsSepClosure K Omega :=
      composite_isSepClosure K L Omega rfl
    let : IsSepClosure F Omega :=
      composite_isSepClosure F L Omega rfl
    simpa only [eF, eK] using
      (fieldFundamentalGroupHom_toAutMulEquiv K F Omega sigma)
  have hfield_a :
      fieldFundamentalGroupHom K F Omega inferInstance a =
        eK (sigma.restrictScalars K) := by
    simpa only [sigma, eF, MulEquiv.apply_symm_apply] using hfield
  let : IsScalarTower K L Omega :=
    IsScalarTower.of_algebraMap_eq' rfl
  change
    localizedNormalizationInertiaFieldSeparableClosureRestrictionHom
        (K := K) (L := L) P Q (eF.symm a) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L
        (eK.symm (fieldFundamentalGroupHom K F Omega inferInstance a))
  rw [hfield_a, MulEquiv.symm_apply_apply]
  ext x
  rfl

end EtaleFundamentalGroups.Inertia

end
