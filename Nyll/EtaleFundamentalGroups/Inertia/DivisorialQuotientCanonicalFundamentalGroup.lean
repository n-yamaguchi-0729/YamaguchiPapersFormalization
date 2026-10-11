/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFundamentalGroupConjugacy
import Nyll.EtaleFundamentalGroups.Inertia.DivisorialQuotientFundamentalGroup

/-!
# Divisorial inertia from the canonical field fundamental-group map

The finite quotient attached to the inertia fixed field factors through the
usual fundamental-group map of spectra after transporting the equality of
the two base points.  The comparison of fiber functors contributes one
explicit inner conjugation and no additional hypothesis.
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

section

variable (P : Ideal A) [P.IsPrime]
variable (Q : Ideal (integralClosure A L))

local notation "F" =>
  localizedNormalizationInertiaField (K := K) (L := L) P Q
local notation "Omega" => SeparableClosure L

/-- The finite quotient obtained directly from the canonical fundamental-group
map, with only the equality of the two geometric base points transported. -/
noncomputable def
    localizedNormalizationInertiaFieldCanonicalUnconjugatedHom :
    let : CommRing F := (inferInstance : Field F).toCommRing
    let : CommSemiring F := (inferInstance : Field F).toSemifield.toCommSemiring
    let : CommRing Omega := (inferInstance : Field Omega).toCommRing
    let : CommSemiring Omega := (inferInstance : Field Omega).toSemifield.toCommSemiring
    let : Algebra F Omega :=
      ((algebraMap L Omega).comp (algebraMap F L)).toAlgebra
    Aut (fib F Omega) →* Gal(L/K) := by
  intro hFCommRing hFCommSemiring hOmegaCommRing hOmegaCommSemiring hFOmega
  let hKOmega : Algebra K Omega :=
    ((algebraMap L Omega).comp (algebraMap K L)).toAlgebra
  let : @IsScalarTower K F Omega
      (@Algebra.toSMul K F _ _ inferInstance)
      (@Algebra.toSMul F Omega _ _ inferInstance)
      (@Algebra.toSMul K Omega _ _ inferInstance) :=
    IsScalarTower.of_algebraMap_eq' (R := K) (S := F) (A := Omega) rfl
  let : IsScalarTower K L Omega := IsScalarTower.of_algebraMap_eq' rfl
  let : IsSepClosure K Omega := by
    exact ⟨IsSepClosure.sep_closed L, Algebra.IsSeparable.trans K L Omega⟩
  exact fieldCanonicalUnconjugatedHom K F L Omega

/-- The image in the finite Galois group of the explicit comparison
automorphism between the two field-fiber comparisons. -/
noncomputable def
    localizedNormalizationInertiaFieldCanonicalConjugatingElement :
    Gal(L/K) := by
  let : CommRing F := (inferInstance : Field F).toCommRing
  let : CommSemiring F := (inferInstance : Field F).toSemifield.toCommSemiring
  let : CommRing Omega := (inferInstance : Field Omega).toCommRing
  let : CommSemiring Omega := (inferInstance : Field Omega).toSemifield.toCommSemiring
  let hFOmega : Algebra F Omega :=
    ((algebraMap L Omega).comp (algebraMap F L)).toAlgebra
  let hKOmega : Algebra K Omega :=
    ((algebraMap L Omega).comp (algebraMap K L)).toAlgebra
  let : @IsScalarTower K F Omega
      (@Algebra.toSMul K F _ _ inferInstance)
      (@Algebra.toSMul F Omega _ _ inferInstance)
      (@Algebra.toSMul K Omega _ _ inferInstance) :=
    IsScalarTower.of_algebraMap_eq' (R := K) (S := F) (A := Omega) rfl
  exact finiteGaloisSeparableClosureQuotientHom (K := K) (L := L)
    (fieldFundamentalGroupComparisonAut K F Omega)

/-- The canonical quotient with the explicit comparison conjugation included. -/
noncomputable def localizedNormalizationInertiaFieldCanonicalHom
    :
    let : CommRing F := (inferInstance : Field F).toCommRing
    let : CommSemiring F := (inferInstance : Field F).toSemifield.toCommSemiring
    let : CommRing Omega := (inferInstance : Field Omega).toCommRing
    let : CommSemiring Omega := (inferInstance : Field Omega).toSemifield.toCommSemiring
    let : Algebra F Omega :=
      ((algebraMap L Omega).comp (algebraMap F L)).toAlgebra
    Aut (fib F Omega) →* Gal(L/K) := by
  intro hFCommRing hFCommSemiring hOmegaCommRing hOmegaCommSemiring hFOmega
  exact (MulAut.conj
      (localizedNormalizationInertiaFieldCanonicalConjugatingElement
        (K := K) (L := L) P Q)).toMonoidHom.comp
    (localizedNormalizationInertiaFieldCanonicalUnconjugatedHom
      (K := K) (L := L) P Q)

/-- The inertia fixed-field quotient is exactly the canonical
fundamental-group quotient with its explicit inner conjugation. -/
theorem localizedNormalizationInertiaFieldFundamentalGroupHom_eq_canonical
    :
    localizedNormalizationInertiaFieldFundamentalGroupHom
        (K := K) (L := L) P Q =
      localizedNormalizationInertiaFieldCanonicalHom
        (K := K) (L := L) P Q := by
  let : CommRing F := (inferInstance : Field F).toCommRing
  let : CommSemiring F := (inferInstance : Field F).toSemifield.toCommSemiring
  let : CommRing Omega := (inferInstance : Field Omega).toCommRing
  let : CommSemiring Omega := (inferInstance : Field Omega).toSemifield.toCommSemiring
  let hFOmega : Algebra F Omega :=
    ((algebraMap L Omega).comp (algebraMap F L)).toAlgebra
  let hKOmega : Algebra K Omega :=
    ((algebraMap L Omega).comp (algebraMap K L)).toAlgebra
  let : @IsScalarTower K F Omega
      (@Algebra.toSMul K F _ _ inferInstance)
      (@Algebra.toSMul F Omega _ _ inferInstance)
      (@Algebra.toSMul K Omega _ _ inferInstance) :=
    IsScalarTower.of_algebraMap_eq' (R := K) (S := F) (A := Omega) rfl
  apply MonoidHom.ext
  intro a
  have hfactor := DFunLike.congr_fun
    (localizedNormalizationInertiaFieldFundamentalGroupHom_eq_comp
      (K := K) (L := L) P Q) a
  have hconj :=
    fieldFundamentalGroupHom_eq_conj_fundamentalGroupHom K F Omega a
  calc
    _ = finiteGaloisSeparableClosureQuotientHom (K := K) (L := L)
        (fieldFundamentalGroupHom K F Omega inferInstance a) := hfactor
    _ = finiteGaloisSeparableClosureQuotientHom (K := K) (L := L)
        (MulAut.conj (fieldFundamentalGroupComparisonAut K F Omega)
          ((fieldBasePointFiberIso K F Omega).conjAut
            (fundamentalGroupHom (ξ K F) (ξ F Omega) a))) :=
      congrArg (finiteGaloisSeparableClosureQuotientHom (K := K) (L := L)) hconj
    _ = _ := by
      change finiteGaloisSeparableClosureQuotientHom (K := K) (L := L)
          (MulAut.conj (fieldFundamentalGroupComparisonAut K F Omega)
            ((fieldBasePointFiberIso K F Omega).conjAut
              (fundamentalGroupHom (ξ K F) (ξ F Omega) a))) =
        MulAut.conj
          (finiteGaloisSeparableClosureQuotientHom (K := K) (L := L)
            (fieldFundamentalGroupComparisonAut K F Omega))
          (finiteGaloisSeparableClosureQuotientHom (K := K) (L := L)
            ((fieldBasePointFiberIso K F Omega).conjAut
              (fundamentalGroupHom (ξ K F) (ξ F Omega) a)))
      simp only [MulAut.conj_apply, map_mul, map_inv]

/-- The corrected canonical quotient has image exactly ideal inertia. -/
theorem localizedNormalizationInertiaFieldCanonicalHom_range
    :
    (localizedNormalizationInertiaFieldCanonicalHom
      (K := K) (L := L) P Q).range =
        localizedNormalizationInertia (K := K) (L := L) P Q := by
  rw [← localizedNormalizationInertiaFieldFundamentalGroupHom_eq_canonical,
    localizedNormalizationInertiaFieldFundamentalGroupHom_range]

/-- Conjugating the image of the uncorrected canonical composite by the
explicit finite comparison element gives exactly ideal inertia. -/
theorem localizedNormalizationInertiaFieldCanonicalUnconjugatedHom_range_map
    :
    (localizedNormalizationInertiaFieldCanonicalUnconjugatedHom
        (K := K) (L := L) P Q).range.map
      (MulAut.conj
        (localizedNormalizationInertiaFieldCanonicalConjugatingElement
          (K := K) (L := L) P Q)).toMonoidHom =
      localizedNormalizationInertia (K := K) (L := L) P Q := by
  rw [← MonoidHom.range_comp]
  exact localizedNormalizationInertiaFieldCanonicalHom_range
    (K := K) (L := L) P Q

end

end EtaleFundamentalGroups.Inertia

end
