/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.Normalization.Field

/-!
# Field sources for divisorial inertia in finite Galois quotients

For a normalization prime in a finite Galois extension, ideal inertia fixes
an actual intermediate field.  The Galois group over that fixed field maps
to the original finite Galois group by scalar restriction, and its image is
exactly the normalization-prime inertia subgroup.

This is the finite field-local source needed before comparing with the
fundamental group of the spectrum of that fixed field.  No strict
henselization, Nagata, finite-type, height, or regularity hypothesis is used.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe uA uK uL uOmega

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [FiniteDimensional K L] [_root_.IsGalois K L]

/-- The subgroup of `Gal(L/K)` fixing the normalization-prime inertia field
is exactly normalization-prime inertia. -/
theorem localizedNormalizationInertiaField_fixingSubgroup_eq
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    (localizedNormalizationInertiaField (K := K) (L := L) P Q).fixingSubgroup =
      localizedNormalizationInertia (K := K) (L := L) P Q := by
  exact HilbertRamification.Dedekind.fixedFieldOfSubgroup_fixingSubgroup_eq
    (K := K) (L := L) Gal(L/K)
    (localizedNormalizationInertia (K := K) (L := L) P Q)

/-- The finite field-local monodromy group over the inertia fixed field is
canonically the normalization-prime inertia subgroup. -/
noncomputable def localizedNormalizationInertiaFieldGalMulEquiv
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
    Gal(L/F) ≃*
      localizedNormalizationInertia (K := K) (L := L) P Q := by
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  exact F.fixingSubgroupEquiv.symm.trans
    (MulEquiv.subgroupCongr
      (localizedNormalizationInertiaField_fixingSubgroup_eq
        (K := K) (L := L) P Q))

/-- Scalar restriction from the finite Galois group over the inertia fixed
field to `Gal(L/K)`, with its target expressed through normalization data. -/
noncomputable def localizedNormalizationInertiaFieldRestrictionHom
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
    Gal(L/F) →* Gal(L/K) := by
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  exact
    (localizedNormalizationInertia (K := K) (L := L) P Q).subtype.comp
      (localizedNormalizationInertiaFieldGalMulEquiv
        (K := K) (L := L) P Q).toMonoidHom

/-- The field-source homomorphism is the ordinary restriction of scalars. -/
@[simp]
theorem localizedNormalizationInertiaFieldRestrictionHom_apply
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L))
    (sigma :
      let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
      Gal(L/F)) :
    localizedNormalizationInertiaFieldRestrictionHom
        (K := K) (L := L) P Q sigma =
      sigma.restrictScalars K := by
  rfl

/-- The actual image of the finite field-local monodromy source in
`Gal(L/K)` is exactly normalization-prime ideal inertia. -/
theorem localizedNormalizationInertiaFieldRestrictionHom_range
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    (localizedNormalizationInertiaFieldRestrictionHom
      (K := K) (L := L) P Q).range =
        localizedNormalizationInertia (K := K) (L := L) P Q := by
  rw [localizedNormalizationInertiaFieldRestrictionHom,
    MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr
      (localizedNormalizationInertiaFieldGalMulEquiv
        (K := K) (L := L) P Q).surjective,
    ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

/-- Restriction from an absolute Galois group over the inertia fixed field,
followed by scalar restriction to the original finite Galois group.  The
finite extension `L/F` is not supplied independently: `F` is the fixed field
of normalization-prime inertia. -/
noncomputable def localizedNormalizationInertiaFieldAbsoluteRestrictionHom
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L))
    (Omega : Type uOmega) [Field Omega]
    [hFOmega : Algebra
      (localizedNormalizationInertiaField (K := K) (L := L) P Q) Omega]
    [hLOmega : Algebra L Omega]
    (hcompat :
      algebraMap
          (localizedNormalizationInertiaField (K := K) (L := L) P Q) Omega =
        (algebraMap L Omega).comp
          (algebraMap
            (localizedNormalizationInertiaField (K := K) (L := L) P Q) L)) :
    Gal(Omega/
      localizedNormalizationInertiaField (K := K) (L := L) P Q) →*
        Gal(L/K) := by
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  letI : SMul F Omega := hFOmega.toSMul
  letI : IsScalarTower F L Omega :=
    IsScalarTower.of_algebraMap_eq' hcompat
  exact
    (localizedNormalizationInertiaFieldRestrictionHom
      (K := K) (L := L) P Q).comp
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := Omega) L)

/-- The absolute field-source map first restricts an automorphism to `L` and
then forgets from the inertia fixed field down to `K`. -/
@[simp]
theorem localizedNormalizationInertiaFieldAbsoluteRestrictionHom_apply
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L))
    (Omega : Type uOmega) [Field Omega]
    [hFOmega : Algebra
      (localizedNormalizationInertiaField (K := K) (L := L) P Q) Omega]
    [hLOmega : Algebra L Omega]
    (hcompat :
      algebraMap
          (localizedNormalizationInertiaField (K := K) (L := L) P Q) Omega =
        (algebraMap L Omega).comp
          (algebraMap
            (localizedNormalizationInertiaField (K := K) (L := L) P Q) L))
    (sigma :
      Gal(Omega/localizedNormalizationInertiaField (K := K) (L := L) P Q)) :
    localizedNormalizationInertiaFieldAbsoluteRestrictionHom
        (K := K) (L := L) P Q Omega hcompat sigma =
      (let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
       letI : SMul F Omega := hFOmega.toSMul
       letI : IsScalarTower F L Omega :=
         IsScalarTower.of_algebraMap_eq' hcompat
       AlgEquiv.restrictNormalHom (F := F) (K₁ := Omega) L sigma).restrictScalars K := by
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  let : SMul F Omega := hFOmega.toSMul
  let : IsScalarTower F L Omega :=
    IsScalarTower.of_algebraMap_eq' hcompat
  rfl

/-- For any separable closure containing `L`, the image of its absolute
Galois group over the inertia fixed field in `Gal(L/K)` is exactly the
normalization-prime inertia subgroup. -/
theorem localizedNormalizationInertiaFieldAbsoluteRestrictionHom_range
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L))
    (Omega : Type uOmega) [Field Omega]
    [hFOmega : Algebra
      (localizedNormalizationInertiaField (K := K) (L := L) P Q) Omega]
    [hLOmega : Algebra L Omega]
    (hcompat :
      algebraMap
          (localizedNormalizationInertiaField (K := K) (L := L) P Q) Omega =
        (algebraMap L Omega).comp
          (algebraMap
            (localizedNormalizationInertiaField (K := K) (L := L) P Q) L))
    [IsSepClosure
      (localizedNormalizationInertiaField (K := K) (L := L) P Q) Omega] :
    (localizedNormalizationInertiaFieldAbsoluteRestrictionHom
        (K := K) (L := L) P Q Omega hcompat).range =
      localizedNormalizationInertia (K := K) (L := L) P Q := by
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  let : SMul F Omega := hFOmega.toSMul
  let : IsScalarTower F L Omega :=
    IsScalarTower.of_algebraMap_eq' hcompat
  rw [localizedNormalizationInertiaFieldAbsoluteRestrictionHom,
    MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr
      (AlgEquiv.restrictNormalHom_surjective
        (F := F) (K₁ := L) (E := Omega)),
    ← MonoidHom.range_eq_map,
    localizedNormalizationInertiaFieldRestrictionHom_range]

/-- The canonical absolute source obtained by taking the separable closure of
`L`.  Its algebra structure over the inertia fixed field is the actual
composite `F → L → SeparableClosure L`, so no separately chosen closure or
compatibility datum remains in the public interface. -/
noncomputable def
    localizedNormalizationInertiaFieldSeparableClosureRestrictionHom
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
    let Omega := SeparableClosure L
    letI : Algebra F Omega :=
      ((algebraMap L Omega).comp (algebraMap F L)).toAlgebra
    Gal(Omega/F) →* Gal(L/K) := by
  dsimp only
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  let Omega := SeparableClosure L
  letI : Algebra F Omega :=
    ((algebraMap L Omega).comp (algebraMap F L)).toAlgebra
  exact localizedNormalizationInertiaFieldAbsoluteRestrictionHom
    (K := K) (L := L) P Q Omega rfl

/-- The canonical separable-closure source has image exactly the selected
normalization-prime inertia subgroup. -/
theorem
    localizedNormalizationInertiaFieldSeparableClosureRestrictionHom_range
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
    let Omega := SeparableClosure L
    letI : Algebra F Omega :=
      ((algebraMap L Omega).comp (algebraMap F L)).toAlgebra
    (localizedNormalizationInertiaFieldSeparableClosureRestrictionHom
      (K := K) (L := L) P Q).range =
        localizedNormalizationInertia (K := K) (L := L) P Q := by
  dsimp only
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  let Omega := SeparableClosure L
  let hFOmega : Algebra F Omega :=
    ((algebraMap L Omega).comp (algebraMap F L)).toAlgebra
  let : SMul F Omega := hFOmega.toSMul
  let : IsScalarTower F L Omega :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsSepClosure F Omega :=
    ⟨IsSepClosure.sep_closed L,
      Algebra.IsSeparable.trans F L Omega⟩
  exact localizedNormalizationInertiaFieldAbsoluteRestrictionHom_range
    (K := K) (L := L) P Q Omega rfl

end EtaleFundamentalGroups.Inertia
