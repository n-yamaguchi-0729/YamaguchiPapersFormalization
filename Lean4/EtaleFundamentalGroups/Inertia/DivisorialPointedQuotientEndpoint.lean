/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.FieldCoverQuotient
import EtaleFundamentalGroups.GeometricFiber.FieldFundamentalGroupConjugacy
import EtaleFundamentalGroups.Inertia.DivisorialQuotientCanonicalFundamentalGroup
import EtaleFundamentalGroups.Inertia.DivisorialStrictHenselian
import EtaleFundamentalGroups.Inertia.DivisorialPointedCoverHom
import EtaleFundamentalGroups.Inertia.FieldPointedQuotient
import ProCGroups.Boundary.CyclotomicInversion

/-!
# Divisorial pointed quotient endpoint

The actual pointed quotient of the finite field cover along the inertia
fixed field agrees with the canonical unconjugated divisorial quotient after
transporting the deck group back to the finite Galois group.  Its transported
range is ideal inertia, so primewise coprimality forces that inertia to vanish.
-/

noncomputable section


universe uA u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

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

local notation "IField" =>
  localizedNormalizationInertiaField (K := K) (L := L) P Q
local notation "Omega" => SeparableClosure L

/-- The actual pointed quotient along the inertia-field spectrum is the
canonical divisorial fundamental-group quotient before its explicit
comparison conjugation. -/
theorem localizedNormalizationInertiaFieldPointedQuotientOfMorphism_eq_canonicalUnconjugated :
    (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L).symm.toMonoidHom.comp
        (localizedNormalizationInertiaFieldPointedQuotientHom (K := K) (L := L) P Q) =
      localizedNormalizationInertiaFieldCanonicalUnconjugatedHom
        (K := K) (L := L) P Q := by
  let : CommRing IField := (inferInstance : Field IField).toCommRing
  let : CommSemiring IField := (inferInstance : Field IField).toSemifield.toCommSemiring
  let : CommRing Omega := (inferInstance : Field Omega).toCommRing
  let : CommSemiring Omega := (inferInstance : Field Omega).toSemifield.toCommSemiring
  let : Algebra K Omega :=
    ((algebraMap L Omega).comp (algebraMap K L)).toAlgebra
  let : Algebra IField Omega :=
    ((algebraMap L Omega).comp (algebraMap IField L)).toAlgebra
  let : IsScalarTower K L Omega := IsScalarTower.of_algebraMap_eq' rfl
  let : @IsScalarTower K IField Omega
      (@Algebra.toSMul K IField _ _ inferInstance)
      (@Algebra.toSMul IField Omega _ _ inferInstance)
      (@Algebra.toSMul K Omega _ _ inferInstance) :=
    IsScalarTower.of_algebraMap_eq' (R := K) (S := IField) (A := Omega) rfl
  let : IsSepClosure K Omega :=
    ⟨IsSepClosure.sep_closed L, Algebra.IsSeparable.trans K L Omega⟩
  exact fieldPointedQuotientHom_eq_canonicalUnconjugatedHom K IField L Omega

/-- After transporting the actual pointed quotient through the field/deck
equivalence and the explicit comparison conjugation, its image is exactly
normalization-prime ideal inertia. -/
theorem localizedNormalizationInertiaFieldPointedQuotientOfMorphism_range_map :
    let actualQuotient :=
      localizedNormalizationInertiaFieldPointedQuotientHom (K := K) (L := L) P Q
    let E := EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L
    let c := localizedNormalizationInertiaFieldCanonicalConjugatingElement
      (K := K) (L := L) P Q
    (actualQuotient.range.map E.symm.toMonoidHom).map
        (MulAut.conj c).toMonoidHom =
      localizedNormalizationInertia (K := K) (L := L) P Q := by
  intro actualQuotient E c
  have hcomp :
      E.symm.toMonoidHom.comp actualQuotient =
        localizedNormalizationInertiaFieldCanonicalUnconjugatedHom
          (K := K) (L := L) P Q :=
    localizedNormalizationInertiaFieldPointedQuotientOfMorphism_eq_canonicalUnconjugated
      (K := K) (L := L) P Q
  have hrange :
      (localizedNormalizationInertiaFieldCanonicalUnconjugatedHom
          (K := K) (L := L) P Q).range.map
            (MulAut.conj c).toMonoidHom =
        localizedNormalizationInertia (K := K) (L := L) P Q :=
    localizedNormalizationInertiaFieldCanonicalUnconjugatedHom_range_map
      (K := K) (L := L) P Q
  calc
    (actualQuotient.range.map E.symm.toMonoidHom).map
          (MulAut.conj c).toMonoidHom =
        (E.symm.toMonoidHom.comp actualQuotient).range.map
          (MulAut.conj c).toMonoidHom := by
      rw [MonoidHom.range_comp]
    _ = (localizedNormalizationInertiaFieldCanonicalUnconjugatedHom
          (K := K) (L := L) P Q).range.map
            (MulAut.conj c).toMonoidHom := by
      rw [hcomp]
    _ = localizedNormalizationInertia (K := K) (L := L) P Q := hrange

local notation "FieldCover" => FiniteEtale.mk (ξ K L)

local instance pointedComparison_fieldCoverIsGalois : IsGalois FieldCover :=
  EtaleFundamentalGroups.fieldFiniteEtaleCover_isGalois K L

local instance pointedComparison_fieldCoverIsConnected : IsConnected FieldCover :=
  inferInstance

local instance pointedComparison_fieldCoverAutFinite : Finite (Aut FieldCover) :=
  inferInstance

local instance pointedComparison_fieldCoverAutOpFinite :
    Finite ((Aut FieldCover)ᵐᵒᵖ) :=
  Finite.of_injective MulOpposite.unop MulOpposite.unop_injective

/-- If the same actual pointed inertia image has cardinality prime to every
rational prime, then normalization-prime ideal inertia is trivial. -/
theorem localizedNormalizationInertia_eq_bot_of_pointedQuotient_coprime_every_prime :
    let actualQuotient :=
      localizedNormalizationInertiaFieldPointedQuotientHom (K := K) (L := L) P Q
    (∀ p : ℕ, p.Prime → Nat.Coprime (Nat.card actualQuotient.range) p) →
      localizedNormalizationInertia (K := K) (L := L) P Q = ⊥ := by
  intro actualQuotient hCoprime
  let E := EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L
  let c := localizedNormalizationInertiaFieldCanonicalConjugatingElement
    (K := K) (L := L) P Q
  have hrange :
      (actualQuotient.range.map E.symm.toMonoidHom).map
          (MulAut.conj c).toMonoidHom =
        localizedNormalizationInertia (K := K) (L := L) P Q :=
    localizedNormalizationInertiaFieldPointedQuotientOfMorphism_range_map
      (K := K) (L := L) P Q
  have hq : actualQuotient.range = ⊥ :=
    ProCGroups.Boundary.subgroup_eq_bot_of_card_coprime_every_prime
      actualQuotient.range hCoprime
  rw [hq] at hrange
  simpa only [Subgroup.map_bot] using hrange.symm

end

end EtaleFundamentalGroups.Inertia

end
