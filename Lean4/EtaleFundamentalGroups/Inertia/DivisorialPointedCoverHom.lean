/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.FieldCoverQuotient
import EtaleFundamentalGroups.Inertia.DivisorialQuotientCanonicalFundamentalGroup
import EtaleFundamentalGroups.Inertia.DivisorialStrictHenselian

/-!
# Pointed field-cover quotients at divisorial inertia sources

This file constructs the actual pointed categorical quotient of the finite
field cover after restriction along the normalization-prime inertia fixed
field.
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

/-- The pointed quotient of the finite field cover along the inertia fixed
field, before transporting its deck group back to `Gal(L/K)`. The point and
its fiber comparison are constructed by the generic field definition. -/
noncomputable def localizedNormalizationInertiaFieldPointedQuotientHom :
    let : CommRing IField := (inferInstance : Field IField).toCommRing
    let : CommSemiring IField := (inferInstance : Field IField).toSemifield.toCommSemiring
    let : CommRing Omega := (inferInstance : Field Omega).toCommRing
    let : CommSemiring Omega := (inferInstance : Field Omega).toSemifield.toCommSemiring
    let : Algebra IField Omega :=
      ((algebraMap L Omega).comp (algebraMap IField L)).toAlgebra
    Aut (fib IField Omega) →* (Aut (FiniteEtale.mk (ξ K L)))ᵐᵒᵖ := by
  intro hFCommRing hFCommSemiring hOmegaCommRing hOmegaCommSemiring hFOmega
  let hKOmega : Algebra K Omega :=
    ((algebraMap L Omega).comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K L Omega := IsScalarTower.of_algebraMap_eq' rfl
  let : @IsScalarTower K IField Omega
      (@Algebra.toSMul K IField _ _ inferInstance)
      (@Algebra.toSMul IField Omega _ _ inferInstance)
      (@Algebra.toSMul K Omega _ _ inferInstance) :=
    IsScalarTower.of_algebraMap_eq' (R := K) (S := IField) (A := Omega) rfl
  exact fieldPointedQuotientHom K IField L Omega

end

end EtaleFundamentalGroups.Inertia

end
