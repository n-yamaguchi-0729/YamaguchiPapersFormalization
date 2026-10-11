/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaBaseLocalization
import SchemeTheory.Normalization.FiniteSeparable
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Original inertia on an affine chart and the actual scheme stalk

The base localization is the scheme's literal local ring, using its germ
map and the existing stalk-to-function-field map. The normalization prime
is extended by the literal inclusion in the same Galois field, and becomes
maximal. Its original inertia subgroup is unchanged.
-/

noncomputable section

open AlgebraicGeometry

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The actual germ from an affine chart to a scheme stalk preserves the
original inertia subgroup after normalizing in the same Galois field.
The prime over the original point becomes a maximal normalization prime. -/
theorem affineNormalizationInertia_eq_stalkNormalizationInertia
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L] [IsGalois X.functionField L]
    (U : X.affineOpens) (x : U.1) :
    let : Nonempty U.1 := ⟨x⟩
    let : Algebra Γ(X, U.1) (X.presheaf.stalk x.val) :=
      (X.presheaf.germ U.1 x.val x.property).hom.toAlgebra
    let : Algebra Γ(X, U.1) L := X.affineExtensionAlgebra U.1 L
    let : Algebra (X.presheaf.stalk x.val) L := X.stalkExtensionAlgebra x.val L
    let : IsScalarTower Γ(X, U.1) (X.presheaf.stalk x.val) L :=
      IsScalarTower.of_algebraMap_eq fun a => by
        change algebraMap X.functionField L (X.germToFunctionField U.1 a) =
          algebraMap X.functionField L
            (algebraMap (X.presheaf.stalk x.val) X.functionField
              (X.presheaf.germ U.1 x.val x.property a))
        exact congrArg (algebraMap X.functionField L)
          (X.algebraMap_germ_eq_germToFunctionField x.property a).symm
    let : IsFractionRing Γ(X, U.1) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U.1 U.2
    let : IsScalarTower Γ(X, U.1) X.functionField L :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower (X.presheaf.stalk x.val) X.functionField L :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : MulSemiringAction Gal(L/X.functionField) (integralClosure Γ(X, U.1) L) :=
      IsIntegralClosure.MulSemiringAction Γ(X, U.1) X.functionField L
        (integralClosure Γ(X, U.1) L)
    let : MulSemiringAction Gal(L/X.functionField)
        (integralClosure (X.presheaf.stalk x.val) L) :=
      IsIntegralClosure.MulSemiringAction (X.presheaf.stalk x.val) X.functionField L
        (integralClosure (X.presheaf.stalk x.val) L)
    ∀ (Q : Ideal (integralClosure Γ(X, U.1) L)) [Q.IsPrime]
      [Q.LiesOver (U.2.primeIdealOf x).asIdeal],
      let q := Q.map
        (normalizationBaseLocalizationRingMap Γ(X, U.1) (X.presheaf.stalk x.val) L)
      q.IsMaximal ∧ Q.inertia Gal(L/X.functionField) = q.inertia Gal(L/X.functionField) := by
  intro actualNonempty actualGermAlgebra actualAffineAlgebra actualStalkAlgebra
    actualGermTower actualFraction actualAffineTower actualStalkTower
    actualAffineAction actualStalkAction Q hQ hOver
  have : IsLocalization.AtPrime (X.presheaf.stalk x.val) (U.2.primeIdealOf x).asIdeal :=
    U.2.isLocalization_stalk x
  exact originalNormalizationInertia_eq_of_primeLocalization Γ(X, U.1)
    (X.presheaf.stalk x.val) X.functionField L (U.2.primeIdealOf x).asIdeal Q

end EtaleFundamentalGroups.Inertia
