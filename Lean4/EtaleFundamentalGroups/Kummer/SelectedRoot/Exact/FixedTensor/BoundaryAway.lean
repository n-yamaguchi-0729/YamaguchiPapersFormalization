/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.IntegralClosure.IntegralBase.BoundaryAway
import EtaleFundamentalGroups.Kummer.SelectedRoot.Exact.FixedTensorComponentBijective

/-!
# Boundary Away in a fixed exact-root tensor component

The prefix normalization and the normalization after adjoining the selected
exact root live in different ambient fields.  Therefore their primitive
Away maps cannot be related by integral-base transport alone.

At a strictly Henselian exact root, however, normalization etaleness in a
fixed tensor component produces bijectivity of its canonical right field
coordinate.  This file first uses that sourced field comparison to transport
the prefix Away map to the *same* component field, and only then enlarges the
integral base to the global root cover.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uA uD uK uV uOmega uW uFroot

/-- A fixed component of an exact ramification-root tensor product inherits
the global primitive Away map of the original target field.

The right-coordinate comparison is generated internally from strict
Henselian splitting and normalization etaleness.  The supplied map
`j : D →ₐ[A] P` is the literal global root-cover action on that same
component.  It is used only after the ambient-field Away transport, so no
ramified `A → D` map is incorrectly treated as etale. -/
theorem
    pureRadicalFractionFieldGenericTensorComponent_integralBase_boundaryAway_of_exactRoot
    {A : Type uA} {D : Type uD}
    {K : Type uK} {Omega : Type uOmega} {Froot : Type uFroot}
    [CommRing A] [CommRing D]
    [Field K] [Field Omega] [Field Froot]
    [Algebra A K] [Algebra K Omega]
    [Algebra A Omega] [IsScalarTower A K Omega]
    [Algebra A D] [Module.Finite A D]
    [Algebra K Froot]
    (base : DVF.{uK, uV} K) (target : DVF.{uOmega, uW} Omega)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    [Algebra
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsFractionRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [Algebra base.valuationSubring Froot]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsScalarTower base.valuationSubring K Froot]
    [HenselianLocalRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))]
    (m : Ideal (Froot ⊗[K] Omega)) [m.IsMaximal] :
    let P := GenericTensorFieldComponent m
    letI : Algebra Omega P := genericTensorFieldComponentRightAlgebra m
    let omegaPAlgebra : Algebra A P :=
      ((algebraMap Omega P).comp (algebraMap A Omega)).toAlgebra
    letI : Algebra A P := omegaPAlgebra
    ∀ (j : D →ₐ[A] P),
      (letI : Algebra base.valuationSubring P :=
         pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
           (N := ramificationIndex base target) varpi m
       letI : Algebra
           (AdjoinRoot
             (X ^ ramificationIndex base target - C varpi)) P :=
         pureRadicalFractionFieldGenericTensorComponentRootAlgebra
           (K := K) varpi m
       Algebra.Etale
         (AdjoinRoot
           (X ^ ramificationIndex base target - C varpi))
         (integralClosure
           (AdjoinRoot
             (X ^ ramificationIndex base target - C varpi)) P)) →
      ∀ (f : A),
        (Localization.awayMap
          (algebraMap A (integralClosure A Omega)) f).Etale →
        letI : Algebra D P := j.toAlgebra
        letI : IsScalarTower A D P :=
          IsScalarTower.of_algebraMap_eq fun x ↦ (j.commutes x).symm
        (Localization.awayMap
          (algebraMap A (integralClosure D P)) f).Etale := by
  dsimp only
  let P := GenericTensorFieldComponent m
  let : Algebra Omega P := genericTensorFieldComponentRightAlgebra m
  let omegaPAlgebra : Algebra A P :=
    ((algebraMap Omega P).comp (algebraMap A Omega)).toAlgebra
  let : Algebra A P := omegaPAlgebra
  let : IsScalarTower A Omega P :=
    IsScalarTower.of_algebraMap_eq' rfl
  intro j hEtale f hAway
  let : Algebra D P := j.toAlgebra
  let : IsScalarTower A D P :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (j.commutes x).symm
  have hbij : Function.Bijective (algebraMap Omega P) :=
    pureRadicalFractionFieldGenericTensorComponent_rightAlgebraMap_bijective_of_exactRoot
      (K := K) (Froot := Froot) (L := Omega)
      base target varpi hvarpi m hEtale
  have hAwayP :
      (Localization.awayMap
        (algebraMap A (integralClosure A P)) f).Etale :=
    EtaleFundamentalGroups.integralClosure_boundaryAway_of_bijective_fieldTower_algebraMap
      (A := A) hbij f hAway
  exact
    EtaleFundamentalGroups.integralClosure_integralBase_boundaryAway
      (A := A) (B := D) (L := P) f hAwayP

end EtaleFundamentalGroups.Kummer

end
