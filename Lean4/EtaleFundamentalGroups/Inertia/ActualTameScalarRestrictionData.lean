/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteTameScalarData
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestrictionConjugate
import EtaleFundamentalGroups.Inertia.ActualFiniteResidueActionSquare
import EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinate

/-!
# The literal actual scalar restriction diagram

Each data function is the underlying function of an existing actual map.
The coefficient and conjugation comparisons are proved separately; none
is a hypothesis or a field of the diagram.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Restriction functions and coefficient inclusion only, with no asserted laws. -/
structure ScalarInertiaRestrictionData
    (source : ScalarInertiaActionData.{u}) (target : ScalarInertiaActionData.{v}) where
  /-- The underlying function of the actual inertia restriction. -/
  inertiaMap : source.inertia → target.inertia
  /-- The underlying function of the actual decomposition restriction. -/
  decompositionMap : source.decomposition → target.decomposition
  /-- The underlying function of the literal residue embedding. -/
  residueMap : target.residue → source.residue

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The SAME original finite coordinate and the SAME original actions. -/
def actualTameCoordinateScalarData (E : FiniteGaloisIntermediateField K L) :
    ScalarInertiaActionData.{w} where
  inertia := (actualNormalizationInertiaGroup A K L Q).carrier
  decomposition := (normalizationDecompositionGroup A K L Q).carrier
  residue := Q.ResidueField
  character σ := ((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val.val
  conjugate := originalFiniteNormalizationInertiaConjugate A K L Q
  action d := (actualNormalizationResidueFieldMap A K L Q d).toFun

/-- Store the actual inertia restriction with its native source and target closed. -/
def actualScalarInertiaRestriction (E : FiniteGaloisIntermediateField K L) :
    (actualTameCoordinateScalarData A K L Q E).inertia →
      (actualFiniteTameScalarData A K L Q E).inertia :=
  (actualFiniteInertiaRestriction A K L Q E).hom'.toFun

/-- Store the actual decomposition restriction with the SAME closed carriers. -/
def actualScalarDecompositionRestriction (E : FiniteGaloisIntermediateField K L) :
    (actualTameCoordinateScalarData A K L Q E).decomposition →
      (actualFiniteTameScalarData A K L Q E).decomposition :=
  (actualFiniteDecompositionRestriction A K L Q E).hom'.toFun

/-- Store the literal finite residue embedding, with no action comparison assumed. -/
def actualScalarResidueInclusion (E : FiniteGaloisIntermediateField K L) :
    (actualFiniteTameScalarData A K L Q E).residue →
      (actualTameCoordinateScalarData A K L Q E).residue :=
  (actualFiniteNormalizationResidueMap A K L Q E).toFun

/-- Assemble only the three independently constructed actual functions. -/
def actualTameScalarRestrictionData (E : FiniteGaloisIntermediateField K L) :
    ScalarInertiaRestrictionData (actualTameCoordinateScalarData A K L Q E)
      (actualFiniteTameScalarData A K L Q E) where
  inertiaMap := actualScalarInertiaRestriction A K L Q E
  decompositionMap := actualScalarDecompositionRestriction A K L Q E
  residueMap := actualScalarResidueInclusion A K L Q E

/-- This diagram's character equation is the existing actual coordinate composition. -/
theorem actualTameScalarRestrictionData_character
    (E : FiniteGaloisIntermediateField K L)
    (σ : (actualTameCoordinateScalarData A K L Q E).inertia) :
    (actualTameCoordinateScalarData A K L Q E).character σ =
      (actualTameScalarRestrictionData A K L Q E).residueMap
        ((actualFiniteTameScalarData A K L Q E).character
          ((actualTameScalarRestrictionData A K L Q E).inertiaMap σ)) := rfl

/-- The diagram uses the proved actual original-to-finite conjugation comparison. -/
theorem actualTameScalarRestrictionData_conjugate
    (E : FiniteGaloisIntermediateField K L)
    (d : (actualTameCoordinateScalarData A K L Q E).decomposition)
    (σ : (actualTameCoordinateScalarData A K L Q E).inertia) :
    (actualTameScalarRestrictionData A K L Q E).inertiaMap
        ((actualTameCoordinateScalarData A K L Q E).conjugate d σ) =
      (actualFiniteTameScalarData A K L Q E).conjugate
        ((actualTameScalarRestrictionData A K L Q E).decompositionMap d)
        ((actualTameScalarRestrictionData A K L Q E).inertiaMap σ) :=
  actualFiniteInertiaRestriction_conjugate A K L Q E d σ

/-- Its residue-action equation is the independently proved literal inclusion square. -/
theorem actualTameScalarRestrictionData_residue
    (E : FiniteGaloisIntermediateField K L)
    (d : (actualTameCoordinateScalarData A K L Q E).decomposition)
    (x : (actualFiniteTameScalarData A K L Q E).residue) :
    (actualTameScalarRestrictionData A K L Q E).residueMap
        ((actualFiniteTameScalarData A K L Q E).action
          ((actualTameScalarRestrictionData A K L Q E).decompositionMap d) x) =
      (actualTameCoordinateScalarData A K L Q E).action d
        ((actualTameScalarRestrictionData A K L Q E).residueMap x) :=
  actualFiniteNormalizationResidueMap_action A K L Q E d x

end EtaleFundamentalGroups.Inertia

end
