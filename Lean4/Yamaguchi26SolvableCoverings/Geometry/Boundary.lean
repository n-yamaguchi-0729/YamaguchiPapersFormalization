/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Divisors.ArithmeticBoundary
import SchemeTheory.Divisors.LocalComplement
import EtaleFundamentalGroups.GeometricFiber.Functoriality
import ProCGroups.ProC.MaximalQuotients.ResidualCore
import ProCGroups.FiniteGroups.StandardClasses
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Arithmetic boundary data

These are the geometric definitions used in `SolvableCoverings.tex`: reduced prime
components of an effective Cartier divisor, their generic points, horizontality over
`Spec ℤ`, and geometric integrality after finite etale covers. Schemes and geometric
point fields are in universe zero.

The ambient scheme is not assumed globally integral, normal, reduced, or of finite
type. The generic-fiber condition is imposed on individual reduced boundary components.
The maximal prosolvable quotient uses the existing closed residual core.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Yamaguchi26SolvableCoverings

/-- The prime components of the divisor (their schemes have reduced structure). -/
abbrev Component {X : Scheme.{0}} (D : X.EffectiveCartierDivisor) :=
  { Z : Set D.1.subscheme // Z ∈ irreducibleComponents D.1.subscheme }

/-- The generic point of a prime component, regarded as a point of `X`. -/
def componentPoint {X : Scheme.{0}} (D : X.EffectiveCartierDivisor)
    (E : Component D) : X :=
  D.1.subschemeι E.property.1.genericPoint

/-- The canonical arithmetic structure morphism; it is not extra input data. -/
def toIntegers (X : Scheme.{0}) : X ⟶ Spec (CommRingCat.of ℤ) :=
  specZIsTerminal.from X

/-- Every prime component of `D` dominates `Spec ℤ`. -/
def IsHorizontal {X : Scheme.{0}} (D : X.EffectiveCartierDivisor) : Prop :=
  D.IsHorizontalOver (toIntegers X)

/-- Geometric integrality of each reduced boundary component's generic fiber
over `ℚ`, rather than geometric integrality of the entire arithmetic morphism. -/
def HasGeometricallyIntegralGenericComponents {X : Scheme.{0}}
    (I : X.IdealSheafData) : Prop :=
  ∀ (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme),
    GeometricallyIntegral
      ((I.componentToBase (toIntegers X) Z hZ).fiberToSpecResidueField
        (genericPoint (Spec (CommRingCat.of ℤ))))

/-- The geometric-integrality hypothesis after every connected finite étale
cover, including covers which are not Galois. -/
def HasGeometricallyIntegralGenericComponentsAfterCovers {X : Scheme.{0}}
    (D : X.EffectiveCartierDivisor) : Prop :=
  ∀ (Y : FiniteEtale X), ConnectedSpace Y.left →
    HasGeometricallyIntegralGenericComponents (D.1.comap Y.hom)

/-- The maximal prosolvable quotient, using the existing closed residual core. -/
abbrev Prosolvable (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :=
  G ⧸ ProCGroups.ProC.proCResidualCore ProCGroups.FiniteGroupClass.solvable G

end Yamaguchi26SolvableCoverings
