/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.ArithmeticBoundary
public import Nyll.SchemeTheory.Fibers.BaseIsomorphism
public import Nyll.SchemeTheory.FunctionFields.IntegerBase
public import Nyll.SchemeTheory.Divisors.CartierBoundaryComponents
public import Nyll.SchemeTheory.Divisors.LocalComplement
public import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore
public import Nyll.ProCGroups.FiniteGroups.StandardClasses
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Arithmetic boundary data

These are the geometric definitions used in [Yamaguchi, arXiv:2610.02948v1](https://arxiv.org/abs/2610.02948v1): reduced prime
components of an effective Cartier divisor, their generic points, horizontality over
`Spec ℤ`, represented by `Spec (ULift.{u} ℤ)`, and geometric integrality after finite etale
covers. The actual arithmetic maps and component fibers are defined in every scheme universe.

The ambient scheme is not assumed globally integral, normal, reduced, or of finite
type. The generic-fiber condition is imposed on individual reduced boundary components.
The maximal prosolvable quotient uses the existing closed residual core.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] uliftIntegerBaseIsDomain

namespace Yamaguchi26SolvableCoverings

/-- The canonical arithmetic structure morphism; it is not extra input data. -/
def toIntegers (X : Scheme.{u}) : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
  specULiftZIsTerminal.from X

/-- Every prime component of `D` dominates `Spec ℤ`. -/
def IsHorizontal {X : Scheme.{u}} (D : X.EffectiveCartierDivisor) : Prop :=
  D.IsHorizontalOver (toIntegers X)

/-- Geometric integrality of each reduced boundary component's generic fiber
over `ℚ`, rather than geometric integrality of the entire arithmetic morphism. -/
def HasGeometricallyIntegralGenericComponents {X : Scheme.{u}}
    (I : X.IdealSheafData) : Prop :=
  ∀ (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme),
    GeometricallyIntegral
      ((I.componentToBase (toIntegers X) Z hZ).fiberToSpecResidueField
        (genericPoint (Spec (CommRingCat.of (ULift.{u} ℤ)))))

/-- The geometric-integrality hypothesis after every connected finite étale
cover, including covers which are not Galois. -/
def HasGeometricallyIntegralGenericComponentsAfterCovers {X : Scheme.{u}}
    (D : X.EffectiveCartierDivisor) : Prop :=
  ∀ (Y : FiniteEtale X), ConnectedSpace Y.left →
    HasGeometricallyIntegralGenericComponents (D.1.comap Y.hom)

/-- The actual arithmetic structure morphism recovers the original one in universe zero. -/
theorem toIntegers_comp_specULiftZIsoOriginal (X : Scheme.{0}) :
    toIntegers X ≫ specULiftZIsoOriginal.hom = specZIsTerminal.from X :=
  specULiftZ_from_comp_isoOriginal X

/-- Horizontality in universe zero is exactly the original density condition over `Spec ℤ`. -/
theorem isHorizontal_iff_original {X : Scheme.{0}}
    (D : X.EffectiveCartierDivisor) :
    IsHorizontal D ↔ D.IsHorizontalOver (specZIsTerminal.from X) := by
  unfold IsHorizontal Scheme.EffectiveCartierDivisor.IsHorizontalOver
  apply forall_congr'
  intro Z
  apply forall_congr'
  intro hZ
  simpa only [Scheme.IdealSheafData.componentToBase, Category.assoc,
    toIntegers_comp_specULiftZIsoOriginal] using
      (Scheme.Hom.denseRange_comp_iso_iff
        (D.1.componentToBase (toIntegers X) Z hZ) specULiftZIsoOriginal).symm

/-- The component generic-fiber condition is unchanged under the actual integer-base iso. -/
theorem hasGeometricallyIntegralGenericComponents_iff_original {X : Scheme.{0}}
    (I : X.IdealSheafData) :
    HasGeometricallyIntegralGenericComponents I ↔
      ∀ (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme),
        GeometricallyIntegral
          ((I.componentToBase (specZIsTerminal.from X) Z hZ).fiberToSpecResidueField
            (genericPoint (Spec (CommRingCat.of ℤ)))) := by
  unfold HasGeometricallyIntegralGenericComponents
  apply forall_congr'
  intro Z
  apply forall_congr'
  intro hZ
  have hcomp : I.componentToBase (toIntegers X) Z hZ ≫ specULiftZIsoOriginal.hom =
      I.componentToBase (specZIsTerminal.from X) Z hZ := by
    simp only [Scheme.IdealSheafData.componentToBase, Category.assoc,
      toIntegers_comp_specULiftZIsoOriginal]
  rw [← hcomp]
  exact Scheme.Hom.geometricallyIntegral_genericFiber_comp_iso_iff
    (I.componentToBase (toIntegers X) Z hZ) specULiftZIsoOriginal

/-- The same comparison applies to every original connected finite étale cover. -/
theorem hasGeometricallyIntegralGenericComponentsAfterCovers_iff_original
    {X : Scheme.{0}} (D : X.EffectiveCartierDivisor) :
    HasGeometricallyIntegralGenericComponentsAfterCovers D ↔
      ∀ (Y : FiniteEtale X), ConnectedSpace Y.left →
        ∀ (Z : Set (D.1.comap Y.hom).subscheme)
          (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme),
          GeometricallyIntegral
            (Scheme.Hom.fiberToSpecResidueField
              ((D.1.comap Y.hom).componentToBase (specZIsTerminal.from Y.left) Z hZ)
              (genericPoint (Spec (CommRingCat.of ℤ)))) := by
  unfold HasGeometricallyIntegralGenericComponentsAfterCovers
  apply forall_congr'
  intro Y
  apply forall_congr'
  intro _hY
  exact hasGeometricallyIntegralGenericComponents_iff_original (D.1.comap Y.hom)

/-- The maximal prosolvable quotient, using the existing closed residual core. -/
abbrev Prosolvable (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :=
  G ⧸ ProCGroups.ProC.proCResidualCore ProCGroups.FiniteGroupClass.solvable G

end Yamaguchi26SolvableCoverings
