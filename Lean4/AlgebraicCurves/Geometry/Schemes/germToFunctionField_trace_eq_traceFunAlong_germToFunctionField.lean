/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_germToFunctionField_trace_eq_traceFunAlong_germToFunctionField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Models.Places
import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Cohomology.Cech.Maps
import AlgebraicCurves.Models.GermToFunctionField_app_eq_of_fromSpecStalk_comp_eq

/-!
# germ To Function Field trace eq trace Fun Along germ To Function Field
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace germToFunctionField_trace_eq_traceFunAlong_germToFunctionField

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem _root_.AlgebraicGeometry.germToFunctionField_trace_eq_traceFunAlong_germToFunctionField
    {K : Type u} [Field K] {X Y : Scheme.{u}} (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
    [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) [IsAffineHom π] (_hπ : π ≫ cX = cY)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (π ⁻¹ᵁ U : Y.Opens)] :
    letI := (AlgebraicCurve.baseToFunctionField cX).toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField cY).toAlgebra
    letI : Algebra Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
    ∀ [Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U)] [Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U)]
      (φ : X.functionField →ₐ[K] Y.functionField)
      (_hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
      (g : Γ(Y, π ⁻¹ᵁ U)),
      (X.germToFunctionField U).hom (Algebra.trace Γ(X, U) Γ(Y, π ⁻¹ᵁ U) g) =
        AlgebraicCurve.traceFunAlong φ ((Y.germToFunctionField (π ⁻¹ᵁ U)).hom g) := by
  intro _ _ φ hφπ g
  let := (AlgebraicCurve.baseToFunctionField cX).toAlgebra
  let := (AlgebraicCurve.baseToFunctionField cY).toAlgebra
  let iAB : Algebra Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
  let : Algebra X.functionField Y.functionField := AlgebraicCurve.algebraAlong φ
  have hUaff : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  have : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U
    hU
  have : IsFractionRing Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ hUaff
  have hnat : ∀ a : Γ(X, U), (Y.germToFunctionField (π ⁻¹ᵁ U)).hom (π.app U a) =
      φ ((X.germToFunctionField U).hom a) := fun a =>
    AlgebraicCurve.germToFunctionField_app_eq_of_fromSpecStalk_comp_eq π φ.toRingHom hφπ U a
  let : Algebra Γ(X, U) Y.functionField :=
    ((algebraMap Γ(Y, π ⁻¹ᵁ U) Y.functionField).comp (algebraMap Γ(X, U) Γ(Y, π ⁻¹ᵁ U))).toAlgebra
  have : IsScalarTower Γ(X, U) Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a => hnat a)
  have : FaithfulSMul Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h := congrArg (fun t => (Y.germToFunctionField (π ⁻¹ᵁ U)).hom t) hab
    change (Y.germToFunctionField (π ⁻¹ᵁ U)).hom (π.app U a) =
      (Y.germToFunctionField (π ⁻¹ᵁ U)).hom (π.app U b) at h
    rw [hnat, hnat] at h
    exact X.germToFunctionField_injective U (φ.toRingHom.injective h)
  have : Algebra.IsIntegral Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := Algebra.IsIntegral.of_finite _ _
  have : Algebra.IsAlgebraic Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := Algebra.IsIntegral.isAlgebraic
  have key : Algebra.trace X.functionField Y.functionField (algebraMap Γ(Y, π ⁻¹ᵁ U)
    Y.functionField g) =
      algebraMap Γ(X, U) X.functionField (Algebra.trace Γ(X, U) Γ(Y, π ⁻¹ᵁ U) g) :=
    Algebra.trace_localization Γ(X, U) (nonZeroDivisors Γ(X, U)) g
  rw [AlgebraicCurve.traceFunAlong_apply]
  exact key.symm
end germToFunctionField_trace_eq_traceFunAlong_germToFunctionField
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
