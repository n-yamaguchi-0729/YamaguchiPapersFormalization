/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.PrincipalIdealDomain
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.RationalLocalization
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.JacobianVarieties.Picard.Designation
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.JacobianVarieties.Picard.schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth_isReduced_of_isReduced_of_isLocallyNoetherian

/-!
# Geometric-point extensionality over a localized integer ring

Smoothness makes the representing scheme reduced, so the reduced geometric-point
extensionality theorem identifies morphisms agreeing on algebraic-closure-valued points.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.SmoothPointRigidity

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

theorem _root_.AlgebraicGeometry.RelPicard.schemeHomOver_ext_of_forall_algebraicClosure_point
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(Rat.LocalizationAt ℓ)))
    (D : RelativePic0Designation ↥(Rat.LocalizationAt ℓ) c)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase)
    (φ ψ : SchemeHomOver D.toBase D.toBase)
    (h : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(Rat.LocalizationAt ℓ) (AlgebraicClosure ℚ)))) D.toBase,
      x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by
  have : IsPrincipalIdealRing ↥(Rat.LocalizationAt ℓ) := Rat.LocalizationAt.isPrincipalIdealRing ℓ
  have : IsNoetherianRing ↥(Rat.LocalizationAt ℓ) := inferInstance
  have : Smooth D.toBase := hsm
  have : IsReduced D.P :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian D.toBase
  exact AlgebraicGeometry.RelPicard.schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced
    ℓ c D hsm hpr φ ψ h
end JacobianVarieties.Picard.Proofs.SmoothPointRigidity
end ProofImplementation
