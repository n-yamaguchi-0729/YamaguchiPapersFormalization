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

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.Modules.ProjectivePresentation
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_FiniteBySections_isFinite_of_unit
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_FiniteBySections_of_isFinite

/-!
# Scheme Modules Finite By Sections of finite By Sections unit
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_FiniteBySections_of_finiteBySections_unit

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_finiteBySections_unit
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (h𝒪 : Scheme.Modules.FiniteBySections (SheafOfModules.unit X.ringCatSheaf : X.Modules) f)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.FiniteBySections M f := by
  have : IsFinite f := AlgebraicGeometry.Scheme.Modules.FiniteBySections.isFinite_of_unit f h𝒪
  exact AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_isFinite f M hM
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_FiniteBySections_of_finiteBySections_unit
end ProofImplementation
