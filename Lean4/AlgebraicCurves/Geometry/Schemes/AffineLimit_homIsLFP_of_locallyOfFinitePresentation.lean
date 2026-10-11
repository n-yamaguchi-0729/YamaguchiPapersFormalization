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

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import AlgebraicCurves.Geometry.Schemes.AffineLimit
import SchemeTheory.Descent.FGSubalgebra
import AlgebraicCurves.Geometry.Schemes.FGSubalgebra_nonempty_isLimit_specCone

/-!
# Finite-presentation morphisms satisfy the affine-limit factorization property

A locally finitely presented morphism admits factorizations and eventual equalities over
the affine inverse systems arising from finitely generated subalgebras.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace AffineLimit_homIsLFP_of_locallyOfFinitePresentation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.AffineLimit.homIsLFP_of_locallyOfFinitePresentation
    (R : Type u) [CommRing R] {X : Scheme.{u}} (ξ : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation ξ] : AffineLimit.HomIsLFP ξ := by
  refine ⟨fun A _ _ φ hφ ↦ ?_, fun A _ _ A₀ hA₀ φ₀ φ₀' h₀ h₀' hφ ↦ ?_⟩
  · obtain ⟨⟨A₀, hA₀⟩, g, hg, hg'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (FGSubalgebra.specDiagram R A) (FGSubalgebra.specOver R A) ξ (FGSubalgebra.specCone R A)
      (FGSubalgebra.nonempty_isLimit_specCone R A).some φ
      (by rw [FGSubalgebra.specCone_π_comp_specOver]; exact congrArg _ hφ.symm)
    exact ⟨A₀, hA₀, g, hg', hg⟩
  · obtain ⟨⟨A₁, hA₁⟩, ⟨⟨⟨h⟩⟩⟩, H⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (FGSubalgebra.specDiagram R A) (FGSubalgebra.specOver R A) ξ (FGSubalgebra.specCone R A)
      (FGSubalgebra.nonempty_isLimit_specCone R A).some (i := Opposite.op ⟨A₀, hA₀⟩) φ₀ φ₀'
      h₀.symm h₀'.symm hφ
    exact ⟨A₁, hA₁, h, H⟩
end AffineLimit_homIsLFP_of_locallyOfFinitePresentation
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

open _root_.AlgebraicGeometry.FGSubalgebra in
attribute [-instance]
  AlgebraicGeometry.FGSubalgebra.instIsDirectedLe
  instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite
  AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instNonempty
  AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG
  instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG
  AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instIsFiltered
attribute [-simp] AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply
