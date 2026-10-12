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

import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut

/-!
The zero section makes the structure map of the representing Picard scheme surjective.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PicardStructureSurjective

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian

theorem _root_.AlgebraicGeometry.RelPicard.surjective_toBase_of_representsRelSubPic_algEquivZeroCut
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (_h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) :
    Surjective D.toBase := by
  refine ⟨fun s => ⟨D.zeroSection.base s, ?_⟩⟩
  have hs := congrArg
    (fun φ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R) => φ.base s) D.zeroSection_toBase
  exact hs
end JacobianVarieties.Picard.Proofs.PicardStructureSurjective
end ProofImplementation
