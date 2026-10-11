/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_abelianSchemePropertyBundle_prodStr.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Product
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_geometricallyIntegral

/-!
# abelian Scheme Property Bundle prod Str
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace abelianSchemePropertyBundle_prodStr

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem _root_.GoodReductionJacobian.abelianSchemePropertyBundle_prodStr
    {K : Type u} [Field K] {B C : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of K)}
    {h : C ⟶ Spec (CommRingCat.of K)} (hB : AbelianSchemePropertyBundle K g)
    (hC : AbelianSchemePropertyBundle K h) :
    AbelianSchemePropertyBundle K (prodStr g h) := by
  have : Smooth g := hB.smooth
  have : Smooth h := hC.smooth
  have : IsProper g := hB.proper
  have : IsProper h := hC.proper
  have : GeometricallyIntegral g := hB.geometricallyIntegral
  have : GeometricallyIntegral h := hC.geometricallyIntegral
  have : IrreducibleSpace C := GeometricallyIrreducible.irreducibleSpace_of_subsingleton h
  have : UniversallyOpen g := UniversallyOpen.of_flat g
  have : IrreducibleSpace ↥(pullback g h) := inferInstance
  obtain ⟨GB⟩ := hB.hasGroupLaw
  obtain ⟨GC⟩ := hC.hasGroupLaw
  refine ⟨inferInstance, inferInstance, fun s => ?_, ⟨GB.prod GC⟩⟩
  have hs : (prodStr g h).base ⁻¹' {s} = Set.univ :=
    Set.eq_univ_of_forall fun a => Subsingleton.elim _ _
  rw [hs, ← connectedSpace_iff_univ]
  infer_instance
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs.abelianSchemePropertyBundle_prodStr
end ProofImplementation
