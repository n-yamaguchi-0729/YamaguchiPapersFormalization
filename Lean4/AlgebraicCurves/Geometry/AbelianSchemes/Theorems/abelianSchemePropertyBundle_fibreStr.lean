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

import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Fibre
import AlgebraicCurves.Geometry.Schemes.SchemeFibreEndo
import AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle

/-!
# abelian Scheme Property Bundle fibre Str
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace abelianSchemePropertyBundle_fibreStr

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem _root_.GoodReductionJacobian.abelianSchemePropertyBundle_fibreStr
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    AbelianSchemePropertyBundle (RelativeGroupLaw.baseResidueField s) (RelativeGroupLaw.fibreStr f
      s) := by
  have : Smooth f := hA.smooth
  have : IsProper f := hA.proper
  refine ⟨inferInstance, inferInstance, ?_, ⟨(Classical.choice hA.hasGroupLaw).fibre s⟩⟩
  intro s'
  have huniv : (RelativeGroupLaw.fibreStr f s).base ⁻¹' {s'} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [huniv]
  have hconn : _root_.IsConnected (f.base ⁻¹' {s}) := hA.connectedFibres s
  have : ConnectedSpace (f.base ⁻¹' {s}) := isConnected_iff_connectedSpace.mp hconn
  have h1 : _root_.IsConnected (Set.univ : Set (f.fiber s)) := by
    have h := (isConnected_univ (α := f.base ⁻¹' {s})).image _ (f.fiberHomeo
      s).symm.continuous.continuousOn
    rwa [Set.image_univ_of_surjective (f.fiberHomeo s).symm.surjective] at h
  exact h1
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs.abelianSchemePropertyBundle_fibreStr
end ProofImplementation
