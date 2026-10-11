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

import AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import AlgebraicCurves.Geometry.Schemes.Smooth_isRegularLocalRing_stalk
import AlgebraicCurves.Geometry.Schemes.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import SchemeTheory.RingTheory.RegularLocalDomain

/-!
# Abelian Scheme Property Bundle is Integral of field
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace AbelianSchemePropertyBundle_isIntegral_of_field

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

theorem _root_.GoodReductionJacobian.AbelianSchemePropertyBundle.isIntegral_of_field {k : Type u}
  [Field k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)}
    (hJ : AbelianSchemePropertyBundle k f) : IsIntegral J := by
  have := hJ.smooth
  have : LocallyOfFiniteType f := inferInstance
  have : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  have : IsLocallyNoetherian J := LocallyOfFiniteType.isLocallyNoetherian f
  have : ConnectedSpace J := by
    rw [connectedSpace_iff_univ]
    have hc := hJ.connectedFibres default
    have heq : f.base ⁻¹' {(default : Spec (CommRingCat.of k))} = Set.univ := by
      ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rwa [heq] at hc
  exact
    AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk J
    fun x => by
      have := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) x
      exact IsRegularLocalRing.isDomain _
end AbelianSchemePropertyBundle_isIntegral_of_field
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation
