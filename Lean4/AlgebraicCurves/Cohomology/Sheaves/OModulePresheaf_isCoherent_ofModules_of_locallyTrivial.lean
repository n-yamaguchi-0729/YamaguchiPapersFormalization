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

import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Finiteness.Defs
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_finite_sections_of_locallyTrivial

/-!
Coherence of the module presheaf associated to a locally trivial module sheaf.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_isCoherent_ofModules_of_locallyTrivial

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.OModulePresheaf.isCoherent_ofModules_of_locallyTrivial
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
    (htriv : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit
        U.toScheme.ringCatSheaf)) :
    (OModulePresheaf.ofModules π M).IsCoherent :=
  fun U => Scheme.Modules.finite_sections_of_locallyTrivial M htriv U
end OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation
