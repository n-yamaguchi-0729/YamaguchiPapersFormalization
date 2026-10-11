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

import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Nyll.SchemeTheory.Modules.LocallyTrivialSectionsLocalization

/-!
Quasicoherence of the section presheaf of a locally trivial scheme module.
-/

/-! Quasicoherence of the presheaf associated to a locally trivial module. -/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
    (htriv : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit
        U.toScheme.ringCatSheaf)) :
    (OModulePresheaf.ofModules π M).IsQuasicoherent :=
  fun U f => Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial M htriv U f
end OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation
