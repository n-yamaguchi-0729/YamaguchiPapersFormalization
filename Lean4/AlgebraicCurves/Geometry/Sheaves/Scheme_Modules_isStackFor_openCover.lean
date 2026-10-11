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

import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_toDescentData_map_bijective_of_openCover
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_toDescentData_essSurj_of_openCover

/-!
# Scheme Modules is Stack For open Cover
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isStackFor_openCover

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.isStackFor_openCover (Y : Scheme.{u}) (𝒰 :
  Y.OpenCover) :
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).IsStackFor
      (Presieve.ofArrows 𝒰.X 𝒰.f) := by
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  set F := ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData 𝒰.f with
    hF
  have hcov : ∀ y : Y, ∃ i, y ∈ Set.range (𝒰.f i).base := fun y => ⟨𝒰.idx y, 𝒰.covers y⟩
  have : F.Faithful :=
    ⟨fun {L₁ L₂} => (Scheme.Modules.toDescentData_map_bijective_of_openCover 𝒰.f hcov L₁ L₂).1⟩
  have : F.Full :=
    ⟨fun {L₁ L₂} φ => ⟨_, ((Scheme.Modules.toDescentData_map_bijective_of_openCover 𝒰.f hcov L₁
      L₂).2 φ).choose_spec⟩⟩
  have : F.EssSurj := Scheme.Modules.toDescentData_essSurj_of_openCover 𝒰.f hcov
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isStackFor_openCover
end ProofImplementation
