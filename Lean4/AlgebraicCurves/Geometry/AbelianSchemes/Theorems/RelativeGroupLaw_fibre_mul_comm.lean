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

/-!
# Relative Group Law fibre mul comm
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs.RelativeGroupLaw_fibre_mul_comm

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem _root_.GoodReductionJacobian.RelativeGroupLaw.fibre_mul_comm
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (s : (Spec (CommRingCat.of R) : Scheme.{u}))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (RelativeGroupLaw.baseResidueField s)))
    (x y : SchemeHomOver t' (RelativeGroupLaw.fibreStr f s)) :
    (G.fibre s).mul t' x y = (G.fibre s).mul t' y x := by
  rw [RelativeGroupLaw.fibre_mul, RelativeGroupLaw.fibre_mul, hcomm]
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs.RelativeGroupLaw_fibre_mul_comm
end ProofImplementation
