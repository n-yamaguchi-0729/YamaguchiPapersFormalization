/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme

/-!
# The zero ideal after postcomposition

The zero-scheme ideal of a postcomposed module section is contained in the zero-scheme
ideal of the original section.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_zeroSchemeIdeal_comp_le

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace ZSCompSol

open AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M M' : X.Modules}

theorem restrictFunctor_map_app {U : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (f : M ⟶ M')
    (W : U.Opens) : ((Scheme.Modules.restrictFunctor i).map f).app W = f.app (i ''ᵁ W) := rfl

theorem restrictSection_comp (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') (U : X.Opens) :
    restrictSection (s ≫ f) U = ((Scheme.Modules.restrictFunctor U.ι).map f).app ⊤
        (restrictSection s U) := by
  rfl

theorem coeff_comp (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') (U : X.Opens)
    (φ : M'.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) :
    coeff (s ≫ f) U φ = coeff s U ((Scheme.Modules.restrictFunctor U.ι).map f ≫ φ) := by
  rfl

theorem coeffIdeal_comp_le (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') (U : X.Opens) :
    coeffIdeal (s ≫ f) U ≤ coeffIdeal s U := by
  apply Ideal.span_mono
  rintro _ ⟨φ, rfl⟩
  exact ⟨(Scheme.Modules.restrictFunctor U.ι).map f ≫ φ, (coeff_comp s f U φ).symm⟩

end ZSCompSol

theorem _root_.AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal_comp_le
    {X : Scheme.{u}} {M M' : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') :
    Scheme.Modules.zeroSchemeIdeal (s ≫ f) ≤ Scheme.Modules.zeroSchemeIdeal s := by
  apply Scheme.Modules.le_zeroSchemeIdeal
  intro J hJ
  exact Scheme.Modules.zeroSchemeIdeal_le fun U => (ZSCompSol.coeffIdeal_comp_le s f U.1).trans
      (hJ U)
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_zeroSchemeIdeal_comp_le
end ProofImplementation
