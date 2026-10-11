/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_ringHom_functionField_germ_eq_of_base_genericPoint_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.FunctionField

/-!
# exists ring Hom function Field germ eq of base generic Point eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_ringHom_functionField_germ_eq_of_base_genericPoint_eq

open CategoryTheory AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.exists_ringHom_functionField_germ_eq_of_base_genericPoint_eq
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    (hf : f.base (genericPoint Y) = genericPoint X) :
    ∃ δ : ↑X.functionField →+* ↑Y.functionField,
      ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Y ∈ f ⁻¹ᵁ U)
        (sec : X.presheaf.obj (Opposite.op U)),
        δ ((X.presheaf.germ U (genericPoint X) hU).hom sec) =
          (Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hU').hom ((f.app U).hom sec) := by
  have hspec : f.base (genericPoint Y) ⤳ genericPoint X := hf ▸ specializes_rfl
  refine ⟨(X.presheaf.stalkSpecializes hspec ≫ f.stalkMap (genericPoint Y)).hom, ?_⟩
  intro U hU hU' sec
  have h1 := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hU hspec
  have h2 := Scheme.Hom.germ_stalkMap f U (genericPoint Y) hU'
  have h3 : X.presheaf.germ U (genericPoint X) hU ≫ X.presheaf.stalkSpecializes hspec ≫
      f.stalkMap (genericPoint Y) = f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hU' := by
    rw [← Category.assoc, h1]
    exact h2
  change (X.presheaf.germ U (genericPoint X) hU ≫ X.presheaf.stalkSpecializes hspec ≫
      f.stalkMap (genericPoint Y)).hom sec = (f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y)
        hU').hom sec
  rw [h3]
end exists_ringHom_functionField_germ_eq_of_base_genericPoint_eq
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
