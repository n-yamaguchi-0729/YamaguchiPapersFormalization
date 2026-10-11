/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField
import Nyll.SchemeTheory.FunctionFields.Functoriality

/-!
# The actual geometric action underlying the Galois function-field action

The function-field automorphism defined using generic geometric fibers is
exactly the pullback on rational functions of the actual deck transformation.
In particular it intertwines the pullback on global sections with their
inclusion in the function field. This identifies the actions used by affine
normalization and by the canonical Galois-group comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]

/-- The canonical field action restricts to the literal pullback on the
coordinate ring of the cover. -/
theorem finiteEtaleAutFunctionFieldAlgEquiv_germToFunctionField
    (Y : FiniteEtale X) [IsConnected Y] (sigma : Aut Y) :
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
    let : Nonempty (⊤ : Y.left.Opens) :=
      ⟨⟨Classical.choice (inferInstance : Nonempty Y.left), trivial⟩⟩
    ∀ a : Γ(Y.left, ⊤),
      finiteEtaleAutFunctionFieldAlgEquiv Y sigma (Y.left.germToFunctionField ⊤ a) =
        Y.left.germToFunctionField ⊤ (sigma.hom.left.appTop a) := by
  intro hIntegral hAlgebra hTop a
  have h := sigma.hom.left.functionFieldMap_comp_germToFunctionField_top
    sigma.hom.left.surjective.denseRange
  have ha := DFunLike.congr_fun h a
  have he := finiteEtaleAutFunctionFieldAlgEquiv_eq_functionFieldMap Y sigma
  exact (DFunLike.congr_fun he (Y.left.germToFunctionField ⊤ a)).trans ha

end EtaleFundamentalGroups
