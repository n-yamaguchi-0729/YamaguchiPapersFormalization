/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitEventualFaithfulness
import Nyll.SchemeTheory.FiniteEtale.InverseLimitEquality
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Faithfulness of the finite etale model localization

Geometric equality descent for the original inverse limit supplies eventual
equality at an actual stage. The categorical fraction argument then makes
the comparison from the cartesian model localization faithful.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteEtale.InverseLimitModel

universe u

variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable (F : Iᵒᵖ ⥤ Scheme.{u}) (s : Cone F) (hs : IsLimit s)
variable [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (F.map h)]
variable [∀ i : Iᵒᵖ, CompactSpace (F.obj i)]

include hs

/-- Two actual model arrows which agree at the limit agree after a
cartesian refinement of their original source. -/
theorem exists_refinement_map_eq
    {A B : InverseLimitModel F} (f g : A ⟶ B)
    (hfg : (baseChange F s).map f = (baseChange F s).map g) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ A.right),
      refinementHom F A h ≫ f = refinementHom F A h ≫ g :=
  exists_refinement_map_eq_of_stage_equality F s
    (exists_inverse_limit_stage_map_eq F s hs) f g hfg

/-- The actual comparison from the model localization is faithful, by
geometric eventual equality and the concrete fraction criterion. -/
theorem localizedBaseChange_faithful : (localizedBaseChange F s).Faithful :=
  localizedBaseChange_faithful_of_stage_equality F s
    (exists_inverse_limit_stage_map_eq F s hs)

end AlgebraicGeometry.FiniteEtale.InverseLimitModel
