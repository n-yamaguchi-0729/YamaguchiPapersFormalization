/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.ExtensionMonodromy
import EtaleFundamentalGroups.Cohomology.IntegerFiberSections
import EtaleFundamentalGroups.Cohomology.MonodromySections

/-!
# Vanishing detected by the actual fundamental-group character

For finite constant abelian coefficients on a connected scheme, the character
of an actual extension is trivial precisely when its derived extension class
vanishes. This uses descent of a fixed monodromy point to a genuine global
section, followed by the splitting obtained from its integral multiples.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits EtaleCohomology
open scoped FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X] (A : AddCommGrpCat.{u}) [Finite A]
  {E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
  (p : E ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)))
  (h : i ≫ p = 0) (hs : (ShortComplex.mk i p h).ShortExact)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The character of an actual extension vanishes exactly when its actual
degree-one étale extension class vanishes. No regularity, finite type,
properness, or characteristic hypothesis is required. -/
theorem extensionMonodromyCharacter_eq_one_iff :
    let : TopologicalSpace (Multiplicative A) := ⊥
    extensionMonodromyCharacter A i p h hs (integerUnitSection X) ξ = 1 ↔
      hs.extClass = 0 := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  let T := extensionMonodromyTorsor A i p h hs (integerUnitSection X) ξ
  have := extensionMonodromy_commutes A i p h hs (integerUnitSection X) ξ
  let M := extensionMonodromy A i p h hs (integerUnitSection X) ξ
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) M.obj.V := M.property
  let F : EtaleFiniteLocallyConstantSetSheaf X :=
    ⟨extensionFiber (ShortComplex.mk i p h) (integerUnitSection X),
      extensionFiber_isFiniteLocallyConstant _ _ hs
        (constantAbelian_isFiniteLocallyConstant X A)⟩
  rw [extClass_eq_zero_iff_integerFiber_section]
  rw [nonempty_globalSection_iff_monodromy_fixed ξ F]
  change torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) (Classical.choice T.nonempty) = 1 ↔
    ∃ q : M.obj.V, ∀ g : Aut (FiniteEtale.fiber ξ), g • q = q
  constructor
  · intro hc
    exact ⟨_, (torsorCharacter_eq_one_iff _).mp hc⟩
  · rintro ⟨q, hq⟩
    exact (torsorCharacter_eq _ q).trans ((torsorCharacter_eq_one_iff q).mpr hq)

end EtaleFundamentalGroups.Cohomology
