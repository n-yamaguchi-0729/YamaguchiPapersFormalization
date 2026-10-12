/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
import Nyll.JacobianVarieties.Kummer.CohomologyPullbackCharacters

/-! # Injectivity of actual finite H¹ restriction to the function field -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Cohomology JacobianVarieties.Kummer

namespace AnabelianGeometry.WeightFiltration

/-- On a normal integral scheme, the actual generic-point pullback on finite
constant-coefficient H¹ is injective. -/
theorem finiteH1Pullback_genericPoint_injective
    (X : Scheme) [IsIntegral X] [IsNormalIntegral X]
    (Ω : Type) [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
    (A : AddCommGrpCat.{0}) [Finite A] :
    Function.Injective (constantCohomologyPullback
      (X.fromSpecStalk (genericPoint X)) A 1) := by
  intro a b hab
  let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  apply finiteH1_ext_genericFieldAction X Ω A a b
  intro σ
  have h := congrArg (fun c => h1Character A η c
    (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)) hab
  rw [h1Character_constantCohomologyPullback,
    h1Character_constantCohomologyPullback] at h
  exact h

end AnabelianGeometry.WeightFiltration
