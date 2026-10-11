/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.UnibranchOpenSurjective
import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointOpenFull

/-!
# Fundamental group surjections for geometrically unibranch schemes

Both original conclusions of Stacks Project, Lemma 58.10.7 (Tag 0BQI),
for arbitrary irreducible geometrically unibranch schemes. The hypotheses
use the normalization definition at every actual scheme stalk. Both maps
are the existing fundamentalGroupHom attached to the literal open immersion
and the literal generic residue-field morphism.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Every nonempty open and the generic point of an irreducible geometrically
unibranch scheme induce surjections on the actual étale fundamental groups. -/
@[stacks 0BQI]
theorem irreducible_geometricallyUnibranch_fundamentalGroup_surjections
    {X : Scheme.{u}} [IrreducibleSpace X]
    (hX : ∀ x : X, IsLocalRing.IsGeometricallyUnibranch (X.presheaf.stalk x)) :
    (∀ (U : X.Opens), (U : Set X).Nonempty →
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (ξ : Spec (.of Ω) ⟶ U.toScheme),
        Function.Surjective (fundamentalGroupHom U.ι ξ)) ∧
    (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (ξ : Spec (.of Ω) ⟶ Spec (X.residueField (genericPoint X))),
      Function.Surjective
        (fundamentalGroupHom (X.fromSpecResidueField (genericPoint X)) ξ)) := by
  constructor
  · intro U hU Ω _ _ ξ
    exact fundamentalGroupHom_surjective_nonemptyOpen_of_geometricallyUnibranch hX U hU ξ
  · intro Ω _ _ ξ
    exact genericPoint_fundamentalGroupHom_surjective_of_nonemptyOpenFull
      (fun U hU => (nonemptyOpenPullbackFullyFaithful_of_geometricallyUnibranch hX U hU).full) ξ

end AlgebraicGeometry.FiniteEtale
