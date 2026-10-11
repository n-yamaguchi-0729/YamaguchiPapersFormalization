/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
public import Nyll.SchemeTheory.FiniteEtale.Algebra.HenselianBaseChange

/-!
# Finite étale covers of a Henselian pair

The affine equivalence identifies pullback of finite étale covers with
tensor-product base change of finite étale algebras. The algebraic Henselian
equivalence therefore gives Stacks Project, Tag 09ZS. The public statement
uses the canonical intersection of the finite and étale morphism properties.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleInfStableUnderBaseChangeHenselian :
    MorphismProperty.IsStableUnderBaseChange
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- Pullback from `Spec R` to `Spec (R / I)` is an equivalence on finite
étale covers whenever `(R, I)` is a Henselian pair. -/
@[stacks 09ZS]
theorem pullback_isEquivalence_of_henselian
    {R : Type u} [CommRing R] (I : Ideal R) [HenselianRing R I] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I))))).IsEquivalence :=
  (pullback_specMap_isEquivalence_iff R (R ⧸ I)).mpr
    (CommAlgCat.FiniteEtale.baseChange_isEquivalence_of_henselian I)

end AlgebraicGeometry.FiniteEtale
