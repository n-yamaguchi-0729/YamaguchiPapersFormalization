/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.RepresenterAction
import EtaleCohomology.Sites.EtaleRestriction
import SchemeTheory.Descent.AffineActionCoordinates
import SchemeTheory.Descent.AffineAlgebraCoaction
import SchemeTheory.Descent.AffineCocycle
import SchemeTheory.Descent.AlgebraCoaction
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Algebra descent data supplied by an affine local representer

An actual representer on an affine étale cover supplies the geometric action.
Tensor coordinates then construct the algebra overlap equivalence and prove
its diagonal and full cocycle laws. These laws are derived from the original
sheaf's universal section, with no assumed descent comparison.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Algebra.Descent
open scoped TensorProduct

namespace EtaleCohomology

variable (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
variable [Etale (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
  [Etale (Spec.map (CommRingCat.ofHom (algebraMap B C)))]
variable (G : Sheaf (Spec (.of R)).smallEtaleTopology (Type u))

/-- The literal spectrum morphism as an object of the cover's small étale site. -/
abbrev affineRepresenterEtale : (Spec (.of B)).Etale :=
  MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) (Spec.map (CommRingCat.ofHom
    (algebraMap B C)))
    inferInstance


variable (h : ((etalePostcompose (Spec.map (CommRingCat.ofHom (algebraMap R B)))).op ⋙
    G.obj).RepresentableBy
  (affineRepresenterEtale B C))

include h


/-- The actual overlap isomorphism of the affine local representer, in tensor coordinates. -/
def affineRepresenterOverlapIso :
    Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B)) :=
  affinePullbackOverlapIso R B C (pullbackActionOverlapCongrIso (Spec.map (CommRingCat.ofHom
    (algebraMap R
    B))) (Spec.map (CommRingCat.ofHom (algebraMap B C))) (Spec.map (CommRingCat.ofHom
      (algebraMap R C)))
    (specMap_tower R B C) (representerAction (Spec.map (CommRingCat.ofHom (algebraMap R B))) G
    (affineRepresenterEtale B C) h) (representerAction_over (Spec.map (CommRingCat.ofHom
      (algebraMap R B))) G
    (affineRepresenterEtale B C) h) (representerAction_unit (Spec.map (CommRingCat.ofHom
      (algebraMap R B))) G
    (affineRepresenterEtale B C) h) (representerAction_assoc (Spec.map (CommRingCat.ofHom
      (algebraMap R B))) G
    (affineRepresenterEtale B C) h))

/-- Both coordinates over the cover's self-pullback are preserved. -/
lemma affineRepresenterOverlapIso_base :
    (affineRepresenterOverlapIso R B C G h).hom ≫
        Spec.map (CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom) =
      Spec.map (CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom) := by
  apply affinePullbackOverlapIso_base R B C (pullbackActionOverlapCongrIso (Spec.map
    (CommRingCat.ofHom
    (algebraMap R B))) (Spec.map (CommRingCat.ofHom (algebraMap B C))) (Spec.map (CommRingCat.ofHom
    (algebraMap R C))) (specMap_tower R B C) (representerAction (Spec.map (CommRingCat.ofHom
      (algebraMap R
    B))) G (affineRepresenterEtale B C) h) (representerAction_over (Spec.map
      (CommRingCat.ofHom (algebraMap R
    B))) G (affineRepresenterEtale B C) h) (representerAction_unit (Spec.map
      (CommRingCat.ofHom (algebraMap R
    B))) G (affineRepresenterEtale B C) h) (representerAction_assoc (Spec.map
      (CommRingCat.ofHom (algebraMap R
    B))) G (affineRepresenterEtale B C) h))
  · rw [← Category.assoc]
    refine (congrArg (fun k => k ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)))
      (pullbackActionOverlapCongrIso_fst _ _ _ _ _ _ _ _)).trans ?_
    exact pullbackActionCongr_over (Spec.map (CommRingCat.ofHom (algebraMap R B))) (Spec.map
      (CommRingCat.ofHom (algebraMap B C))) (Spec.map (CommRingCat.ofHom (algebraMap R C)))
        (specMap_tower R B
      C) (representerAction (Spec.map (CommRingCat.ofHom (algebraMap R B))) G
        (affineRepresenterEtale B C) h)
      (representerAction_over (Spec.map (CommRingCat.ofHom (algebraMap R B))) G
        (affineRepresenterEtale B C)
      h)
  · exact pullbackActionOverlapCongrIso_snd _ _ _ _ _ _ _ _

/-- The universal section's unit law supplies diagonal normalization. -/
lemma affineRepresenterOverlapIso_diagonal :
    Spec.map (CommRingCat.ofHom (tensorTargetDiagonal R B C).toRingHom) ≫
        (affineRepresenterOverlapIso R B C G h).hom =
      Spec.map (CommRingCat.ofHom (tensorSourceDiagonal R B C).toRingHom) :=
  affinePullbackOverlapIso_diagonal R B C (pullbackActionOverlapCongrIso (Spec.map
    (CommRingCat.ofHom
    (algebraMap R B))) (Spec.map (CommRingCat.ofHom (algebraMap B C))) (Spec.map (CommRingCat.ofHom
    (algebraMap R C))) (specMap_tower R B C) (representerAction (Spec.map (CommRingCat.ofHom
      (algebraMap R
    B))) G (affineRepresenterEtale B C) h) (representerAction_over (Spec.map
      (CommRingCat.ofHom (algebraMap R
    B))) G (affineRepresenterEtale B C) h) (representerAction_unit (Spec.map
      (CommRingCat.ofHom (algebraMap R
    B))) G (affineRepresenterEtale B C) h) (representerAction_assoc (Spec.map
      (CommRingCat.ofHom (algebraMap R
    B))) G (affineRepresenterEtale B C) h))
    (pullbackActionOverlapCongrIso_diagonal (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map
      (CommRingCat.ofHom (algebraMap B C))) (Spec.map (CommRingCat.ofHom (algebraMap R C)))
        (specMap_tower R B
      C) (representerAction (Spec.map (CommRingCat.ofHom (algebraMap R B))) G
        (affineRepresenterEtale B C) h)
      (representerAction_over (Spec.map (CommRingCat.ofHom (algebraMap R B))) G
        (affineRepresenterEtale B C)
      h) (representerAction_unit (Spec.map (CommRingCat.ofHom (algebraMap R B))) G
        (affineRepresenterEtale B
      C) h) (representerAction_assoc (Spec.map (CommRingCat.ofHom (algebraMap R B))) G
        (affineRepresenterEtale
      B C) h))

/-- The extracted action is the representer's actual geometric action in the changed coordinates. -/
lemma affineRepresenterOverlapIso_action :
    affineOverlapAction R B C (affineRepresenterOverlapIso R B C G h) =
      pullbackActionCongr (Spec.map (CommRingCat.ofHom (algebraMap R B))) (Spec.map
        (CommRingCat.ofHom
        (algebraMap B C))) (Spec.map (CommRingCat.ofHom (algebraMap R C))) (specMap_tower R B C)
        (representerAction (Spec.map (CommRingCat.ofHom (algebraMap R B))) G
          (affineRepresenterEtale B C) h)
        := by
  rw [affineRepresenterOverlapIso, affinePullbackOverlapIso_action]
  exact pullbackActionOverlapCongrIso_fst _ _ _ _ _ _ _ _

/-- The genuine triple-pullback action law of the local representer. -/
lemma affineRepresenterOverlapIso_actionLaw :
    pullbackActionStep (Spec.map (CommRingCat.ofHom (algebraMap R B))) (Spec.map (CommRingCat.ofHom
      (algebraMap R C)))
        (affineOverlapAction R B C (affineRepresenterOverlapIso R B C G h))
        (affineOverlapAction_base R B C _ (affineRepresenterOverlapIso_base R B C G h)) ≫
          affineOverlapAction R B C (affineRepresenterOverlapIso R B C G h) =
      pullbackSkipMiddle (Spec.map (CommRingCat.ofHom (algebraMap R B))) (Spec.map
        (CommRingCat.ofHom
        (algebraMap R C))) ≫
        affineOverlapAction R B C (affineRepresenterOverlapIso R B C G h) := by
  simpa only [affineRepresenterOverlapIso_action] using
    pullbackActionCongr_assoc (Spec.map (CommRingCat.ofHom (algebraMap R B))) (Spec.map
      (CommRingCat.ofHom
      (algebraMap B C))) (Spec.map (CommRingCat.ofHom (algebraMap R C))) (specMap_tower R B C)
      (representerAction (Spec.map (CommRingCat.ofHom (algebraMap R B))) G
        (affineRepresenterEtale B C) h)
      (representerAction_over (Spec.map (CommRingCat.ofHom (algebraMap R B))) G
        (affineRepresenterEtale B C)
      h) (representerAction_assoc (Spec.map (CommRingCat.ofHom (algebraMap R B))) G
        (affineRepresenterEtale B
      C) h)

/-- The algebra overlap equivalence supplied by the actual affine local representer. -/
def affineRepresenterAlgEquiv : C ⊗[R] B ≃ₐ[B] B ⊗[R] C :=
  affineOverlapAlgEquiv R B C (affineRepresenterOverlapIso R B C G h)
    (affineRepresenterOverlapIso_base R B C G h)

/-- The constructed algebra overlap is normalized on the diagonal. -/
lemma affineRepresenterAlgEquiv_diagonal :
    (tensorTargetDiagonal R B C).comp (affineRepresenterAlgEquiv R B C G h).toAlgHom =
      tensorSourceDiagonal R B C :=
  affineOverlapAlgEquiv_diagonal R B C _ (affineRepresenterOverlapIso_base R B C G h)
    (affineRepresenterOverlapIso_diagonal R B C G h)

/-- The full tensor cocycle follows from the original sheaf's representing equivalence. -/
lemma affineRepresenterAlgEquiv_cocycle :
    tensorCocycleLeft R B C (affineRepresenterAlgEquiv R B C G h) =
      tensorCocycleRight R B C (affineRepresenterAlgEquiv R B C G h) :=
  affineOverlapAlgEquiv_cocycle_of_actionLaw R B C _
    (affineRepresenterOverlapIso_base R B C G h)
    (affineRepresenterOverlapIso_actionLaw R B C G h)

end EtaleCohomology
