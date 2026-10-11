/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.FiniteRefinementCompatibleLift
import EtaleCohomology.Sites.FiniteSurjectiveDescent
import EtaleCohomology.Sites.ProperLocalSections
import EtaleCohomology.Sites.PullbackSections
import EtaleCohomology.Sites.PushforwardGlobalSections
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Henselian

/-!
# Étale H⁰ proper base change over a henselian local ring

For any proper scheme over a henselian local ring, restriction to its actual
closed fiber is bijective on global sections of every étale module sheaf.
The section on a finite surjective refinement satisfies the actual Čech
equation and descends by finite-surjection descent. Naturality and faithful
pullback identify its image with the original closed-fiber section.

There is no noetherian or torsion hypothesis. This is the degree-zero result;
positive-degree proper base change and Nagata compactification are separate.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- The actual closed-fiber adjunction unit is bijective on global sections
for a proper scheme over a henselian local ring and any étale module sheaf. -/
theorem etaleClosedFiber_unit_globalSections_bijective
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let i : pullback f r ⟶ X := pullback.fst f r
    Function.Bijective (((etalePullbackPushforwardAdjunction i Λ).unit.app F).hom.app
      (op (Scheme.Etale.mk (𝟙 X)))) := by
  intro r i
  refine ⟨etaleClosedFiber_unit_globalSections_injective R f Λ F, ?_⟩
  let G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) :=
    (etalePushforward i Λ).obj ((etalePullback i Λ).obj F)
  let η : F ⟶ G := (etalePullbackPushforwardAdjunction i Λ).unit.app F
  intro t
  obtain ⟨Y, q, hfinite, hsurj, a, ha, hcech⟩ :=
    exists_finite_refinement_compatible_global_pullback_lift R f Λ F t
  have : IsFinite q := hfinite
  have : Surjective q := hsurj
  obtain ⟨b, hb, _⟩ := existsUnique_globalSections_lift_of_finite_cech_compatible q Λ F a hcech
  refine ⟨b, ?_⟩
  apply etaleFiniteSurjective_globalSections_injective q Λ G
  have hn := etalePullbackSectionMap_naturality q Λ η
    (U := Scheme.Etale.mk (𝟙 Y)) (V := Scheme.Etale.mk (𝟙 X)) q
    ((Category.comp_id q).trans (Category.id_comp q).symm)
  exact (ConcreteCategory.congr_hom hn b).symm.trans
    ((congrArg (((etalePullback q Λ).map η).hom.app (op (Scheme.Etale.mk (𝟙 Y)))) hb).trans ha)

/-- Restriction to the actual closed fiber is bijective on étale H⁰ for every
module sheaf on a proper scheme over a henselian local ring. -/
theorem etaleClosedFiber_globalSections_bijective
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let i : pullback f r ⟶ X := pullback.fst f r
    Function.Bijective (etalePullbackGlobalSectionsMap i Λ F) := by
  intro r i
  rw [← etalePullbackGlobalSectionsMap_eq_unit]
  exact (ConcreteCategory.bijective_of_isIso
    (etalePushforwardGlobalSectionsIso i Λ ((etalePullback i Λ).obj F)).hom).comp
      (etaleClosedFiber_unit_globalSections_bijective R f Λ F)

end EtaleCohomology
