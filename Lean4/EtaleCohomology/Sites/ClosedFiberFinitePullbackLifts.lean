/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import EtaleCohomology.Sites.ClosedFiberFiniteLiftCover
import EtaleCohomology.Sites.PullbackSections
import EtaleCohomology.Sites.SheafFunctors
import EtaleCohomology.Sites.ZariskiRestriction
import SchemeTheory.Etale.LocalFactorOpenCover
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Actual Zariski local lifts on the finite refinement

The finite refinement of the actual closed-unit lift cover locally factors
through individual members of the original étale cover. Pulling their given
sections through these factors produces actual sections of inverse image
on Zariski neighborhoods of the finite source. The equations against the
original unit are preserved by its naturality.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace EtaleCohomology

/-- A closed-fiber section acquires actual Zariski local preimages after
a finite surjective refinement of the original scheme. -/
theorem exists_finite_refinement_zariski_pullback_lifts
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (t : ((etalePushforward i Λ).obj ((etalePullback i Λ).obj F)).obj.obj
      (op (Scheme.Etale.mk (𝟙 X)))) :
    let G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) :=
      (etalePushforward i Λ).obj ((etalePullback i Λ).obj F)
    let η : F ⟶ G := (etalePullbackPushforwardAdjunction i Λ).unit.app F
    ∃ (Y : Scheme.{u}) (q : Y ⟶ X), IsFinite q ∧ Surjective q ∧
      ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧
        ∃ b : ((etalePullback q Λ).obj F).obj.obj (op ((zariskiToEtale Y).obj W)),
          ((etalePullback q Λ).map η).hom.app (op ((zariskiToEtale Y).obj W)) b =
            ((etalePullback q Λ).obj G).obj.map
              (MorphismProperty.Over.homMk
                (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
                (A := (zariskiToEtale Y).obj W) (B := Scheme.Etale.mk (𝟙 Y))
                W.ι (Category.comp_id W.ι)).op
              (etalePullbackGlobalSectionsMap q Λ G t) := by
  intro G η
  obtain ⟨V, g, a, Y, q, ha, _, hFinite, hSurjective, hLocal⟩ :=
    exists_finite_refinement_closed_unit_lifts i Λ F t
  refine ⟨Y, q, hFinite, hSurjective, ?_⟩
  intro y
  obtain ⟨W, hyW, x, l, hl⟩ :=
    Scheme.Hom.ZariskiLocallyFactorsThrough.exists_sigma_factor
      (fun x : X => (V x).left) (fun x : X => (g x).left) q hLocal y
  have hg : (g x).left = (V x).hom := by
    have hw : (g x).left ≫ 𝟙 X = (V x).hom := (g x).w
    exact (Category.comp_id (g x).left).symm.trans hw
  have hl' : l ≫ (V x).hom = W.ι ≫ q := by
    rw [← hg]
    exact hl
  let U : Y.Etale := (zariskiToEtale Y).obj W
  let b : ((etalePullback q Λ).obj F).obj.obj (op U) :=
    etalePullbackSectionMap q Λ F (U := U) (V := V x) l hl' (a x)
  refine ⟨W, hyW, b, ?_⟩
  exact etalePullbackSectionMap_local_lift q Λ η (U := U) (V := V x)
    (g x) l hl' (a x) t (ha x)

end EtaleCohomology
