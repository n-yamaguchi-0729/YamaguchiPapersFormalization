/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import EtaleCohomology.Sites.CechSections
import EtaleCohomology.Sites.ClosedFiberPullbackGluing
import EtaleCohomology.Sites.ProperPullbackClosedUnitInjective
import EtaleCohomology.Sites.PullbackComposition
import EtaleCohomology.Sites.PullbackSections
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The finite-refinement lift satisfies the actual Čech equation

Pulling the original closed-fiber unit to the self-fiber product stays
injective on global sections. Naturality and the actual Čech equation for
the pulled-back target section therefore force compatibility of the
constructed lift. All maps use the original chosen inverse images.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem cech_compatible_of_closedUnit_lift
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (q : Y ⟶ X) [IsFinite q] (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let i : pullback f r ⟶ X := pullback.fst f r
    let G := (etalePushforward i Λ).obj ((etalePullback i Λ).obj F)
    let η : F ⟶ G := (etalePullbackPushforwardAdjunction i Λ).unit.app F
    ∀ (t : G.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
      (a : ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y)))),
      ((etalePullback q Λ).map η).hom.app (op (Scheme.Etale.mk (𝟙 Y))) a =
          etalePullbackGlobalSectionsMap q Λ G t →
        etaleCechFirstSectionsMap q Λ F a = etaleCechSecondSectionsMap q Λ F a := by
  intro r i G η t a ha
  let W : Scheme.{u} := pullback q q
  let W₀ : W.Etale := Scheme.Etale.mk (𝟙 W)
  let Y₀ : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let p₁ : W ⟶ Y := pullback.fst q q
  let p₂ : W ⟶ Y := pullback.snd q q
  let g : W ⟶ X := p₂ ≫ q
  let Fq := (etalePullback q Λ).obj F
  let Gq := (etalePullback q Λ).obj G
  let μ : Fq ⟶ Gq := (etalePullback q Λ).map η
  let F₁ := (etalePullback p₁ Λ).obj Fq
  let G₁ := (etalePullback p₁ Λ).obj Gq
  let F₂ := (etalePullback p₂ Λ).obj Fq
  let G₂ := (etalePullback p₂ Λ).obj Gq
  let μq : Fq.obj.obj (op Y₀) ⟶ Gq.obj.obj (op Y₀) := μ.hom.app (op Y₀)
  let μ₁ : F₁.obj.obj (op W₀) ⟶ G₁.obj.obj (op W₀) :=
    ((etalePullback p₁ Λ).map μ).hom.app (op W₀)
  let μ₂ : F₂.obj.obj (op W₀) ⟶ G₂.obj.obj (op W₀) :=
    ((etalePullback p₂ Λ).map μ).hom.app (op W₀)
  let V := sheafToPresheaf W.smallEtaleTopology (ModuleCat.{u} Λ)
  let eF := (V.mapIso ((etalePullbackCompIso p₂ q Λ).app F)).app (op W₀)
  let eG := (V.mapIso ((etalePullbackCompIso p₂ q Λ).app G)).app (op W₀)
  let μg : ((etalePullback g Λ).obj F).obj.obj (op W₀) ⟶
      ((etalePullback g Λ).obj G).obj.obj (op W₀) :=
    ((etalePullback g Λ).map η).hom.app (op W₀)
  have hμg : Mono μg := (ModuleCat.mono_iff_injective μg).mpr
    (etalePullbackClosedFiberUnit_globalSections_injective R f g Λ F)
  have hn : μg ≫ eG.hom = eF.hom ≫ μ₂ :=
    congrArg (fun k : (etalePullback g Λ).obj F ⟶ G₂ => k.hom.app (op W₀))
      ((etalePullbackCompIso p₂ q Λ).hom.naturality η)
  have heq : μ₂ = eF.inv ≫ μg ≫ eG.hom := by
    rw [hn, eF.inv_hom_id_assoc]
  have hμ₂ : Mono μ₂ := by
    have hc : Mono (eF.inv ≫ μg ≫ eG.hom) :=
      mono_comp' (inferInstanceAs (Mono eF.inv))
        (mono_comp' hμg (inferInstanceAs (Mono eG.hom)))
    exact heq.symm ▸ hc
  let aF := etaleCechFirstSectionsMap q Λ F
  let aG := etaleCechFirstSectionsMap q Λ G
  let bF := etaleCechSecondSectionsMap q Λ F
  let bG := etaleCechSecondSectionsMap q Λ G
  let uF := etalePullbackGlobalSectionsMap p₁ Λ Fq
  let uG := etalePullbackGlobalSectionsMap p₁ Λ Gq
  let cF : F₁.obj.obj (op W₀) ⟶ F₂.obj.obj (op W₀) :=
    ((etaleCechPullbackIso q Λ).hom.app F).hom.app (op W₀)
  let cG : G₁.obj.obj (op W₀) ⟶ G₂.obj.obj (op W₀) :=
    ((etaleCechPullbackIso q Λ).hom.app G).hom.app (op W₀)
  have hc : μ₁ ≫ cG = cF ≫ μ₂ :=
    congrArg (fun k : F₁ ⟶ G₂ => k.hom.app (op W₀))
      ((etaleCechPullbackIso q Λ).hom.naturality η)
  have hp₁ : uF ≫ μ₁ = μq ≫ uG :=
    etalePullbackSectionMap_naturality p₁ Λ μ (U := W₀) (V := Y₀) p₁
      ((Category.comp_id p₁).trans (Category.id_comp p₁).symm)
  have hn₁ : aF ≫ μ₂ = μq ≫ aG := by
    change (uF ≫ cF) ≫ μ₂ = μq ≫ (uG ≫ cG)
    rw [Category.assoc, ← hc, ← Category.assoc, hp₁, Category.assoc]
  have hn₂ : bF ≫ μ₂ = μq ≫ bG :=
    etalePullbackSectionMap_naturality p₂ Λ μ (U := W₀) (V := Y₀) p₂
      ((Category.comp_id p₂).trans (Category.id_comp p₂).symm)
  apply (ModuleCat.mono_iff_injective μ₂).mp hμ₂
  have h₁ := congrArg (fun k : Fq.obj.obj (op Y₀) ⟶ G₂.obj.obj (op W₀) => k a) hn₁
  have h₂ := congrArg (fun k : Fq.obj.obj (op Y₀) ⟶ G₂.obj.obj (op W₀) => k a) hn₂
  have ht := congrArg (fun k : G.obj.obj (op (Scheme.Etale.mk (𝟙 X))) ⟶
      G₂.obj.obj (op W₀) => k t) (etaleCechSections_condition q Λ G)
  exact h₁.trans ((congrArg aG ha).trans
    (ht.trans ((congrArg bG ha).symm.trans h₂.symm)))

/-- The actual finite-surjective lift of a closed-fiber section satisfies
the two degree-zero Čech section maps, ready for finite descent. -/
theorem exists_finite_refinement_compatible_global_pullback_lift
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let i : pullback f r ⟶ X := pullback.fst f r
    let G := (etalePushforward i Λ).obj ((etalePullback i Λ).obj F)
    let η : F ⟶ G := (etalePullbackPushforwardAdjunction i Λ).unit.app F
    ∀ t : G.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
      ∃ (Y : Scheme.{u}) (q : Y ⟶ X), IsFinite q ∧ Surjective q ∧
        ∃ a : ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))),
          (((etalePullback q Λ).map η).hom.app (op (Scheme.Etale.mk (𝟙 Y))) a =
            etalePullbackGlobalSectionsMap q Λ G t) ∧
          etaleCechFirstSectionsMap q Λ F a = etaleCechSecondSectionsMap q Λ F a := by
  intro r i G η t
  obtain ⟨Y, q, hfinite, hsurj, a, ha⟩ :=
    exists_finite_refinement_global_pullback_lift R f Λ F t
  have : IsFinite q := hfinite
  exact ⟨Y, q, hfinite, hsurj, a, ha, cech_compatible_of_closedUnit_lift R f q Λ F t a ha⟩

end EtaleCohomology
