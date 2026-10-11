/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.Subcanonical
import SchemeTheory.FiniteEtale.Basic
import SchemeTheory.FiniteEtale.Geometry
import EtaleFundamentalGroups.FiniteEtale.GaloisCategory
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.FintypeCat

/-!
# Sheaves represented by finite étale covers

The existing category `FiniteEtale X` embeds fully faithfully into sheaves
of sets on the actual small étale site. The geometric stalk of the represented
sheaf is naturally isomorphic to the underlying finite set of EFG's geometric
fiber functor `FiniteEtale.fiber`.

The comparison uses the ordinary colimit definition of a stalk, the
map/pullback adjunction on slice categories, and the existing equivalence
between finite étale schemes over a separably closed field and finite sets.
No connectedness hypothesis is imposed on `X`.

This supplies the represented-sheaf and fiber comparison needed for
https://stacks.math.columbia.edu/tag/09Y8 . The converse representability
of finite locally constant sheaves is a subsequent step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u v

namespace EtaleCohomology

/-- A finite étale cover is an object of the small étale site. -/
def finiteEtaleToEtale (X : Scheme.{u}) : FiniteEtale X ⥤ X.Etale :=
  MorphismProperty.Over.changeProp X
    (P := show MorphismProperty Scheme.{u} from @IsFiniteEtale)
    (P' := show MorphismProperty Scheme.{u} from @Etale)
    (Q := ⊤) (Q' := ⊤) (fun _ _ _ hf => hf.toEtale) le_rfl

/-- The sheaf represented by a finite étale cover. -/
def finiteEtaleSheaf (X : Scheme.{u}) :
    FiniteEtale X ⥤ Sheaf X.smallEtaleTopology (Type u) :=
  finiteEtaleToEtale X ⋙ X.smallEtaleTopology.yoneda

/-- Maps of represented étale sheaves are exactly maps of finite étale covers. -/
def finiteEtaleSheafFullyFaithful (X : Scheme.{u}) :
    (finiteEtaleSheaf X).FullyFaithful :=
  (MorphismProperty.Comma.fullyFaithfulChangeProp
    (Functor.id Scheme.{u}) (Functor.fromPUnit X)
    (P := show MorphismProperty Scheme.{u} from @IsFiniteEtale)
    (P' := show MorphismProperty Scheme.{u} from @Etale)
    (Q := ⊤) (W := ⊤) (fun _ _ _ hf => hf.toEtale)).comp
      X.smallEtaleTopology.yonedaFullyFaithful

private def representableSheafFiberIso {C : Type v} [Category.{u} C]
    {J : GrothendieckTopology C} [J.Subcanonical] (Φ : J.Point.{u}) :
    J.yoneda ⋙ Φ.sheafFiber ≅ Φ.fiber := by
  change yoneda ⋙ Φ.presheafFiber ≅ Φ.fiber
  exact Functor.isoWhiskerRight (shrinkYonedaIsoYoneda (C := C)).symm Φ.presheafFiber ≪≫
    Φ.shrinkYonedaCompPresheafFiberIso

/-- The stalk of the represented sheaf consists of geometric points of the cover. -/
def finiteEtaleSheafStalkIso {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    finiteEtaleSheaf X ⋙ (Scheme.pointSmallEtale s).sheafFiber ≅
      finiteEtaleToEtale X ⋙ (Scheme.pointSmallEtale s).fiber :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (finiteEtaleToEtale X)
      (representableSheafFiberIso (Scheme.pointSmallEtale s))

private def finiteEtalePoint (Ω : Type u) [Field Ω] : FiniteEtale (Spec (.of Ω)) :=
  MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) (𝟙 (Spec (.of Ω)))
    (show IsFiniteEtale (𝟙 (Spec (.of Ω))) from ⟨⟩)

private def finiteEtaleSectionEquivPoints {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (W : FiniteEtale (Spec (.of Ω))) :
    (finiteEtalePoint Ω ⟶ W) ≃ W.left :=
  (FiniteEtale.equivFintypeCat Ω).fullyFaithfulFunctor.homEquiv.trans
    ((InducedCategory.homEquiv.trans TypeCat.homEquiv).trans
      (Equiv.funUnique (Spec (.of Ω)) W.left))

private def finiteEtaleGeometricHomEquivFiber {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) (W : FiniteEtale X) :
    (Over.mk s ⟶ (FiniteEtale.forget X).obj W) ≃ (FiniteEtale.fiber s).obj W := by
  let e : (Over.map s).obj (Over.mk (𝟙 (Spec (.of Ω)))) ≅ Over.mk s :=
    Over.isoMk (Iso.refl _) (by
      change (𝟙 _) ≫ s = (𝟙 _) ≫ s
      rfl)
  exact (Iso.homCongr e.symm (Iso.refl _)).trans
    (((Over.mapPullbackAdj s).homEquiv (Over.mk (𝟙 (Spec (.of Ω))))
      ((FiniteEtale.forget X).obj W)).trans
      (((FiniteEtale.forgetFullyFaithful (Spec (.of Ω))).homEquiv
        (X := finiteEtalePoint Ω) (Y := (FiniteEtale.pullback s).obj W)).symm.trans
        (finiteEtaleSectionEquivPoints ((FiniteEtale.pullback s).obj W))))

private lemma finiteEtaleGeometricHomEquivFiber_apply {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) (W : FiniteEtale X)
    (a : Over.mk s ⟶ (FiniteEtale.forget X).obj W) :
    finiteEtaleGeometricHomEquivFiber s W a =
      (pullback.lift (f := ((FiniteEtale.forget X).obj W).hom) (g := s)
        a.left (𝟙 (Spec (.of Ω)))
        ((Over.w a).trans (Category.id_comp s).symm)) (default : Spec (.of Ω)) := by
  dsimp only [finiteEtaleGeometricHomEquivFiber, finiteEtaleSectionEquivPoints,
    Equiv.trans_apply]
  simp only [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  change (pullback.lift (f := ((FiniteEtale.forget X).obj W).hom) (g := s)
    ((𝟙 (Spec (.of Ω))) ≫ a.left ≫ (𝟙 ((FiniteEtale.forget X).obj W).left))
      (𝟙 (Spec (.of Ω))) _) (default : Spec (.of Ω)) = _
  simp only [Category.id_comp, Category.comp_id]

private def finiteEtaleGeometricFiberIso {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    finiteEtaleToEtale X ⋙ (Scheme.pointSmallEtale s).fiber ≅
      FiniteEtale.fiber s ⋙ forget FintypeCat :=
  NatIso.ofComponents (fun W => (finiteEtaleGeometricHomEquivFiber s W).toIso) (by
    intro V W f
    ext a
    change Over.mk s ⟶ (FiniteEtale.forget X).obj V at a
    change finiteEtaleGeometricHomEquivFiber s W (a ≫ (FiniteEtale.forget X).map f) =
      ((FiniteEtale.fiber s).map f) (finiteEtaleGeometricHomEquivFiber s V a)
    rw [finiteEtaleGeometricHomEquivFiber_apply, finiteEtaleGeometricHomEquivFiber_apply]
    change (pullback.lift (f := ((FiniteEtale.forget X).obj W).hom) (g := s)
      (a.left ≫ ((FiniteEtale.forget X).map f).left) (𝟙 _) _) (default : Spec (.of Ω)) =
      ((pullback.lift (f := ((FiniteEtale.forget X).obj V).hom) (g := s) a.left (𝟙 _) _) ≫
        ((Over.pullback s).map ((FiniteEtale.forget X).map f)).left)
        (default : Spec (.of Ω))
    apply congrArg (fun t : Spec (.of Ω) ⟶ _ => t (default : Spec (.of Ω)))
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_snd])

/-- The geometric stalk of a finite étale represented sheaf is naturally the
underlying finite set of the existing EFG fiber functor. -/
def finiteEtaleSheafFiberIso {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    finiteEtaleSheaf X ⋙ (Scheme.pointSmallEtale s).sheafFiber ≅
      FiniteEtale.fiber s ⋙ forget FintypeCat :=
  finiteEtaleSheafStalkIso s ≪≫ finiteEtaleGeometricFiberIso s

end EtaleCohomology
