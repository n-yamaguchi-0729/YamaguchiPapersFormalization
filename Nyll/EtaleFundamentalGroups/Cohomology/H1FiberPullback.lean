/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
import Nyll.EtaleFundamentalGroups.Cohomology.ConstantPullbackSections

/-!
# The actual H¹ lift cover commutes with geometric inverse image

After identifying both constant coefficients, the inverse image of the original
lift sheaf is the lift sheaf over the original integer section on the new base.
This is the lift sheaf of the extension representing the actual derived
cohomology pullback, not an independently chosen replacement.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite EtaleCohomology

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (A : AddCommGrpCat.{u})
  {E : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
  (p : E ⟶ (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)))
  (h : i ≫ p = 0)

/-- The pulled-back original lift cover has the fiber square for the geometric
inverse-image extension with its original constant quotient. -/
theorem schemePullbackH1Extension_fiber_isPullback :
    IsPullback
      ((etaleSetPullback f).map
          (extensionFiberInclusion (ShortComplex.mk i p h) (integerUnitSection Y)) ≫
        (abelianPullbackUnderlyingMateIso f).inv.app E)
      ((Sheaf.isTerminalTerminal X.smallEtaleTopology Types.isTerminalPUnit).from
        ((etaleSetPullback f).obj
          (extensionFiber (ShortComplex.mk i p h) (integerUnitSection Y))))
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).map
        (schemePullbackH1Extension f A i p h).g)
      (extensionFiberSection (schemePullbackH1Extension f A i p h)
        (integerUnitSection X)) := by
  let UX := sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})
  let eZ := (etaleAbelianPullbackConstantIso f).app
    (AddCommGrpCat.of (ULift.{u} ℤ))
  refine (extensionFiber_pullback_isPullback f (ShortComplex.mk i p h)
    (integerUnitSection Y)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (UX.mapIso eZ) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · change UX.map ((etaleAbelianPullback f).map p) ≫ UX.map eZ.hom =
      𝟙 _ ≫ UX.map ((etaleAbelianPullback f).map p ≫ eZ.hom)
    rw [Functor.map_comp, Category.id_comp]
  · let t := (etaleSetPullback f).map (integerUnitSheafSection Y)
    let c := (abelianPullbackUnderlyingComparison f).app
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))
    let k := UX.map eZ.hom
    change ((extensionFiberTerminalPullbackIso f).inv ≫ t ≫ c) ≫ k =
      𝟙 _ ≫ integerUnitSheafSection X
    exact (Category.assoc (extensionFiberTerminalPullbackIso f).inv (t ≫ c) k).trans
      ((congrArg (fun v => (extensionFiberTerminalPullbackIso f).inv ≫ v)
        (Category.assoc t c k)).trans
          ((integerUnitSheafSection_pullback_inv f).trans (Category.id_comp _).symm))

/-- The actual lift sheaf of an H¹ extension commutes with geometric pullback,
including the identification of its distinguished integer section. -/
def schemePullbackH1Extension_fiberIso :
    (etaleSetPullback f).obj
        (extensionFiber (ShortComplex.mk i p h) (integerUnitSection Y)) ≅
      extensionFiber (schemePullbackH1Extension f A i p h) (integerUnitSection X) :=
  (schemePullbackH1Extension_fiber_isPullback f A i p h).isoIsPullback _ _
    (extensionFiber_isPullback (schemePullbackH1Extension f A i p h)
      (integerUnitSection X))

/-- This comparison keeps the inclusion into the original inverse-image middle sheaf. -/
theorem schemePullbackH1Extension_fiberIso_hom_inclusion :
    (schemePullbackH1Extension_fiberIso f A i p h).hom ≫
        extensionFiberInclusion (schemePullbackH1Extension f A i p h)
          (integerUnitSection X) =
      (etaleSetPullback f).map
          (extensionFiberInclusion (ShortComplex.mk i p h) (integerUnitSection Y)) ≫
        (abelianPullbackUnderlyingMateIso f).inv.app E :=
  (schemePullbackH1Extension_fiber_isPullback f A i p h).isoIsPullback_hom_fst _ _
    (extensionFiber_isPullback (schemePullbackH1Extension f A i p h)
      (integerUnitSection X))

end EtaleFundamentalGroups.Cohomology
