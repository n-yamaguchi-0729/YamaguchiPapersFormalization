/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.ExtensionFiberSquare
import EtaleFundamentalGroups.Cohomology.AbelianPullbackMate
import EtaleCohomology.Sites.SetPullbackExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Inverse image of the actual sheaf of lifts

The lift sheaf of an abelian extension is pulled back using its categorical
fiber square. The comparison uses the actual abelian inverse image and the
actual underlying-set comparison; no compatibility is imposed as a hypothesis.
The quotient section is transported explicitly.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits EtaleCohomology Opposite

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The singleton sheaf is preserved by the actual inverse image. -/
def extensionFiberTerminalPullbackIso :
    (etaleSetPullback f).obj (extensionFiberTerminal Y) ≅ extensionFiberTerminal X :=
  ((Sheaf.isTerminalTerminal Y.smallEtaleTopology Types.isTerminalPUnit).isTerminalObj
    (etaleSetPullback f) (extensionFiberTerminal Y)).uniqueUpToIso
      (Sheaf.isTerminalTerminal X.smallEtaleTopology Types.isTerminalPUnit)

variable (S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))
  (t : (Functor.const Y.Etaleᵒᵖ).obj PUnit ⟶ S.X₃.obj ⋙ forget AddCommGrpCat.{u})

/-- Transport the original quotient section through the actual inverse image. -/
def extensionFiberPullbackSection :
    extensionFiberTerminal X ⟶
      (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj
        ((etaleAbelianPullback f).obj S.X₃) :=
  (extensionFiberTerminalPullbackIso f).inv ≫
    (etaleSetPullback f).map (extensionFiberSection S t) ≫
      (abelianPullbackUnderlyingMateIso f).inv.app S.X₃

/-- The transported lift square remains a pullback. -/
theorem extensionFiber_pullback_isPullback :
    IsPullback
      ((etaleSetPullback f).map (extensionFiberInclusion S t) ≫
        (abelianPullbackUnderlyingMateIso f).inv.app S.X₂)
      ((Sheaf.isTerminalTerminal X.smallEtaleTopology Types.isTerminalPUnit).from
        ((etaleSetPullback f).obj (extensionFiber S t)))
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).map
        ((etaleAbelianPullback f).map S.g))
      (extensionFiberPullbackSection f S t) := by
  refine ((extensionFiber_isPullback S t).map (etaleSetPullback f)).of_iso
    (Iso.refl _) ((abelianPullbackUnderlyingMateIso f).app S.X₂).symm
    (extensionFiberTerminalPullbackIso f)
    ((abelianPullbackUnderlyingMateIso f).app S.X₃).symm ?_ ?_ ?_ ?_
  · exact (Category.id_comp _).symm
  · exact (Sheaf.isTerminalTerminal X.smallEtaleTopology
      Types.isTerminalPUnit).hom_ext _ _
  · exact (abelianPullbackUnderlyingMateIso f).inv.naturality S.g
  · dsimp only [extensionFiberPullbackSection]
    exact ((extensionFiberTerminalPullbackIso f).hom_inv_id_assoc
      ((etaleSetPullback f).map (extensionFiberSection S t) ≫
        (abelianPullbackUnderlyingMateIso f).inv.app S.X₃)).symm

/-- Actual set inverse image of the lift sheaf is the lift sheaf of the actual
abelian inverse-image extension, over the transported quotient section. -/
def extensionFiberPullbackIso :
    (etaleSetPullback f).obj (extensionFiber S t) ≅
      extensionFiber (S.map (etaleAbelianPullback f))
        (extensionFiberPullbackSection f S t).hom :=
  (extensionFiber_pullback_isPullback f S t).isoIsPullback _ _
    (extensionFiber_isPullback (S.map (etaleAbelianPullback f))
      (extensionFiberPullbackSection f S t).hom)

/-- The comparison preserves the original section of the middle sheaf. -/
theorem extensionFiberPullbackIso_hom_inclusion :
    (extensionFiberPullbackIso f S t).hom ≫
        extensionFiberInclusion (S.map (etaleAbelianPullback f))
          (extensionFiberPullbackSection f S t).hom =
      (etaleSetPullback f).map (extensionFiberInclusion S t) ≫
        (abelianPullbackUnderlyingMateIso f).inv.app S.X₂ :=
  (extensionFiber_pullback_isPullback f S t).isoIsPullback_hom_fst _ _
    (extensionFiber_isPullback (S.map (etaleAbelianPullback f))
      (extensionFiberPullbackSection f S t).hom)

end EtaleFundamentalGroups.Cohomology
