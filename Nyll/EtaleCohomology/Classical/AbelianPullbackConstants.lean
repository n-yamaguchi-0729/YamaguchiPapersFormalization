/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
import Nyll.EtaleCohomology.Sites.ConstantPullback
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Constant sections under actual abelian inverse image

The constant-sheaf inverse-image comparison is defined by uniqueness of left
adjoints. Its adjoint sends each original constant section to the same section
on the base-changed etale scheme. In particular it preserves the integer section
one used to represent degree-one cohomology classes by extension fibers.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

private theorem constantSheafAdj_homEquiv_section (X : Scheme.{u})
    (T : X.Etale) (hT : IsTerminal T) (A : AddCommGrpCat.{u})
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (g : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E) :
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).homEquiv A E g =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op T) ≫
        g.hom.app (op T) := rfl

private theorem constantPullbackSection
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (adj : L ⊣ etaleAbelianPushforward f) (A : AddCommGrpCat.{u}) (U : Y.Etale) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app (op U) ≫
        (adj.homEquiv _ _
          ((Sites.constantSheafCompLeftAdjointIso (etaleBaseChange f) AddCommGrpCat.{u}
            terminalIsTerminal
              (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ Y.Etale))
                L adj).hom.app A)).hom.app (op U) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
        (op ((etaleBaseChange f).obj U)) := by
  let F := etaleBaseChange f
  let ηY : (Functor.const Y.Etaleᵒᵖ).obj A ⟶
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A).obj :=
    toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)
  let ηX : (Functor.const X.Etaleᵒᵖ).obj A ⟶
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A).obj :=
    toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)
  let c := adj.homEquiv _ _
    ((Sites.constantSheafCompLeftAdjointIso (etaleBaseChange f) AddCommGrpCat.{u}
      terminalIsTerminal (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ Y.Etale))
        L adj).hom.app A)
  have hc : ηY.app (op (⊤_ Y.Etale)) ≫ c.hom.app (op (⊤_ Y.Etale)) =
      ηX.app (op (F.obj (⊤_ Y.Etale))) := by
    let adjY : constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⊣
        (sheafSections Y.smallEtaleTopology AddCommGrpCat.{u}).obj (op (⊤_ Y.Etale)) :=
      constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} terminalIsTerminal
    let adjX : constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⊣
        etaleAbelianPushforward f ⋙
          (sheafSections Y.smallEtaleTopology AddCommGrpCat.{u}).obj (op (⊤_ Y.Etale)) :=
      constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
        (terminalIsTerminal.isTerminalObj F (⊤_ Y.Etale))
    have hcomp : adjY.homEquiv A _ c = adjX.unit.app A :=
      Adjunction.homEquiv_leftAdjointUniq_hom_app
        (adjY.comp adj) adjX A
    have hsource : adjY.homEquiv A _ c =
        ηY.app (op (⊤_ Y.Etale)) ≫ c.hom.app (op (⊤_ Y.Etale)) :=
      constantSheafAdj_homEquiv_section Y (⊤_ Y.Etale) terminalIsTerminal A _ c
    have htarget : adjX.unit.app A = ηX.app (op (F.obj (⊤_ Y.Etale))) :=
      (adjX.homEquiv_id A).symm.trans
        ((constantSheafAdj_homEquiv_section X (F.obj (⊤_ Y.Etale))
          (terminalIsTerminal.isTerminalObj F (⊤_ Y.Etale)) A _ (𝟙 _)).trans
            (Category.comp_id _))
    exact hsource.symm.trans (hcomp.trans htarget)
  let j : U ⟶ ⊤_ Y.Etale := terminal.from U
  have hY : ηY.app (op U) = ηY.app (op (⊤_ Y.Etale)) ≫
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.map j.op := by
    exact (Category.id_comp _).symm.trans (ηY.naturality j.op)
  have hX : ηX.app (op (F.obj U)) = ηX.app (op (F.obj (⊤_ Y.Etale))) ≫
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.map (F.map j).op := by
    exact (Category.id_comp _).symm.trans (ηX.naturality (F.map j).op)
  change ηY.app (op U) ≫ c.hom.app (op U) = ηX.app (op (F.obj U))
  rw [hY, Category.assoc, c.hom.naturality j.op, ← Category.assoc, hc]
  exact hX.symm


/-- The adjoint of the actual constant inverse-image comparison sends a constant
coefficient to the same coefficient on each base-changed etale scheme. -/
theorem etaleAbelianPullbackConstantIso_hom_section
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : AddCommGrpCat.{u}) (U : Y.Etale) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app (op U) ≫
        ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _
          ((etaleAbelianPullbackConstantIso f).hom.app A)).hom.app (op U) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
        (op ((etaleBaseChange f).obj U)) :=
  constantPullbackSection f (etaleAbelianPullback f)
    (etaleAbelianPullbackPushforwardAdjunction f) A U

end EtaleCohomology
