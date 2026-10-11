/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.AbelianPullbackMate
import EtaleFundamentalGroups.Cohomology.ExtensionFiberPullback
import EtaleFundamentalGroups.Cohomology.H1FiniteCover
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Constant sections under actual inverse image

The constant-sheaf comparison is the unique comparison of left adjoints.
Its adjoint carries each constant section to the same section on the
base-changed étale object. In particular it preserves the integer section
used to construct the torsor of an actual derived H¹ extension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite EtaleCohomology

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Adjoint of the existing constant-coefficient inverse-image comparison. -/
def constantAbelianPullbackAdjoint (A : AddCommGrpCat.{u}) :
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶
      (etaleAbelianPushforward f).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) :=
  (etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _
    ((etaleAbelianPullbackConstantIso f).hom.app A)

/-- The adjoint of constant inverse image preserves every constant section. -/
theorem constantAbelianPullbackAdjoint_unit (A : AddCommGrpCat.{u}) (U : Y.Etale) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app (op U) ≫
        (constantAbelianPullbackAdjoint f A).hom.app (op U) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
        (op ((etaleBaseChange f).obj U)) := by
  let TY := ⊤_ Y.Etale
  let q := constantAbelianPullbackAdjoint f A
  let y := toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)
  let x := toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)
  have hT := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} terminalIsTerminal).comp
      (etaleAbelianPullbackPushforwardAdjunction f))
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
      (terminalIsTerminal.isTerminalObj (etaleBaseChange f) TY)) A
  rw [Adjunction.comp_homEquiv] at hT
  change y.app (op TY) ≫ q.hom.app (op TY) =
    x.app (op ((etaleBaseChange f).obj TY)) at hT
  let j : op TY ⟶ op U := (terminal.from U).op
  apply ConcreteCategory.hom_ext
  intro a
  have hy := ConcreteCategory.congr_hom (y.naturality j) a
  change y.app (op U) a =
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.map j
      (y.app (op TY) a) at hy
  have hq := ConcreteCategory.congr_hom (q.hom.naturality j) (y.app (op TY) a)
  have hx := ConcreteCategory.congr_hom
    (x.naturality ((etaleBaseChange f).map (terminal.from U)).op) a
  change x.app (op ((etaleBaseChange f).obj U)) a =
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.map
      ((etaleBaseChange f).map (terminal.from U)).op
      (x.app (op ((etaleBaseChange f).obj TY)) a) at hx
  exact (congrArg (q.hom.app (op U)) hy).trans (hq.trans
    ((congrArg
      (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.map
        ((etaleBaseChange f).map (terminal.from U)).op)
      (ConcreteCategory.congr_hom hT a)).trans hx.symm))

/-- Pointwise form of constant-section compatibility, retaining the coefficient type. -/
theorem constantAbelianPullbackAdjoint_unit_apply (A : AddCommGrpCat.{u})
    (U : Y.Etale) (a : A) :
    (constantAbelianPullbackAdjoint f A).hom.app (op U)
        ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app (op U) a) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
        (op ((etaleBaseChange f).obj U)) a := by
  exact ConcreteCategory.congr_hom (constantAbelianPullbackAdjoint_unit f A U) a

/-- The particular quotient section defining H¹ torsors is preserved by the
adjoint of the actual constant integer comparison. -/
theorem integerUnitSection_constantPullbackAdjoint_app (U : Y.Etaleᵒᵖ) (z : PUnit) :
    (constantAbelianPullbackAdjoint f (AddCommGrpCat.of (ULift.{u} ℤ))).hom.app U
        ((integerUnitSection Y).app U z) =
      (integerUnitSection X).app (op ((etaleBaseChange f).obj U.unop)) PUnit.unit := by
  dsimp only [integerUnitSection]
  exact constantAbelianPullbackAdjoint_unit_apply f
    (AddCommGrpCat.of (ULift.{u} ℤ)) U.unop (ULift.up 1)

/-- The integer section as a morphism of actual set-valued sheaves. -/
def integerUnitSheafSection (Z : Scheme.{u}) :
    extensionFiberTerminal Z ⟶
      (sheafCompose Z.smallEtaleTopology (forget AddCommGrpCat.{u})).obj
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) :=
  ⟨integerUnitSection Z⟩

private theorem integerUnitSheafSection_pushforward_comp
    (a : extensionFiberTerminal Y ⟶
      (etaleSetPushforward f).obj (extensionFiberTerminal X))
    (U : Y.Etaleᵒᵖ) (z : PUnit) :
    (a ≫ (etaleSetPushforward f).map (integerUnitSheafSection X)).hom.app U z =
      (integerUnitSection X).app (op ((etaleBaseChange f).obj U.unop)) PUnit.unit := rfl

private theorem integerUnitSheafSection_comp_adjoint
    (a : extensionFiberTerminal Y ⟶
      (etaleSetPushforward f).obj (extensionFiberTerminal X)) :
    integerUnitSheafSection Y ≫
        (sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u})).map
          (constantAbelianPullbackAdjoint f (AddCommGrpCat.of (ULift.{u} ℤ))) =
      a ≫ (etaleSetPushforward f).map (integerUnitSheafSection X) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro z
  exact (integerUnitSection_constantPullbackAdjoint_app f U z).trans
    (integerUnitSheafSection_pushforward_comp f a U z).symm

/-- The canonical underlying comparison and the constant coefficient comparison
carry the original integer section to the original integer section. -/
theorem integerUnitSheafSection_pullback :
    (etaleSetPullback f).map (integerUnitSheafSection Y) ≫
        (abelianPullbackUnderlyingComparison f).app
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} ℤ))) ≫
          (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).map
            ((etaleAbelianPullbackConstantIso f).hom.app
              (AddCommGrpCat.of (ULift.{u} ℤ))) =
      (extensionFiberTerminalPullbackIso f).hom ≫ integerUnitSheafSection X := by
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  let CY := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj Z
  let CX := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj Z
  let UX := sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})
  let UY := sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u})
  let adj := etaleSetPullbackPushforwardAdjunction f
  apply (adj.homEquiv (extensionFiberTerminal Y) (UX.obj CX)).injective
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  refine (congrArg
    (fun k : UY.obj CY ⟶ (etaleSetPushforward f).obj (UX.obj CX) =>
      integerUnitSheafSection Y ≫ k)
    (abelianPullbackUnderlyingComparison_homEquiv f CY CX
      ((etaleAbelianPullbackConstantIso f).hom.app Z))).trans ?_
  exact integerUnitSheafSection_comp_adjoint f
    (adj.homEquiv (extensionFiberTerminal Y) (extensionFiberTerminal X)
      (extensionFiberTerminalPullbackIso f).hom)

/-- Explicitly transporting the integer section through inverse image leaves it
equal to the distinguished section defining the H¹ extension torsor. -/
theorem integerUnitSheafSection_pullback_inv :
    (extensionFiberTerminalPullbackIso f).inv ≫
      (etaleSetPullback f).map (integerUnitSheafSection Y) ≫
        (abelianPullbackUnderlyingComparison f).app
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} ℤ))) ≫
          (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).map
            ((etaleAbelianPullbackConstantIso f).hom.app
              (AddCommGrpCat.of (ULift.{u} ℤ))) =
      integerUnitSheafSection X := by
  rw [integerUnitSheafSection_pullback]
  exact (extensionFiberTerminalPullbackIso f).inv_hom_id_assoc
    (integerUnitSheafSection X)

end EtaleFundamentalGroups.Cohomology
