/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.H1FiniteCover
import EtaleFundamentalGroups.Cohomology.ExtensionSplitting
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Global lifts of one and vanishing of the actual extension class

A global section of the fiber over the constant integer section `1` gives a
splitting of the original quotient morphism, by taking integral multiples and
using the sheafification adjunction. Conversely a splitting gives such a
section. Thus this torsor has a global point precisely when the actual Ext
class vanishes.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} {K E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
  (i : K ⟶ E)
  (p : E ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))) (h : i ≫ p = 0)

private def integerLiftMap
    (d : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶
      (extensionFiber (ShortComplex.mk i p h) (integerUnitSection X)).obj) :
    (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ E.obj where
  app U := AddCommGrpCat.ofHom (uliftZMultiplesHom (E.obj.obj U) (d.app U PUnit.unit).val)
  naturality U V f := by
    apply (AddCommGrpCat.uliftZMultiplesAddEquiv (E.obj.obj V)).injective
    change (uliftZMultiplesHom (E.obj.obj V) (d.app V PUnit.unit).val) (ULift.up 1) =
      E.obj.map f ((uliftZMultiplesHom (E.obj.obj U) (d.app U PUnit.unit).val) (ULift.up 1))
    rw [uliftZMultiplesHom_apply_apply, uliftZMultiplesHom_apply_apply]
    change (1 : ℤ) • (d.app V PUnit.unit).val = E.obj.map f ((1 : ℤ) • (d.app U PUnit.unit).val)
    rw [one_zsmul, one_zsmul]
    exact congrArg Subtype.val (ConcreteCategory.congr_hom (d.naturality f) PUnit.unit)

/-- A global lift of the section `1` splits the actual extension quotient. -/
theorem exists_section_of_integerFiber_section
    (d : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶
      (extensionFiber (ShortComplex.mk i p h) (integerUnitSection X)).obj) :
    ∃ s : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ E, s ≫ p = 𝟙 _ := by
  let P := (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  let adj := sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}
  let f := integerLiftMap i p h d
  have hf : f ≫ p.hom = toSheafify X.smallEtaleTopology P := by
    apply NatTrans.ext
    funext U
    apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
    change p.hom.app U
      ((uliftZMultiplesHom (E.obj.obj U) (d.app U PUnit.unit).val) (ULift.up 1)) =
        (toSheafify X.smallEtaleTopology P).app U (ULift.up 1)
    rw [uliftZMultiplesHom_apply_apply]
    change p.hom.app U ((1 : ℤ) • (d.app U PUnit.unit).val) = _
    rw [one_zsmul]
    exact (d.app U PUnit.unit).property
  refine ⟨(adj.homEquiv P E).symm f, ?_⟩
  apply (adj.homEquiv P _).injective
  exact (adj.homEquiv_naturality_right ((adj.homEquiv P E).symm f) p).trans
    ((congrArg (· ≫ p.hom) ((adj.homEquiv P E).apply_symm_apply f)).trans
      (hf.trans (Category.comp_id _).symm))

/-- A splitting gives a section of the actual fiber over `1`. -/
def integerFiberSectionOfSection
    (s : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ E) (hs : s ≫ p = 𝟙 _) :
    (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶
      (extensionFiber (ShortComplex.mk i p h) (integerUnitSection X)).obj where
  app U := ↾fun _ => ⟨s.hom.app U ((integerUnitSection X).app U PUnit.unit), by
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun k => k.hom.app U) hs) ((integerUnitSection X).app U PUnit.unit)
    exact hh⟩
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    have hn := ConcreteCategory.congr_hom (s.hom.naturality f)
      ((integerUnitSection X).app U PUnit.unit)
    have ht := ConcreteCategory.congr_hom ((integerUnitSection X).naturality f) PUnit.unit
    exact (congrArg (s.hom.app V) ht).trans hn

/-- The actual extension class is zero precisely when its fiber over `1` has
a global section. -/
theorem extClass_eq_zero_iff_integerFiber_section (hs : (ShortComplex.mk i p h).ShortExact) :
    hs.extClass = 0 ↔ Nonempty ((Functor.const X.Etaleᵒᵖ).obj PUnit ⟶
      (extensionFiber (ShortComplex.mk i p h) (integerUnitSection X)).obj) := by
  rw [extClass_eq_zero_iff_exists_section]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨integerFiberSectionOfSection i p h s hs⟩
  · rintro ⟨d⟩
    exact exists_section_of_integerFiber_section i p h d

end EtaleFundamentalGroups.Cohomology
