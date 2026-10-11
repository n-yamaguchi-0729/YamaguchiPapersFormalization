/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.GlobalSectionsComplex
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic


/-!
# Classical étale cohomology computed on an injective resolution

A given `InjectiveResolution F` is extended from nonnegative to integer
degrees by the existing zero-extension functor. Its actual augmentation
becomes a quasi-isomorphism from the single complex of `F`, and the
extended resolution is K-injective by mathlib's bounded-below theorem.

The additive derived-Hom and homotopy-Hom comparisons therefore compute
actual small-universe `Sheaf.H` by the Hom complex. The constructed natural
cochain isomorphism then identifies this with the homology of actual global
sections of the extended resolution, followed by the canonical universe lift.
There is no comparison premise or replacement cohomology definition.
-/

noncomputable section

universe w v uC u

open AlgebraicGeometry CategoryTheory Limits Opposite
open CochainComplex

namespace EtaleCohomology.Classical

private def homCongrAddEquiv {C : Type uC} [Category.{v} C] [Preadditive C]
    {A B A' B' : C} (e : A ≅ A') (f : B ≅ B') : (A ⟶ B) ≃+ (A' ⟶ B') where
  toEquiv := Iso.homCongr e f
  map_add' a b := by
    change e.inv ≫ (a + b) ≫ f.hom = (e.inv ≫ a ≫ f.hom) + (e.inv ≫ b ≫ f.hom)
    rw [Preadditive.add_comp, Preadditive.comp_add]

private def derivedHomComplexHomologyEquiv
    {C : Type uC} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) ≃+
      (CochainComplex.HomComplex K L).homology n := by
  let qK : HomotopyCategory C (ComplexShape.up ℤ) :=
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K
  let qL : HomotopyCategory C (ComplexShape.up ℤ) :=
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧)
  let eK : (DerivedCategory.Qh (C := C)).obj qK ≅ DerivedCategory.Q.obj K :=
    (DerivedCategory.quotientCompQhIso C).app K
  let eL : (DerivedCategory.Qh (C := C)).obj qL ≅ (DerivedCategory.Q.obj L)⟦n⟧ :=
    (DerivedCategory.quotientCompQhIso C).app (L⟦n⟧) ≪≫
      ((DerivedCategory.Q (C := C)).commShiftIso n).app L
  let eQ : (qK ⟶ qL) ≃+
      ((DerivedCategory.Qh (C := C)).obj qK ⟶ (DerivedCategory.Qh (C := C)).obj qL) :=
    AddEquiv.ofBijective (DerivedCategory.Qh (C := C)).mapAddHom
      (CochainComplex.IsKInjective.Qh_map_bijective qK (L⟦n⟧))
  exact (homCongrAddEquiv eK eL).symm.trans
    (eQ.symm.trans
      ((HomComplex.CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).symm.trans
        (HomComplex.homologyAddEquiv K L n).symm))

private def extResolutionHomologyEquiv
    {C : Type uC} [Category.{v} C] [Abelian C] [HasDerivedCategory C] [HasExt.{w} C]
    (A : C) {F : C} (I : InjectiveResolution F) (n : ℕ) :
    Abelian.Ext.{w} A F n ≃+
      (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj A)
        (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) := by
  let L : CochainComplex C ℤ := I.cocomplex.extend ComplexShape.embeddingUpNat
  let s : (CochainComplex.singleFunctor C 0).obj F ⟶ L :=
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).inv ≫
      HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat
  let e : (DerivedCategory.singleFunctor C 0).obj F ≅ DerivedCategory.Q.obj L :=
    asIso (DerivedCategory.Q.map s)
  let en : ((DerivedCategory.singleFunctor C 0).obj F)⟦(n : ℤ)⟧ ≅
      (DerivedCategory.Q.obj L)⟦(n : ℤ)⟧ :=
    (CategoryTheory.shiftFunctor (DerivedCategory C) (n : ℤ)).mapIso e
  exact Abelian.Ext.homAddEquiv.trans
    ((homCongrAddEquiv (Iso.refl ((DerivedCategory.singleFunctor C 0).obj A)) en).trans
      (derivedHomComplexHomologyEquiv ((CochainComplex.singleFunctor C 0).obj A) L (n : ℤ)))

end EtaleCohomology.Classical

namespace EtaleCohomology

/-- Classical `Sheaf.H` is computed by actual global sections of a given
injective resolution, extended by zero to integer degrees. The left-hand
cohomology remains in universe `u`; only the explicit target lift enters the
raw Hom-complex universe. -/
def etaleAbelianCohomologyInjectiveResolutionEquiv
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (I : InjectiveResolution F) (n : ℕ) :
    Sheaf.H.{u} F n ≃+
      (((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (⊤_ X.Etale))) ⋙
          AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) := by
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
  letI : HasDerivedCategory C := HasDerivedCategory.standard C
  let e : Sheaf.H.{u} F n ≃+
      (CochainComplex.HomComplex
        ((CochainComplex.singleFunctor C 0).obj
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} ℤ))))
        (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) :=
    Classical.extResolutionHomologyEquiv
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) I n
  exact e.trans
    (((HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) (n : ℤ)).mapIso
      ((etaleHomFromIntegerSectionsIso X).app
        (I.cocomplex.extend ComplexShape.embeddingUpNat))).addCommGroupIsoToAddEquiv)

end EtaleCohomology
