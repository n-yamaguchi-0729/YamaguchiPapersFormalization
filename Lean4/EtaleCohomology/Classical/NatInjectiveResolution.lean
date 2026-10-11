/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Classical.InjectiveResolution
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Sites.Sheaf


/-!
# Classical cohomology and nonnegative injective resolutions

Mapping a zero-extended complex by a zero-preserving functor commutes with
extension: the comparison uses `extendXIso` in nonnegative degrees and
actual zero-object witnesses in negative degrees. This is a constructed
chain isomorphism, not an interchange premise.

The existing extension-homology comparison and exactness of the canonical
abelian-group universe lift then remove the extension and lift from the
classical cohomology calculation. Thus the original small `Sheaf.H` is
computed by actual global sections of the original `ℕ`-indexed resolution.
The existing `InjectiveResolution.isoRightDerivedObj` gives the corresponding
objectwise comparison with `Functor.rightDerived` of actual global sections.
-/

noncomputable section

universe uC vC uD vD u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology.Classical

section Extension

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D] [HasZeroObject D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

private theorem isZero_extend_negSucc (K : CochainComplex C ℕ) (n : ℕ) :
    IsZero ((K.extend ComplexShape.embeddingUpNat).X (Int.negSucc n)) :=
  K.isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc n) (fun i h => by
    change Int.ofNat i = Int.negSucc n at h
    cases h)

private def mapExtendUpNatXIso (K : CochainComplex C ℕ) (j : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat)).X j ≅
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat).X j := by
  cases j with
  | ofNat n =>
      exact F.mapIso (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl) ≪≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
          ComplexShape.embeddingUpNat (i := n) rfl).symm
  | negSucc n =>
      exact (F.map_isZero (isZero_extend_negSucc K n)).iso
        (isZero_extend_negSucc ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n)

private def mapExtendUpNatIso (K : CochainComplex C ℕ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents (mapExtendUpNatXIso F K) (by
    intro i j _
    cases i with
    | negSucc i =>
        exact (F.map_isZero (isZero_extend_negSucc K i)).eq_of_src _ _
    | ofNat i =>
        cases j with
        | negSucc j =>
            exact (isZero_extend_negSucc
              ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) j).eq_of_tgt _ _
        | ofNat j =>
            have hi : ComplexShape.embeddingUpNat.f i = (i : ℤ) := rfl
            have hj : ComplexShape.embeddingUpNat.f j = (j : ℤ) := rfl
            let ai := K.extendXIso ComplexShape.embeddingUpNat hi
            let aj := K.extendXIso ComplexShape.embeddingUpNat hj
            let bi := ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
              ComplexShape.embeddingUpNat hi
            let bj := ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
              ComplexShape.embeddingUpNat hj
            change (F.map ai.hom ≫ bi.inv) ≫
                (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
                  ComplexShape.embeddingUpNat).d (i : ℤ) (j : ℤ) =
              F.map ((K.extend ComplexShape.embeddingUpNat).d (i : ℤ) (j : ℤ)) ≫
                F.map aj.hom ≫ bj.inv
            rw [HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat hi hj,
              HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat hi hj]
            change (F.map ai.hom ≫ bi.inv) ≫ (bi.hom ≫ F.map (K.d i j) ≫ bj.inv) =
              F.map (ai.hom ≫ K.d i j ≫ aj.inv) ≫ F.map aj.hom ≫ bj.inv
            have hcancel : F.map aj.inv ≫ F.map aj.hom ≫ bj.inv = bj.inv := by
              rw [← F.map_comp_assoc, aj.inv_hom_id, F.map_id, Category.id_comp]
            simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, hcancel])

end Extension

end EtaleCohomology.Classical

namespace EtaleCohomology

/-- Actual global sections commute with zero extension of a nonnegative
complex. The comparison is an explicit chain isomorphism in the original
coefficient universe. -/
def etaleGlobalSectionsExtendIso (X : Scheme.{u})
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℕ) :
    (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (⊤_ X.Etale))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
          ComplexShape.embeddingUpNat :=
  Classical.mapExtendUpNatIso
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (⊤_ X.Etale))) K

/-- The original small classical cohomology group is computed by actual global
sections of the original nonnegative injective resolution. Both sides have
carrier universe `u`; extension and universe lift have been explicitly compared
and removed. -/
def etaleAbelianCohomologyNatResolutionEquiv
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (I : InjectiveResolution F) (n : ℕ) :
    Sheaf.H.{u} F n ≃+
      ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (op (⊤_ X.Etale))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).homology n := by
  let Γ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (⊤_ X.Etale))
  let U : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u + 1} := AddCommGrpCat.uliftFunctor.{u + 1, u}
  let K : CochainComplex AddCommGrpCat.{u} ℕ :=
    (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let B : CochainComplex AddCommGrpCat.{u + 1} ℕ :=
    ((Γ ⋙ U).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let eExtend := Classical.mapExtendUpNatIso (Γ ⋙ U) I.cocomplex
  let eComp : (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ≅ B :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (Γ ⋙ U)) (ComplexShape.up ℕ)).app I.cocomplex
  let eLift : ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n ≅
      U.obj (K.homology n) :=
    (K.sc n).mapHomologyIso U
  let e : (((Γ ⋙ U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) ≅
      U.obj (K.homology n) :=
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) (n : ℤ)).mapIso
        eExtend ≪≫
      B.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) n).mapIso
        eComp.symm ≪≫ eLift
  exact (etaleAbelianCohomologyInjectiveResolutionEquiv X F I n).trans
    (e.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)

/-- Étale global sections are additive via the canonical sheaf-evaluation
isomorphism and the existing additive inclusion and evaluation functors. -/
instance etaleAbelianGlobalSections_additive (X : Scheme.{u}) :
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (⊤_ X.Etale))).Additive :=
  Functor.additive_of_iso
    (sheafSectionsNatIsoEvaluation X.smallEtaleTopology AddCommGrpCat.{u}
      (X := ⊤_ X.Etale)).symm

/-- Objectwise identification of actual classical `Sheaf.H` with the existing
right-derived functor of actual abelian global sections. This uses the canonical
supplied injective resolution and its standard derived-functor computation. -/
def etaleAbelianCohomologyRightDerivedEquiv
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} F n ≃+
      ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (op (⊤_ X.Etale))).rightDerived n).obj F) :=
  (etaleAbelianCohomologyNatResolutionEquiv X F (injectiveResolution F) n).trans
    ((((injectiveResolution F).isoRightDerivedObj
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (op (⊤_ X.Etale))) n).symm).addCommGroupIsoToAddEquiv)

end EtaleCohomology
