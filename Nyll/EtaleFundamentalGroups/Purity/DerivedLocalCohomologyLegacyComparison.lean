/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedExtLegacyComparison
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomology
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Comparing derived and legacy local cohomology

This file constructs the projective-resolution comparison between
derived-category Ext and the legacy left-derived Ext used by
`localCohomology`.  The comparison is first built in positive degree from
the common cocycle quotient; its naturality in the first variable is the
input needed to compare the ideal-powers diagrams and their colimits.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u

section PositiveDegree

variable {R : Type u} [CommRing R]
variable {X : ModuleCat.{u} R}

/-- The three terms around positive degree `n + 1` in the cochain complex
computing legacy Ext, after forgetting the `R`-module structure. -/
abbrev projectiveResolutionForgottenLinearYonedaShortComplexSucc
    (P : ProjectiveResolution X) (Y : ModuleCat.{u} R) (n : ℕ) :
    ShortComplex AddCommGrpCat.{u} :=
  ((P.complex.linearYonedaObj R Y).sc' n (n + 1) (n + 2)).map
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

/-- A cocycle in the projective-resolution complex determines its
derived-category Ext class. -/
def projectiveResolutionCyclesToDerivedExtSucc
    (P : ProjectiveResolution X) (Y : ModuleCat.{u} R) (n : ℕ) :
    AddMonoidHom
      (AddMonoidHom.ker
        (projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P Y n).g.hom)
      (CategoryTheory.Abelian.Ext.{u} X Y (n + 1)) where
  toFun f := P.extMk f.1 (n + 2) (by omega) (by
    change P.complex.d (n + 2) (n + 1) ≫ f.1 = 0
    exact f.2)
  map_zero' := by
    apply P.extMk_zero
  map_add' f g := by
    symm
    apply P.add_extMk

/-- Every positive-degree derived Ext class has a cocycle representative in
the chosen projective resolution. -/
theorem projectiveResolutionCyclesToDerivedExtSucc_surjective
    (P : ProjectiveResolution X) (Y : ModuleCat.{u} R) (n : ℕ) :
    Function.Surjective
      (projectiveResolutionCyclesToDerivedExtSucc P Y n) := by
  intro x
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective x (n + 2) (by omega)
  refine ⟨⟨f, ?_⟩, rfl⟩
  change P.complex.d (n + 2) (n + 1) ≫ f = 0
  exact hf

/-- In the cocycle group, the kernel of the map to derived Ext is exactly
the subgroup of coboundaries. -/
theorem projectiveResolutionCyclesToDerivedExtSucc_ker_eq_range
    (P : ProjectiveResolution X) (Y : ModuleCat.{u} R) (n : ℕ) :
    AddMonoidHom.ker (projectiveResolutionCyclesToDerivedExtSucc P Y n) =
      AddMonoidHom.range
        (projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P Y n).abToCycles := by
  ext f
  rw [AddMonoidHom.mem_ker]
  change
    P.extMk f.1 (n + 2) (by omega) (by
      change P.complex.d (n + 2) (n + 1) ≫ f.1 = 0
      exact f.2) = 0 ↔ _
  rw [P.extMk_eq_zero_iff f.1 (n + 2) (by omega) (by
    change P.complex.d (n + 2) (n + 1) ≫ f.1 = 0
    exact f.2) n (by omega)]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    ext
    exact hg
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    exact congr_arg Subtype.val hg

/-- The explicit cocycles-modulo-coboundaries group of the forgotten legacy
Ext complex is additively equivalent to derived-category Ext. -/
def projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc
    (P : ProjectiveResolution X) (Y : ModuleCat.{u} R) (n : ℕ) :
    ((AddMonoidHom.ker
        (projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P Y n).g.hom) ⧸
      AddMonoidHom.range
        (projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P Y n).abToCycles) ≃+
      CategoryTheory.Abelian.Ext.{u} X Y (n + 1) :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (projectiveResolutionCyclesToDerivedExtSucc_ker_eq_range
        P Y n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (projectiveResolutionCyclesToDerivedExtSucc P Y n)
      (projectiveResolutionCyclesToDerivedExtSucc_surjective P Y n))

/-- After forgetting the `R`-module structure, legacy Ext computed from a
chosen projective resolution is canonically isomorphic to positive-degree
derived-category Ext. -/
def projectiveResolutionForgottenLegacyExtIsoDerivedExtSucc
    (P : ProjectiveResolution X) (Y : ModuleCat.{u} R) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        (((_root_.Ext R (ModuleCat.{u} R) (n + 1)).obj (op X)).obj Y) ≅
      AddCommGrpCat.of
        (CategoryTheory.Abelian.Ext.{u} X Y (n + 1)) :=
  let K := P.complex.linearYonedaObj R Y
  let S := K.sc' n (n + 1) (n + 2)
  (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapIso
      (P.isoExt (n + 1) Y) ≪≫
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapIso
      (K.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)) ≪≫
    (S.mapHomologyIso
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).symm ≪≫
    (S.map (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).abHomologyIso ≪≫
    (projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc
      P Y n).toAddCommGrpIso

section FirstVariableNaturality

variable {X' : ModuleCat.{u} R}
variable (P' : ProjectiveResolution X') (P : ProjectiveResolution X)
variable {f : X' ⟶ X}

/-- Applying the linear Yoneda functor to a lift of projective resolutions
gives the contravariant map of the cochain complexes computing legacy Ext. -/
def projectiveResolutionLinearYonedaMap
    (phi : ProjectiveResolution.Hom P' P f)
    (Y : ModuleCat.{u} R) :
    P.complex.linearYonedaObj R Y ⟶
      P'.complex.linearYonedaObj R Y :=
  (HomologicalComplex.unopFunctor
      (ModuleCat.{u} R) (ComplexShape.down ℕ)).map
    (((((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map phi.hom).op)

/-- The projective-resolution computation of legacy Ext is natural in the
first variable for any specified lift of the underlying morphism. -/
theorem projectiveResolution_isoExt_hom_naturality
    (phi : ProjectiveResolution.Hom P' P f)
    (Y : ModuleCat.{u} R) (i : ℕ) :
    (((_root_.Ext R (ModuleCat.{u} R) i).map f.op).app Y) ≫
        (P'.isoExt i Y).hom =
      (P.isoExt i Y).hom ≫
        HomologicalComplex.homologyMap
          (projectiveResolutionLinearYonedaMap P' P phi Y) i := by
  dsimp [ProjectiveResolution.isoExt, _root_.Ext]
  have h := ProjectiveResolution.isoLeftDerivedObj_inv_naturality
    f P' P phi.hom phi.hom_f_zero_comp_π_f_zero
      ((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp i
  have hLeftDerived :
      ((((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.leftDerived i).map
          f).unop ≫
        (P'.isoLeftDerivedObj
          ((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp i).inv.unop =
      (P.isoLeftDerivedObj
          ((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp i).inv.unop ≫
        (HomologicalComplex.homologyMap
          (((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ) |>.map phi.hom) i).unop := by
    change
      ((P'.isoLeftDerivedObj
          ((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp i).inv ≫
        (((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.leftDerived i).map f).unop =
      (HomologicalComplex.homologyMap
          (((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ) |>.map phi.hom) i ≫
        (P.isoLeftDerivedObj
          ((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp i).inv).unop
    dsimp only [Functor.comp_map, HomologicalComplex.homologyFunctor] at h ⊢
    exact congr_arg Quiver.Hom.unop h
  change
    ((((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.leftDerived i).map
          f).unop ≫
        (P'.isoLeftDerivedObj
          ((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp i).inv.unop ≫
        (((((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.mapHomologicalComplex
              (ComplexShape.down ℕ)).obj P'.complex).homologyUnop i).inv =
      (P.isoLeftDerivedObj
          ((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp i).inv.unop ≫
        (((((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.mapHomologicalComplex
              (ComplexShape.down ℕ)).obj P.complex).homologyUnop i).inv ≫
        HomologicalComplex.homologyMap
          (projectiveResolutionLinearYonedaMap P' P phi Y) i
  dsimp only [HomologicalComplex.homologyFunctor] at hLeftDerived ⊢
  rw [← Category.assoc, hLeftDerived, Category.assoc]
  congr 1
  change
    (HomologicalComplex.homologyMap
        (((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.mapHomologicalComplex
          (ComplexShape.down ℕ) |>.map phi.hom) i).unop ≫
      (((((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P'.complex).homologyUnop i).inv =
    (((((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex).homologyUnop i).inv ≫
      HomologicalComplex.homologyMap
        (projectiveResolutionLinearYonedaMap P' P phi Y) i
  have hOp := HomologicalComplex.homologyOp_hom_naturality
    (projectiveResolutionLinearYonedaMap P' P phi Y) i
  have hOp' := congr_arg Quiver.Hom.unop hOp
  have hHom :
      (((((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex).homologyUnop i).hom ≫
        (HomologicalComplex.homologyMap
          (((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ) |>.map phi.hom) i).unop =
      HomologicalComplex.homologyMap
          (projectiveResolutionLinearYonedaMap P' P phi Y) i ≫
        (((((linearYoneda R (ModuleCat.{u} R)).obj Y).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P'.complex).homologyUnop i).hom := by
    change
      (HomologicalComplex.homologyMap
          ((HomologicalComplex.opFunctor
            (ModuleCat.{u} R) (ComplexShape.up ℕ)).map
              (projectiveResolutionLinearYonedaMap P' P phi Y).op) i ≫
        (HomologicalComplex.homologyOp
          (P.complex.linearYonedaObj R Y) i).hom).unop =
      ((HomologicalComplex.homologyOp
          (P'.complex.linearYonedaObj R Y) i).hom ≫
        (HomologicalComplex.homologyMap
          (projectiveResolutionLinearYonedaMap P' P phi Y) i).op).unop
    exact hOp'
  have inverseSquare {A B C D : ModuleCat.{u} R}
      (e : A ≅ B) (e' : C ≅ D) (a : B ⟶ D) (b : A ⟶ C)
      (h : e.hom ≫ a = b ≫ e'.hom) : a ≫ e'.inv = e.inv ≫ b := by
    rw [← cancel_epi e.hom, ← Category.assoc, h, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  exact inverseSquare _ _ _ _ hHom

/-- The adjacent positive-degree short-complex map obtained from a lift of
projective resolutions, after forgetting module structure. -/
def projectiveResolutionForgottenLinearYonedaShortComplexSuccMap
    (phi : ProjectiveResolution.Hom P' P f)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    projectiveResolutionForgottenLinearYonedaShortComplexSucc P Y n ⟶
      projectiveResolutionForgottenLinearYonedaShortComplexSucc P' Y n :=
  (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapShortComplex.map
    ((HomologicalComplex.shortComplexFunctor'
      (ModuleCat.{u} R) (ComplexShape.up ℕ) n (n + 1) (n + 2)).map
        (projectiveResolutionLinearYonedaMap P' P phi Y))

/-- Passing from complex homology to the adjacent three-term short complex
is natural for the cochain map induced by a projective-resolution lift. -/
theorem projectiveResolution_homologyIsoScSucc_hom_naturality
    (phi : ProjectiveResolution.Hom P' P f)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    HomologicalComplex.homologyMap
        (projectiveResolutionLinearYonedaMap P' P phi Y) (n + 1) ≫
      ((P'.complex.linearYonedaObj R Y).homologyIsoSc'
        n (n + 1) (n + 2) (by simp) (by simp)).hom =
    ((P.complex.linearYonedaObj R Y).homologyIsoSc'
        n (n + 1) (n + 2) (by simp) (by simp)).hom ≫
      ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor'
          (ModuleCat.{u} R) (ComplexShape.up ℕ)
            n (n + 1) (n + 2)).map
          (projectiveResolutionLinearYonedaMap P' P phi Y)) := by
  let e := HomologicalComplex.homologyFunctorIso'
    (ModuleCat.{u} R) (ComplexShape.up ℕ)
      n (n + 1) (n + 2) (by simp) (by simp)
  have hcomp (Q : HomologicalComplex (ModuleCat.{u} R)
      (ComplexShape.up ℕ)) :
      e.hom.app Q =
        (Q.homologyIsoSc' n (n + 1) (n + 2)
          (by simp) (by simp)).hom := by
    change (𝟙 (Q.homology (n + 1))) ≫
        ShortComplex.homologyMap
          (Q.isoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom =
      ShortComplex.homologyMap
        (Q.isoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom
    exact Category.id_comp _
  have h := e.hom.naturality
    (projectiveResolutionLinearYonedaMap P' P phi Y)
  rw [hcomp, hcomp] at h
  dsimp only [HomologicalComplex.homologyFunctor,
    Functor.comp_map, ShortComplex.homologyFunctor,
    HomologicalComplex.shortComplexFunctor'] at h ⊢
  exact h

/-- A lift between projective resolutions pulls a cocycle back by
precomposition in the corresponding degree. -/
def projectiveResolutionCocycleMapSucc
    (phi : ProjectiveResolution.Hom P' P f)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    AddMonoidHom
      (AddMonoidHom.ker
        (projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P Y n).g.hom)
      (AddMonoidHom.ker
        (projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P' Y n).g.hom) where
  toFun z :=
    ⟨(projectiveResolutionForgottenLinearYonedaShortComplexSuccMap
      P' P phi Y n).τ₂ z.1, by
      change (projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P' Y n).g ((projectiveResolutionForgottenLinearYonedaShortComplexSuccMap
          P' P phi Y n).τ₂ z.1) = 0
      rw [← ConcreteCategory.comp_apply,
        (projectiveResolutionForgottenLinearYonedaShortComplexSuccMap
          P' P phi Y n).comm₂₃,
        ConcreteCategory.comp_apply, z.2, map_zero]⟩
  map_zero' := by
    ext
    exact map_zero _
  map_add' z z' := by
    ext
    exact map_add _ _ _

/-- The concrete kernel description of cycles is natural for the forgotten
short-complex map induced by a projective-resolution lift. -/
theorem projectiveResolutionAbCyclesIsoSucc_naturality
    (phi : ProjectiveResolution.Hom P' P f)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    (projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P Y n).abCyclesIso.inv ≫
      ShortComplex.cyclesMap
        (projectiveResolutionForgottenLinearYonedaShortComplexSuccMap
          P' P phi Y n) ≫
      (projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P' Y n).abCyclesIso.hom =
    AddCommGrpCat.ofHom
      (projectiveResolutionCocycleMapSucc P' P phi Y n) := by
  rw [← cancel_mono
    ((projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P' Y n).abCyclesIso.inv ≫
      (projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P' Y n).iCycles)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  ext z
  simp only [ConcreteCategory.comp_apply]
  calc
    _ = (projectiveResolutionForgottenLinearYonedaShortComplexSuccMap
          P' P phi Y n).τ₂
        ((projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P Y n).iCycles
          ((projectiveResolutionForgottenLinearYonedaShortComplexSucc
            P Y n).abCyclesIso.inv z)) :=
      ConcreteCategory.congr_hom
        (ShortComplex.cyclesMap_i
          (projectiveResolutionForgottenLinearYonedaShortComplexSuccMap
            P' P phi Y n))
        ((projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P Y n).abCyclesIso.inv z)
    _ = (projectiveResolutionForgottenLinearYonedaShortComplexSuccMap
          P' P phi Y n).τ₂ z := by
      rw [(projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P Y n).abCyclesIso_inv_apply_iCycles]
    _ = (projectiveResolutionCocycleMapSucc P' P phi Y n z).1 := rfl
    _ = (projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P' Y n).iCycles
        ((projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P' Y n).abCyclesIso.inv
            (projectiveResolutionCocycleMapSucc P' P phi Y n z)) := by
      rw [(projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P' Y n).abCyclesIso_inv_apply_iCycles]

/-- Elementwise naturality of the cocycle-to-derived-Ext map in the first
variable for a specified lift between projective resolutions. -/
theorem projectiveResolutionCyclesToDerivedExtSucc_naturality_apply
    (phi : ProjectiveResolution.Hom P' P f)
    (Y : ModuleCat.{u} R) (n : ℕ)
    (z : AddMonoidHom.ker
      (projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P Y n).g.hom) :
    derivedExtContravariantMap f Y (n + 1)
        (projectiveResolutionCyclesToDerivedExtSucc P Y n z) =
      projectiveResolutionCyclesToDerivedExtSucc P' Y n
        (projectiveResolutionCocycleMapSucc P' P phi Y n z) := by
  change
    (CategoryTheory.Abelian.Ext.mk₀ f).comp
        (P.extMk z.1 (n + 2) (by omega) (by
          change P.complex.d (n + 2) (n + 1) ≫ z.1 = 0
          exact z.2)) (zero_add (n + 1)) =
      P'.extMk (phi.hom.f (n + 1) ≫ z.1)
        (n + 2) (by omega) (by
          change P'.complex.d (n + 2) (n + 1) ≫
            (projectiveResolutionCocycleMapSucc P' P phi Y n z).1 = 0
          exact (projectiveResolutionCocycleMapSucc P' P phi Y n z).2)
  apply P.mk₀_comp_extMk

/-- The cocycle-to-derived-Ext map is natural in the first variable for a
specified lift between projective resolutions. -/
theorem projectiveResolutionCyclesToDerivedExtSucc_naturality
    (phi : ProjectiveResolution.Hom P' P f)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    AddCommGrpCat.ofHom
        (projectiveResolutionCyclesToDerivedExtSucc P Y n) ≫
      derivedExtContravariantMap f Y (n + 1) =
    AddCommGrpCat.ofHom
        (projectiveResolutionCocycleMapSucc P' P phi Y n) ≫
      AddCommGrpCat.ofHom
        (projectiveResolutionCyclesToDerivedExtSucc P' Y n) := by
  ext z
  exact projectiveResolutionCyclesToDerivedExtSucc_naturality_apply
    P' P phi Y n z

/-- The cocycle pullback induced by a lift descends to the corresponding
quotients by coboundaries. -/
def projectiveResolutionCocycleQuotientMapSucc
    (phi : ProjectiveResolution.Hom P' P f)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    ((AddMonoidHom.ker
        (projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P Y n).g.hom) ⧸
      AddMonoidHom.range
        (projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P Y n).abToCycles) →+
    ((AddMonoidHom.ker
        (projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P' Y n).g.hom) ⧸
      AddMonoidHom.range
        (projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P' Y n).abToCycles) :=
  QuotientAddGroup.lift
    (AddMonoidHom.range
      (projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P Y n).abToCycles)
    ((QuotientAddGroup.mk'
      (AddMonoidHom.range
        (projectiveResolutionForgottenLinearYonedaShortComplexSucc
          P' Y n).abToCycles)).comp
      (projectiveResolutionCocycleMapSucc P' P phi Y n)) (by
        intro z hz
        rw [AddMonoidHom.mem_ker]
        change (QuotientAddGroup.mk'
          (AddMonoidHom.range
            (projectiveResolutionForgottenLinearYonedaShortComplexSucc
              P' Y n).abToCycles)
          ((projectiveResolutionCocycleMapSucc P' P phi Y n) z)) = 0
        apply (QuotientAddGroup.eq_zero_iff _).2
        rw [AddMonoidHom.mem_range]
        rw [AddMonoidHom.mem_range] at hz
        obtain ⟨g, rfl⟩ := hz
        let α :=
          projectiveResolutionForgottenLinearYonedaShortComplexSuccMap
            P' P phi Y n
        refine ⟨α.τ₁ g, ?_⟩
        apply Subtype.ext
        exact ConcreteCategory.congr_hom α.comm₁₂ g)

@[simp]
theorem projectiveResolutionCocycleQuotientMapSucc_mk
    (phi : ProjectiveResolution.Hom P' P f)
    (Y : ModuleCat.{u} R) (n : ℕ)
    (z : AddMonoidHom.ker
      (projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P Y n).g.hom) :
    projectiveResolutionCocycleQuotientMapSucc P' P phi Y n
        (QuotientAddGroup.mk'
          (AddMonoidHom.range
            (projectiveResolutionForgottenLinearYonedaShortComplexSucc
              P Y n).abToCycles) z) =
      QuotientAddGroup.mk'
        (AddMonoidHom.range
          (projectiveResolutionForgottenLinearYonedaShortComplexSucc
            P' Y n).abToCycles)
        (projectiveResolutionCocycleMapSucc P' P phi Y n z) :=
  rfl

/-- The explicit cocycle-quotient description of forgotten short-complex
homology is natural for a projective-resolution lift. -/
theorem projectiveResolutionAbHomologyIsoSucc_naturality
    (phi : ProjectiveResolution.Hom P' P f)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    ShortComplex.homologyMap
        (projectiveResolutionForgottenLinearYonedaShortComplexSuccMap
          P' P phi Y n) ≫
      (projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P' Y n).abHomologyIso.hom =
    (projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P Y n).abHomologyIso.hom ≫
      AddCommGrpCat.ofHom
        (projectiveResolutionCocycleQuotientMapSucc P' P phi Y n) := by
  let S := projectiveResolutionForgottenLinearYonedaShortComplexSucc P Y n
  let S' := projectiveResolutionForgottenLinearYonedaShortComplexSucc P' Y n
  let alpha := projectiveResolutionForgottenLinearYonedaShortComplexSuccMap
    P' P phi Y n
  let c := projectiveResolutionCocycleMapSucc P' P phi Y n
  let q := projectiveResolutionCocycleQuotientMapSucc P' P phi Y n
  change ShortComplex.homologyMap alpha ≫ S'.abHomologyIso.hom =
    S.abHomologyIso.hom ≫ AddCommGrpCat.ofHom q
  have hCycles :
      S.abCyclesIso.inv ≫ ShortComplex.cyclesMap alpha ≫
          S'.abCyclesIso.hom =
        AddCommGrpCat.ofHom c := by
    simpa only [S, S', alpha, c] using
      projectiveResolutionAbCyclesIsoSucc_naturality P' P phi Y n
  have hCycles' :
      ShortComplex.cyclesMap alpha ≫ S'.abCyclesIso.hom =
        S.abCyclesIso.hom ≫ AddCommGrpCat.ofHom c := by
    rw [← cancel_epi S.abCyclesIso.inv, hCycles,
      Iso.inv_hom_id_assoc]
  have hπ (T : ShortComplex AddCommGrpCat.{u}) :
      T.homologyπ ≫ T.abHomologyIso.hom =
        T.abCyclesIso.hom ≫
          AddCommGrpCat.ofHom
            (QuotientAddGroup.mk' (AddMonoidHom.range T.abToCycles)) := by
    exact T.abLeftHomologyData.homologyπ_comp_homologyIso_hom
  rw [← cancel_epi S.homologyπ]
  rw [ShortComplex.homologyπ_naturality_assoc, hπ S']
  conv_rhs => rw [← Category.assoc, hπ S]
  rw [← Category.assoc, hCycles']
  simp only [Category.assoc]
  congr 1

@[simp]
theorem projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc_mk
    (Q : ProjectiveResolution X) (Y : ModuleCat.{u} R) (n : ℕ)
    (z : AddMonoidHom.ker
      (projectiveResolutionForgottenLinearYonedaShortComplexSucc
        Q Y n).g.hom) :
    projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc Q Y n
        (QuotientAddGroup.mk'
          (AddMonoidHom.range
            (projectiveResolutionForgottenLinearYonedaShortComplexSucc
              Q Y n).abToCycles) z) =
      projectiveResolutionCyclesToDerivedExtSucc Q Y n z :=
  rfl

/-- The positive-degree cocycle-quotient equivalence with derived Ext is
natural in the first variable for a specified lift of projective
resolutions. -/
theorem projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc_naturality
    (phi : ProjectiveResolution.Hom P' P f)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    AddCommGrpCat.ofHom
        (projectiveResolutionCocycleQuotientMapSucc P' P phi Y n) ≫
      (projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc
        P' Y n).toAddCommGrpIso.hom =
    (projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc
        P Y n).toAddCommGrpIso.hom ≫
      derivedExtContravariantMap f Y (n + 1) := by
  ext z
  change
    projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc P' Y n
        (projectiveResolutionCocycleQuotientMapSucc P' P phi Y n
          (QuotientAddGroup.mk'
            (AddMonoidHom.range
              (projectiveResolutionForgottenLinearYonedaShortComplexSucc
                P Y n).abToCycles) z)) =
      derivedExtContravariantMap f Y (n + 1)
        (projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc P Y n
          (QuotientAddGroup.mk'
            (AddMonoidHom.range
              (projectiveResolutionForgottenLinearYonedaShortComplexSucc
                P Y n).abToCycles) z))
  rw [projectiveResolutionCocycleQuotientMapSucc_mk,
    projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc_mk,
    projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc_mk]
  exact (projectiveResolutionCyclesToDerivedExtSucc_naturality_apply
    P' P phi Y n z).symm

/-- The full positive-degree comparison from forgotten legacy Ext to
derived-category Ext is natural in the first variable for a specified lift
of projective resolutions. -/
theorem projectiveResolutionForgottenLegacyExtIsoDerivedExtSucc_naturality
    (phi : ProjectiveResolution.Hom P' P f)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (((_root_.Ext R (ModuleCat.{u} R) (n + 1)).map f.op).app Y) ≫
      (projectiveResolutionForgottenLegacyExtIsoDerivedExtSucc
        P' Y n).hom =
    (projectiveResolutionForgottenLegacyExtIsoDerivedExtSucc
        P Y n).hom ≫
      derivedExtContravariantMap f Y (n + 1) := by
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let beta :=
    (HomologicalComplex.shortComplexFunctor'
      (ModuleCat.{u} R) (ComplexShape.up ℕ)
        n (n + 1) (n + 2)).map
      (projectiveResolutionLinearYonedaMap P' P phi Y)
  have hIsoExt :
      F.map (((_root_.Ext R (ModuleCat.{u} R) (n + 1)).map f.op).app Y) ≫
          F.map (P'.isoExt (n + 1) Y).hom =
        F.map (P.isoExt (n + 1) Y).hom ≫
          F.map (HomologicalComplex.homologyMap
            (projectiveResolutionLinearYonedaMap P' P phi Y) (n + 1)) := by
    rw [← F.map_comp, projectiveResolution_isoExt_hom_naturality
      P' P phi Y (n + 1), F.map_comp]
  have hSc :
      F.map (HomologicalComplex.homologyMap
          (projectiveResolutionLinearYonedaMap P' P phi Y) (n + 1)) ≫
        F.map ((P'.complex.linearYonedaObj R Y).homologyIsoSc'
          n (n + 1) (n + 2) (by simp) (by simp)).hom =
      F.map ((P.complex.linearYonedaObj R Y).homologyIsoSc'
          n (n + 1) (n + 2) (by simp) (by simp)).hom ≫
        F.map (ShortComplex.homologyMap beta) := by
    rw [← F.map_comp,
      projectiveResolution_homologyIsoScSucc_hom_naturality
        P' P phi Y n, F.map_comp]
  have hMapHomology :
      F.map (ShortComplex.homologyMap beta) ≫
          (((P'.complex.linearYonedaObj R Y).sc'
            n (n + 1) (n + 2)).mapHomologyIso F).inv =
        (((P.complex.linearYonedaObj R Y).sc'
            n (n + 1) (n + 2)).mapHomologyIso F).inv ≫
          ShortComplex.homologyMap
            (projectiveResolutionForgottenLinearYonedaShortComplexSuccMap
              P' P phi Y n) := by
    simpa only [F, beta,
      projectiveResolutionForgottenLinearYonedaShortComplexSuccMap] using
      ShortComplex.mapHomologyIso_inv_naturality beta F
  have hAb := projectiveResolutionAbHomologyIsoSucc_naturality
    P' P phi Y n
  have hQuotient :=
    projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc_naturality
      P' P phi Y n
  simp only [projectiveResolutionForgottenLegacyExtIsoDerivedExtSucc,
    Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% hIsoExt, reassoc_of% hSc]
  rw [cancel_epi, cancel_epi]
  change
    F.map (ShortComplex.homologyMap beta) ≫
        (((P'.complex.linearYonedaObj R Y).sc'
          n (n + 1) (n + 2)).mapHomologyIso F).inv ≫
        (((P'.complex.linearYonedaObj R Y).sc'
          n (n + 1) (n + 2)).map F).abHomologyIso.hom ≫
        (projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc
          P' Y n).toAddCommGrpIso.hom =
      (((P.complex.linearYonedaObj R Y).sc'
          n (n + 1) (n + 2)).mapHomologyIso F).inv ≫
        (((P.complex.linearYonedaObj R Y).sc'
          n (n + 1) (n + 2)).map F).abHomologyIso.hom ≫
        (projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc
          P Y n).toAddCommGrpIso.hom ≫
        derivedExtContravariantMap f Y (n + 1)
  rw [reassoc_of% hMapHomology]
  rw [cancel_epi]
  change
    ShortComplex.homologyMap
        (projectiveResolutionForgottenLinearYonedaShortComplexSuccMap
          P' P phi Y n) ≫
      (projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P' Y n).abHomologyIso.hom ≫
      (projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc
        P' Y n).toAddCommGrpIso.hom =
    (projectiveResolutionForgottenLinearYonedaShortComplexSucc
        P Y n).abHomologyIso.hom ≫
      (projectiveResolutionCocycleQuotientAddEquivDerivedExtSucc
        P Y n).toAddCommGrpIso.hom ≫
      derivedExtContravariantMap f Y (n + 1)
  rw [reassoc_of% hAb, hQuotient]

end FirstVariableNaturality

/-- Legacy Ext in the first variable, after evaluating the second variable
and forgetting the module structure. -/
def forgottenLegacyExtContravariantFunctor
    (Y : ModuleCat.{u} R) (i : ℕ) :
    (ModuleCat.{u} R)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  _root_.Ext R (ModuleCat.{u} R) i ⋙
    (evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj Y ⋙
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- The canonical lift of a morphism to the chosen projective resolutions,
packaged with its augmentation compatibility. -/
def projectiveResolutionLiftHom
    {X' X : ModuleCat.{u} R} (f : X' ⟶ X)
    (P' : ProjectiveResolution X') (P : ProjectiveResolution X) :
    ProjectiveResolution.Hom P' P f where
  hom := ProjectiveResolution.lift f P' P
  hom_f_zero_comp_π_f_zero := by
    simpa using ProjectiveResolution.lift_commutes_zero f P' P

/-- The positive-degree comparison at an object, using Mathlib's chosen
projective resolution. -/
def forgottenLegacyExtIsoDerivedExtSucc
    (X Y : ModuleCat.{u} R) (n : ℕ) :
    (forgottenLegacyExtContravariantFunctor Y (n + 1)).obj (op X) ≅
      (derivedExtContravariantFunctor Y (n + 1)).obj (op X) :=
  projectiveResolutionForgottenLegacyExtIsoDerivedExtSucc
    (CategoryTheory.projectiveResolution X) Y n

/-- In positive degree, forgotten legacy Ext and derived-category Ext are
naturally isomorphic as contravariant functors of the first variable. -/
def forgottenLegacyExtNatIsoDerivedExtSucc
    (Y : ModuleCat.{u} R) (n : ℕ) :
    forgottenLegacyExtContravariantFunctor Y (n + 1) ≅
      derivedExtContravariantFunctor Y (n + 1) :=
  NatIso.ofComponents
    (fun Xop => forgottenLegacyExtIsoDerivedExtSucc (unop Xop) Y n)
    (fun {Xop Xop'} f => by
      let P' := CategoryTheory.projectiveResolution (unop Xop')
      let P := CategoryTheory.projectiveResolution (unop Xop)
      let phi := projectiveResolutionLiftHom f.unop P' P
      change
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
              (((_root_.Ext R (ModuleCat.{u} R) (n + 1)).map f).app Y) ≫
            (projectiveResolutionForgottenLegacyExtIsoDerivedExtSucc
              P' Y n).hom =
          (projectiveResolutionForgottenLegacyExtIsoDerivedExtSucc
              P Y n).hom ≫
            ((CategoryTheory.Abelian.extFunctor (C := ModuleCat.{u} R)
              (n + 1)).map f).app Y
      have hDerived :
          ((CategoryTheory.Abelian.extFunctor (C := ModuleCat.{u} R)
              (n + 1)).map f).app Y =
            derivedExtContravariantMap f.unop Y (n + 1) := by
        ext z
        rfl
      rw [hDerived]
      dsimp only [CategoryTheory.Abelian.extFunctor, CategoryTheory.Abelian.extFunctorObj]
      simpa only [Quiver.Hom.op_unop, Opposite.op_unop] using
        projectiveResolutionForgottenLegacyExtIsoDerivedExtSucc_naturality
          P' P phi Y n)

/-- The powers diagram of positive-degree legacy Ext, evaluated at a module
and then regarded as a diagram of additive commutative groups. -/
def forgottenLegacyLocalCohomologyPowersDiagram
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    (ℕᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (localCohomology.ringModIdeals
      (localCohomology.idealPowersDiagram I)).op ⋙
    forgottenLegacyExtContravariantFunctor M i

/-- At every positive degree, the evaluated forgotten legacy-Ext powers
diagram is naturally isomorphic to the derived-Ext powers diagram. -/
def forgottenLegacyLocalCohomologyPowersDiagramIsoDerivedSucc
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    forgottenLegacyLocalCohomologyPowersDiagram I M (n + 1) ≅
      derivedLocalCohomologyPowersDiagram I M (n + 1) :=
  Functor.isoWhiskerLeft
    (localCohomology.ringModIdeals
      (localCohomology.idealPowersDiagram I)).op
    (forgottenLegacyExtNatIsoDerivedExtSucc M n)

/-- The colimit of the evaluated forgotten legacy-Ext powers diagram is
canonically isomorphic to positive-degree derived local cohomology. -/
def forgottenLegacyLocalCohomologyPowersColimitIsoDerivedSucc
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    colimit (forgottenLegacyLocalCohomologyPowersDiagram I M (n + 1)) ≅
      derivedLocalCohomology I M (n + 1) :=
  HasColimit.isoOfNatIso
    (forgottenLegacyLocalCohomologyPowersDiagramIsoDerivedSucc I M n)

/-- Forgetting the legacy local-cohomology module commutes with its defining
ideal-powers colimit. -/
def forgottenLegacyLocalCohomologyIsoPowersColimit
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        ((localCohomology I i).obj M) ≅
      colimit (forgottenLegacyLocalCohomologyPowersDiagram I M i) :=
  let D := localCohomology.diagram
    (localCohomology.idealPowersDiagram I) i
  let E := (evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj M
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  F.mapIso (colimitObjIsoColimitCompEvaluation D M) ≪≫
    preservesColimitIso F (D ⋙ E) ≪≫
    HasColimit.isoOfNatIso (Functor.associator D E F) ≪≫
    HasColimit.isoOfNatIso
      (Functor.associator
        (localCohomology.ringModIdeals
          (localCohomology.idealPowersDiagram I)).op
        (_root_.Ext R (ModuleCat.{u} R) i) (E ⋙ F))

/-- In positive degree, derived local cohomology is canonically isomorphic
to Mathlib's legacy local-cohomology module after forgetting scalars. -/
def forgottenLegacyLocalCohomologyIsoDerivedSucc
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        ((localCohomology I (n + 1)).obj M) ≅
      derivedLocalCohomology I M (n + 1) :=
  forgottenLegacyLocalCohomologyIsoPowersColimit I M (n + 1) ≪≫
    forgottenLegacyLocalCohomologyPowersColimitIsoDerivedSucc I M n

end PositiveDegree

end EtaleFundamentalGroups

end
