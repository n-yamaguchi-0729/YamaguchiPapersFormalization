/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
The iterated-pullback and fibre calculations are adapted from:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelSubPicBaseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Copyright (c) 2026 Naganori Yamaguchi.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the unrigidified comparison: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import AlgebraicCurves.Geometry.Picard.Unrigidified
import AlgebraicCurves.Geometry.Picard.UnrigidifiedAlgEquivZero
import AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import SchemeTheory.Modules.Monoidal
import SchemeTheory.Modules.PullbackMonoidal

/-!
# Base change of unrigidified Picard classes

The canonical isomorphism between iterated pullbacks identifies relative classes
over an extended base with restriction of the original presheaf. The comparison
preserves the actual geometric-fibre condition and requires no rational point.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra
open AlgebraicGeometry.RelPicard.BaseChange

noncomputable section

namespace AlgebraicGeometry.RelPicard.Unrigidified

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R))
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- View an invertible module on the scalar-extended curve over the original base. -/
def restrictBundle {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')}
    (M : LineBundle (baseChange R c R') t) : LineBundle c (t ≫ specMap R R') :=
  ⟨(Scheme.Modules.pullback (κ c R' t).inv).obj M.1, M.2.pullback (κ c R' t).inv⟩

/-- Transport an invertible module to the scalar-extended curve. -/
def extendBundle {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')}
    (M : LineBundle c (t ≫ specMap R R')) : LineBundle (baseChange R c R') t :=
  ⟨(Scheme.Modules.pullback (κ c R' t).hom).obj M.1, M.2.pullback (κ c R' t).hom⟩

theorem baseTwist_restrict {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')}
    {M N : LineBundle (baseChange R c R') t} (h : BaseTwist (baseChange R c R') t M N) :
    BaseTwist c (t ≫ specMap R R') (restrictBundle c R' M) (restrictBundle c R' N) := by
  obtain ⟨Q, hQ, ⟨e⟩⟩ := h
  have hsnd : (κ c R' t).inv ≫ pullback.snd (baseChange R c R') t =
      pullback.snd c (t ≫ specMap R R') := by
    rw [← κ_hom_snd c R' t, Iso.inv_hom_id_assoc]
  exact ⟨Q, hQ, ⟨(Scheme.Modules.pullback (κ c R' t).inv).mapIso e ≪≫
    Scheme.Modules.pullbackTensorObjIso (κ c R' t).inv _ M.1 ≪≫
    (((Scheme.Modules.pullbackComp _ _).app Q ≪≫
      (Scheme.Modules.pullbackCongr hsnd).app Q) ⊗ᵢ Iso.refl _)⟩⟩

theorem baseTwist_extend {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')}
    {M N : LineBundle c (t ≫ specMap R R')} (h : BaseTwist c (t ≫ specMap R R') M N) :
    BaseTwist (baseChange R c R') t (extendBundle c R' M) (extendBundle c R' N) := by
  obtain ⟨Q, hQ, ⟨e⟩⟩ := h
  exact ⟨Q, hQ, ⟨(Scheme.Modules.pullback (κ c R' t).hom).mapIso e ≪≫
    Scheme.Modules.pullbackTensorObjIso (κ c R' t).hom _ M.1 ≪≫
    (((Scheme.Modules.pullbackComp _ _).app Q ≪≫
      (Scheme.Modules.pullbackCongr (κ_hom_snd c R' t)).app Q) ⊗ᵢ Iso.refl _)⟩⟩

/-- The actual equivalence of relative classes across the canonical pullback isomorphism. -/
def baseChangeClassesEquiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    Classes (baseChange R c R') t ≃ Classes c (t ≫ specMap R R') where
  toFun := Quot.map (restrictBundle c R') (fun _ _ h => baseTwist_restrict c R' h)
  invFun := Quot.map (extendBundle c R') (fun _ _ h => baseTwist_extend c R' h)
  left_inv x := by
    induction x using Quot.ind with
    | _ M =>
      exact Quot.sound (baseTwist_of_iso
        ((Scheme.Modules.pullbackComp (κ c R' t).hom (κ c R' t).inv).app M.1 ≪≫
          (Scheme.Modules.pullbackCongr (κ c R' t).hom_inv_id).app M.1 ≪≫
          (Scheme.Modules.pullbackId _).app M.1))
  right_inv x := by
    induction x using Quot.ind with
    | _ M =>
      exact Quot.sound (baseTwist_of_iso
        ((Scheme.Modules.pullbackComp (κ c R' t).inv (κ c R' t).hom).app M.1 ≪≫
          (Scheme.Modules.pullbackCongr (κ c R' t).inv_hom_id).app M.1 ≪≫
          (Scheme.Modules.pullbackId _).app M.1))

/-- Base change of the unrigidified relative Picard presheaf. -/
def baseChangeIso :
    presheaf (baseChange R c R') ≅ (Over.map (specMap R R')).op ⋙ presheaf c :=
  NatIso.ofComponents (fun X => Equiv.toIso (baseChangeClassesEquiv c R' X.unop.hom))
    (fun {X Y} φ => by
      apply TypeCat.homEquiv.injective
      funext x
      induction x using Quot.ind with
      | _ M =>
        let ψ : SchemeHomOver Y.unop.hom X.unop.hom := ⟨φ.unop.left, Over.w φ.unop⟩
        exact Quot.sound (baseTwist_of_iso
          ((Scheme.Modules.pullbackComp (κ c R' Y.unop.hom).inv
              (baseChangeSnd (baseChange R c R') ψ)).app M.1 ≪≫
            (Scheme.Modules.pullbackCongr (baseChangeSnd_κ_inv c R' ψ).symm).app M.1 ≪≫
            ((Scheme.Modules.pullbackComp (baseChangeSnd c (overR R' ψ))
              (κ c R' X.unop.hom).inv).app M.1).symm)))

theorem fibrewiseZero_restrict_iff {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')}
    (M : LineBundle (baseChange R c R') t) :
    FibrewiseZero (restrictBundle c R' M) ↔ FibrewiseZero M := by
  constructor
  · intro h k _ _ s
    have h1 := (h k s).pullback (fibreMap c R' t s) (fibreMap_fibreAt c R' t s)
    refine h1.of_iso ?_
    exact (Scheme.Modules.pullbackComp (fibreMap c R' t s)
        (pullback.fst (pullback.snd c (t ≫ specMap R R')) s)).app _ ≪≫
      (Scheme.Modules.pullbackComp
        (fibreMap c R' t s ≫ pullback.fst (pullback.snd c (t ≫ specMap R R')) s)
        (κ c R' t).inv).app M.1 ≪≫
      (Scheme.Modules.pullbackCongr (by
        rw [fibreMap_fst, Category.assoc, Iso.hom_inv_id, Category.comp_id])).app M.1
  · intro h k _ _ s
    have h1 := (h k s).pullback (fibreMap' c R' t s) (fibreMap'_fibreAt c R' t s)
    refine h1.of_iso ?_
    exact (Scheme.Modules.pullbackComp (fibreMap' c R' t s)
        (pullback.fst (pullback.snd (baseChange R c R') t) s)).app M.1 ≪≫
      (Scheme.Modules.pullbackCongr (fibreMap'_fst c R' t s)).app M.1 ≪≫
      ((Scheme.Modules.pullbackComp
        (pullback.fst (pullback.snd c (t ≫ specMap R R')) s) (κ c R' t).inv).app M.1).symm

theorem classesZero_baseChange_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
    (x : Classes (baseChange R c R') t) :
    classesZero (t ≫ specMap R R') (baseChangeClassesEquiv c R' t x) ↔ classesZero t x := by
  induction x using Quot.ind with
  | _ M => exact fibrewiseZero_restrict_iff c R' M

/-- The geometric-fibre condition cuts out corresponding subsets on either base. -/
def zeroBaseChangeClassesEquiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    {x : Classes (baseChange R c R') t // classesZero t x} ≃
      {x : Classes c (t ≫ specMap R R') // classesZero (t ≫ specMap R R') x} where
  toFun x := ⟨baseChangeClassesEquiv c R' t x.1, (classesZero_baseChange_iff c R' t x.1).2 x.2⟩
  invFun y := ⟨(baseChangeClassesEquiv c R' t).symm y.1,
    (classesZero_baseChange_iff c R' t _).1 (by
      rw [Equiv.apply_symm_apply]
      exact y.2)⟩
  left_inv x := Subtype.ext ((baseChangeClassesEquiv c R' t).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((baseChangeClassesEquiv c R' t).apply_symm_apply y.1)

/-- Base change of the unrigidified Picard-zero presheaf, without any choice of section. -/
def zeroBaseChangeIso :
    zeroPresheaf (baseChange R c R') ≅ (Over.map (specMap R R')).op ⋙ zeroPresheaf c :=
  NatIso.ofComponents (fun X => Equiv.toIso (zeroBaseChangeClassesEquiv c R' X.unop.hom))
    (fun {X Y} φ => by
      apply TypeCat.homEquiv.injective
      funext x
      apply Subtype.ext
      exact congrArg (fun f => f x.1) ((baseChangeIso c R').hom.naturality φ))

end AlgebraicGeometry.RelPicard.Unrigidified
