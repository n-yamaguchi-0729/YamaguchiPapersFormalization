/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLawGrpObj
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange
/-!
# Compatibility of relative Picard multiplication with base change

The comparison of Poincaré bundles under base change identifies the multiplication
laws on points of the two representing schemes.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.BaseChangeGroupLaw

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard.BaseChange


open scoped CategoryTheory.MonObj

namespace GrpBCLawSol

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

/-- Comparison of iterated pullback with pullback along the composite base morphism. -/
noncomputable def pullbackAlongComp {T T' T'' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {t'' : T'' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (φ : SchemeHomOver t' t) (ψ : SchemeHomOver t'' t') :
    ((M.pullbackAlong φ).pullbackAlong ψ).L ≅ (M.pullbackAlong (postComp φ ψ)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c ψ) (baseChangeSnd c φ)).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c φ ψ)).app M.L

/-- Equal underlying base morphisms induce isomorphic pulled-back line bundles. -/
noncomputable def pullbackAlongCongr {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) {φ ψ : SchemeHomOver t' t}
    (e : φ.1 = ψ.1) : (M.pullbackAlong φ).L ≅ (M.pullbackAlong ψ).L :=
  eqToIso (by cases φ; cases ψ; cases e; rfl)

end GrpBCLawSol

open GrpBCLawSol in
theorem _root_.AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (x y : SchemeHomOver t' (D.baseChange R').toBase)
    (x₁ y₁ : SchemeHomOver (t' ≫ specMap R R') D.toBase)
    (hx : x₁.1 = x.1 ≫ pullback.fst D.toBase (specMap R R'))
    (hy : y₁.1 = y.1 ≫ pullback.fst D.toBase (specMap R R')) :
    ((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').mul
          t' x y).1 ≫
        pullback.fst D.toBase (specMap R R') =
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul
        (t' ≫ specMap R R') x₁ y₁).1 := by
  classical
  let hg : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D := h
  let hg' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)).toSubPicCondition
      (D.baseChange R') := h'
  let := hg'.grpObj
  let := hg.grpObj
  let ψ₀ : SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  let Θ : SchemeHomOver t' (D.baseChange R').toBase → SchemeHomOver (t' ≫ specMap R R') D.toBase :=
    fun z => postComp ψ₀ (overR R' z)
  have hΘ : ∀ z, (Θ z).1 = z.1 ≫ pullback.fst D.toBase (specMap R R') := fun z => rfl
  obtain rfl : x₁ = Θ x := Subtype.ext (hx.trans (hΘ x).symm)
  obtain rfl : y₁ = Θ y := Subtype.ext (hy.trans (hΘ y).symm)
  let P' : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε)
      (D.baseChange R').toBase :=
    ofR c ε R' (h.poincare.pullbackAlong ψ₀)
  have chain : ∀ (z : SchemeHomOver t' (D.baseChange R').toBase),
      (toR c ε R' (P'.pullbackAlong z)).L ≅ (h.poincare.pullbackAlong (Θ z)).L :=
    fun z => (toR_pullbackAlong_iso c ε R' z P').symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c (overR R' z))).mapIso (toR_ofR_iso c ε R' _) ≪≫
      pullbackAlongComp h.poincare ψ₀ (overR R' z)
  have poinc : ∀ z : SchemeHomOver t' (D.baseChange R').toBase,
      (toR c ε R' (h'.poincare.pullbackAlong z)).L ≅ (h.poincare.pullbackAlong (Θ z)).L :=
    fun z =>
      (Scheme.Modules.pullback (κ c R' t').inv).mapIso
          ((Scheme.Modules.pullback (baseChangeSnd (baseChange R c R') z)).mapIso hP.some) ≪≫
        chain z
  let a : Over.mk t' ⟶ Over.mk (D.baseChange R').toBase := schemeHomOverToOverHom x
  let b : Over.mk t' ⟶ Over.mk (D.baseChange R').toBase := schemeHomOverToOverHom y
  obtain ⟨i₂⟩ := hg'.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk t') a b
  obtain ⟨i₁⟩ := hg.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk (t' ≫ specMap R R'))
    (schemeHomOverToOverHom (Θ x)) (schemeHomOverToOverHom (Θ y))
  suffices key : Θ (hg'.relativeGroupLaw.mul t' x y) =
      hg.relativeGroupLaw.mul (t' ≫ specMap R R') (Θ x) (Θ y) by
    exact (hΘ _).symm.trans (congrArg Subtype.val key)
  refine hg.ext_of_iso (t' ≫ specMap R R') _ _ ⟨?_⟩
  exact (poinc (hg'.relativeGroupLaw.mul t' x y)).symm ≪≫
    (Scheme.Modules.pullback (κ c R' t').inv).mapIso i₂ ≪≫
    Scheme.Modules.pullbackTensorObjIso (κ c R' t').inv _ _ ≪≫
    (poinc x ⊗ᵢ poinc y) ≪≫ i₁.symm
end JacobianVarieties.Picard.Proofs.BaseChangeGroupLaw
end ProofImplementation
