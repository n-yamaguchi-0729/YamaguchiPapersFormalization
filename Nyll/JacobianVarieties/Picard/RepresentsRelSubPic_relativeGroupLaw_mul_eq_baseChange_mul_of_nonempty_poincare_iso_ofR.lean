/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange
/-!
# Compatibility of the relative Picard group law with base change

The comparison between the Poincare bundles transports tensor products along base change.
It identifies the multiplication represented after base change with the base-changed group law.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.LawBC

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.GoodReductionJacobian



open _root_.CategoryTheory.MonoidalCategory


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.pullback
  Spec
  Scheme
  Scheme.Modules.pullbackCongr
  Scheme.Modules
  Scheme.Modules.pullbackComp
  RelPicard.BaseChange.κ
  Scheme.Modules.pullbackTensorObjIso)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  baseChangeSnd
  postComp
  baseChangeSnd_comp
  RigidifiedLineBundle
  RepresentsRelSubPic
  algEquivZeroCut
  BaseChange.κ
  BaseChange.ofR
  algEquivZeroGroupCut
  RepresentsRelSubPic.relativeGroupLaw
  RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso)

namespace BaseChange

export _root_.AlgebraicGeometry.RelPicard.BaseChange (
  κ
  overR
  baseChangeSnd_κ_hom
  toR
  ofR
  toR_ofR_iso)


open _root_.AlgebraicGeometry.RelPicard.BaseChange
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry


variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (R' : Type u) [CommRing R'] [Algebra R R']

/-- Base change of a rigidified line bundle commutes with pullback along points. -/
noncomputable def LAW_ofR_pullbackAlong_iso {T T'' : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    {t'' : T'' ⟶ Spec (CommRingCat.of R')} (ψ : SchemeHomOver t'' t')
    (X : RigidifiedLineBundle c ε (t' ≫ specMap R R')) :
    ((ofR c ε R' X).pullbackAlong ψ).L ≅ (ofR c ε R' (X.pullbackAlong (overR R' ψ))).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd (baseChange R c R') ψ) (κ c R' t').hom).app X.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_κ_hom c R' ψ)).app X.L ≪≫
    ((Scheme.Modules.pullbackComp (κ c R' t'').hom (baseChangeSnd c (overR R' ψ))).app X.L).symm

omit [Algebra R R'] in
/-- Iterated pullback of a rigidified line bundle agrees with pullback along the composite. -/
noncomputable def LAW_pullbackAlong_pullbackAlong_iso {X₀ X₁ X₂ : Scheme.{u}}
    {x₀ : X₀ ⟶ Spec (CommRingCat.of R)}
    {x₁ : X₁ ⟶ Spec (CommRingCat.of R)} {x₂ : X₂ ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε x₀) (φ : SchemeHomOver x₁ x₀) (ψ : SchemeHomOver x₂ x₁) :
    ((M.pullbackAlong φ).pullbackAlong ψ).L ≅ (M.pullbackAlong (postComp φ ψ)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c ψ) (baseChangeSnd c φ)).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c φ ψ)).app M.L

/-- Transport of a Poincare fibre back to the base through the given base-change comparison. -/
noncomputable def LAW_transportIso {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
        (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (e : h'.poincare.L ≅ (BaseChange.ofR c ε R'
        (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (z : SchemeHomOver t' (D.baseChange R').toBase) :
    (toR c ε R' (h'.poincare.pullbackAlong z)).L ≅
      (h.poincare.pullbackAlong (RelativeGroupLaw.baseChangePointToBase (specMap R R') z)).L :=
  ((Scheme.Modules.pullback (κ c R' t').inv).mapIso
      ((Scheme.Modules.pullback (baseChangeSnd (baseChange R c R') z)).mapIso e ≪≫
        LAW_ofR_pullbackAlong_iso c ε R' z _) ≪≫
    toR_ofR_iso c ε R' _ ≪≫
    LAW_pullbackAlong_pullbackAlong_iso c ε h.poincare _ _ : _)

end AlgebraicGeometry.RelPicard.BaseChange

open _root_.JacobianVarieties.Picard.Proofs.LawBC.AlgebraicGeometry.RelPicard.BaseChange in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic
theorem relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
        (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
        (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L)) :
    ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (x y : SchemeHomOver t' (D.baseChange R').toBase),
      (RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').mul t' x y =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).baseChange
          (specMap R R')).mul t' x y := by
  intro T t' x y
  obtain ⟨e⟩ := hP
  rw [RelativeGroupLaw.baseChange_mul]
  apply (RelativeGroupLaw.baseChangePointEquiv (specMap R R') t').injective
  change RelativeGroupLaw.baseChangePointToBase (specMap R R') _ =
    RelativeGroupLaw.baseChangePointToBase (specMap R R') _
  rw [RelativeGroupLaw.baseChangePointToBase_ofBase]
  apply h.ext_of_iso (t' ≫ specMap R R')
  obtain ⟨m'⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso
    (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h'
    (T := Over.mk t') (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
  obtain ⟨m⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso
    (P := algEquivZeroGroupCut c ε) h
    (T := Over.mk (t' ≫ specMap R R'))
    (schemeHomOverToOverHom (RelativeGroupLaw.baseChangePointToBase (specMap R R') x))
    (schemeHomOverToOverHom (RelativeGroupLaw.baseChangePointToBase (specMap R R') y))
  exact ⟨(LAW_transportIso c ε R' h h' e _).symm ≪≫
    (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.RelPicard.BaseChange.κ c R' t').inv).mapIso m' ≪≫
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    (LAW_transportIso c ε R' h h' e x ⊗ᵢ
      LAW_transportIso c ε R' h h' e y) ≪≫ m.symm⟩
end JacobianVarieties.Picard.Proofs.LawBC
end ProofImplementation
