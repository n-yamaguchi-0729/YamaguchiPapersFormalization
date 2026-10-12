/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_pullback_map_of_comp_eq_comp.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup

/-!
# Classifying a semilinear pullback of the Poincare bundle

A map of the curve over a split change of base induces a classifying map.
The rigidified pullback construction preserves multiplication and the identity.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PullbackMapExistence


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


universe u

noncomputable section

namespace P2mSemilin

theorem nonempty_pullback_fst_ofInvertible_iso {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (L : (pullback c t).Modules)
    (hL : Scheme.Modules.IsInvertible L) {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj
      (RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj L) := by
  rw [RigidifiedLineBundle.ofInvertible_L_eq_tensor]
  have hD : Scheme.Modules.IsInvertible (rigCorrection ε t L) := ((hL.pullback _).dual).1
  obtain ⟨u⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ (hD.pullback s)
  refine ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ ?_) ≪≫ ρ_ _⟩
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (pullback.condition (f := pullback.snd c t) (g := s))).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso u ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _

section Transform

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  (β β' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R)) (hβ : β' ≫ β = 𝟙 (Spec (CommRingCat.of
    R)))
  (f : C ⟶ C) (hf : f ≫ c = c ≫ β)

/-- The base-change map induced by the curve map and the chosen splitting of the base map. -/
def fT {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : pullback c (t ≫ β') ⟶ pullback c t :=
  pullback.map c (t ≫ β') c t f (𝟙 T) β hf.symm
    (by rw [Category.assoc, hβ, Category.comp_id, Category.id_comp])

theorem fT_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    fT β β' hβ f hf t ≫ pullback.snd c t = pullback.snd c (t ≫ β') := by
  simp only [fT, pullback.lift_snd, Category.comp_id]

/-- A morphism over the base, viewed over its composition with the chosen base splitting. -/
def shift {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) : SchemeHomOver (t' ≫ β') (t ≫ β') :=
  ⟨ψ.1, by rw [← Category.assoc, ψ.2]⟩

theorem fT_baseChangeSnd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    fT β β' hβ f hf t' ≫ baseChangeSnd c ψ = baseChangeSnd c (shift β' ψ) ≫ fT β β' hβ f hf t := by
  apply pullback.hom_ext <;>
    simp only [fT, shift, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

theorem hinv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (fT β β' hβ f hf t)).obj M.L) :=
  M.isInvertible.pullback _

/-- Pull back an invertible bundle along the semilinear map and rigidify it. -/
def Psi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c ε (t ≫ β') :=
  RigidifiedLineBundle.ofInvertible (ε := ε)
    ((Scheme.Modules.pullback (fT β β' hβ f hf t)).obj M.L) (hinv β β' hβ f hf t M)

theorem hcut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Psi (ε := ε) β β' hβ f hf t M) := by
  intro k _ _ s
  let e : Limits.pullback (pullback.snd c (t ≫ β')) s ⟶ Limits.pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ (fT β β' hβ f hf t) (𝟙 _) (𝟙 T)
      (by rw [Category.comp_id, fT_snd])
      (by rw [Category.comp_id, Category.id_comp])
  have he : e ≫ fibreAt c t s = fibreAt c (t ≫ β') s := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c (t ≫ β')) s ≫ fT β β' hβ f hf t := by
    simp only [e, pullback.lift_fst]
  have h1 : IsAlgEquivZero (fibreAt c (t ≫ β') s)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c (t ≫ β')) s)).obj
        ((Scheme.Modules.pullback (fT β β' hβ f hf t)).obj M.L)) := by
    refine IsAlgEquivZero.of_iso ?_ ((hM k s).pullback e he)
    exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
      (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M.L).symm
  obtain ⟨e2⟩ := nonempty_pullback_fst_ofInvertible_iso (ε := ε) _ (hinv β β' hβ f hf t M) s
  exact h1.of_iso e2.symm

end Transform

section Law

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {D : RelativePic0Designation R c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

theorem nonempty_poincare_pullbackAlong_law_mul_iso {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver s D.toBase) :
    Nonempty ((h.poincare.pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y)).L ≅
      ((h.poincare.pullbackAlong x).tensor (h.poincare.pullbackAlong y)).L) := by
  exact RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut c ε)
    h
    (T := Over.mk s) (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)

theorem nonempty_poincare_pullbackAlong_law_one_iso {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((h.poincare.pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one s)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) s).L) := by
  let := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut c ε) h
  have h1 := RepresentsRelSubPic.homEquiv_one (P := algEquivZeroGroupCut c ε) h (Over.mk s)
  have h2 := congrArg (fun z => z.1) h1
  exact Quotient.exact h2

end Law

section Clauses

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {D : RelativePic0Designation R c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
  (β β' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R)) (hβ : β' ≫ β = 𝟙 (Spec (CommRingCat.of
    R)))
  (f : C ⟶ C) (hf : f ≫ c = c ≫ β)
  (N : SchemeHomOver (D.toBase ≫ β') D.toBase)
  (hN : Nonempty ((h.poincare.pullbackAlong N).L ≅ (Psi (ε := ε) β β' hβ f hf D.toBase
    h.poincare).L))

/-- Compose a point of the representing scheme with the classifying map over the changed base. -/
def tw {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (z : SchemeHomOver t D.toBase) :
    SchemeHomOver (t ≫ β') D.toBase :=
  ⟨z.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, z.2]⟩

include hN in
theorem keyA {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (tw β' N a)).L ≅ (Psi (ε := ε) β β' hβ f hf t
      (h.poincare.pullbackAlong a)).L) := by
  let a' : SchemeHomOver (t ≫ β') (D.toBase ≫ β') := shift β' a
  have e0 : tw β' N a = postComp N a' := rfl
  rw [e0]
  let e1 := (h.poincare.pullbackAlongPullbackAlongIso' N a').symm
  obtain ⟨e2⟩ := RigidifiedLineBundle.pullbackAlong_congr a' hN
  obtain ⟨e3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) a'
    (hinv β β' hβ f hf D.toBase h.poincare)
  have e4 : (Scheme.Modules.pullback (baseChangeSnd c a')).obj
      ((Scheme.Modules.pullback (fT β β' hβ f hf D.toBase)).obj h.poincare.L) ≅
      (Scheme.Modules.pullback (fT β β' hβ f hf t)).obj ((Scheme.Modules.pullback (baseChangeSnd c
        a)).obj h.poincare.L) :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (fT_baseChangeSnd β β' hβ f hf a).symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm
  obtain ⟨e5⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    ((hinv β β' hβ f hf D.toBase h.poincare).pullback (baseChangeSnd c a'))
    (hinv β β' hβ f hf t (h.poincare.pullbackAlong a)) e4
  exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ e5⟩

include hN in
theorem keyB {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase) :
    tw β' N ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t x y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (t ≫ β') (tw β'
        N x) (tw β' N y) := by
  apply h.ext_of_iso (t ≫ β')
  obtain ⟨e1⟩ := keyA h β β' hβ f hf N hN t ((RepresentsRelSubPic.relativeGroupLaw (P :=
    algEquivZeroGroupCut c ε) h).mul t x y)
  obtain ⟨em⟩ := nonempty_poincare_pullbackAlong_law_mul_iso h t x y
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinv β β' hβ f hf t _) (hinv β β' hβ f hf t ((h.poincare.pullbackAlong x).tensor
      (h.poincare.pullbackAlong y)))
    ((Scheme.Modules.pullback (fT β β' hβ f hf t)).mapIso em)
  obtain ⟨e3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinv β β' hβ f hf t ((h.poincare.pullbackAlong x).tensor (h.poincare.pullbackAlong y)))
    ((hinv β β' hβ f hf t (h.poincare.pullbackAlong x)).tensor (hinv β β' hβ f hf t
      (h.poincare.pullbackAlong y)))
    (Scheme.Modules.pullbackTensorObjIso _ _ _)
  obtain ⟨e4⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε)
    (hinv β β' hβ f hf t (h.poincare.pullbackAlong x)) (hinv β β' hβ f hf t
      (h.poincare.pullbackAlong y))
  obtain ⟨ex⟩ := keyA h β β' hβ f hf N hN t x
  obtain ⟨ey⟩ := keyA h β β' hβ f hf N hN t y
  obtain ⟨em'⟩ := nonempty_poincare_pullbackAlong_law_mul_iso h (t ≫ β') (tw β' N x) (tw β' N y)
  exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ e4 ≪≫ (ex.symm ⊗ᵢ ey.symm) ≪≫ em'.symm⟩

include hN in
theorem keyC {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    tw β' N ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one t) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (t ≫ β') := by
  apply h.ext_of_iso (t ≫ β')
  obtain ⟨e1⟩ := keyA h β β' hβ f hf N hN t ((RepresentsRelSubPic.relativeGroupLaw (P :=
    algEquivZeroGroupCut c ε) h).one t)
  obtain ⟨eo⟩ := nonempty_poincare_pullbackAlong_law_one_iso h t
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinv β β' hβ f hf t _) (RigidifiedLineBundle.unit (c := c) (ε := ε) (t ≫ β')).isInvertible
    ((Scheme.Modules.pullback (fT β β' hβ f hf t)).mapIso eo ≪≫ Scheme.Modules.pullbackUnitIso _)
  obtain ⟨e3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (RigidifiedLineBundle.unit (c := c) (ε := ε) (t ≫ β'))
  obtain ⟨eo'⟩ := nonempty_poincare_pullbackAlong_law_one_iso h (t ≫ β')
  exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ eo'.symm⟩

end Clauses

end P2mSemilin

end

end JacobianVarieties.Picard.Proofs.PullbackMapExistence

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.PullbackMapExistence

universe u

open P2mSemilin in
theorem exists_hom_classifies_rigidify_pullback_map_of_comp_eq_comp
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (β β' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
    (hβ : β' ≫ β = 𝟙 (Spec (CommRingCat.of R)))
    (f : C ⟶ C) (hf : f ≫ c = c ≫ β) :
    ∃ N : SchemeHomOver (D.toBase ≫ β') D.toBase,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        Nonempty ((h.poincare.pullbackAlong
            (⟨a.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, a.2]⟩ :
              SchemeHomOver (t ≫ β') D.toBase)).L ≅
          Scheme.Modules.rigidify (rigSection c (t ≫ β') ε) (pullback.snd c (t ≫ β'))
            ((Scheme.Modules.pullback
                (pullback.map c (t ≫ β') c t f (𝟙 T) β hf.symm
                  (by rw [Category.assoc, hβ, Category.comp_id, Category.id_comp]))).obj
              (h.poincare.pullbackAlong a).L))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase),
        (⟨((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t x y).1 ≫
          N.1,
            by
              rw [Category.assoc, N.2, ← Category.assoc,
                ((RepresentsRelSubPic.relativeGroupLaw
                  (P := algEquivZeroGroupCut c ε) h).mul t x y).2]⟩ :
            SchemeHomOver (t ≫ β') D.toBase) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (t ≫ β')
            ⟨x.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, y.2]⟩) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one t).1 ≫ N.1 =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (t ≫
            β')).1) := by
  let N : SchemeHomOver (D.toBase ≫ β') D.toBase :=
    h.classify (D.toBase ≫ β') (Psi (ε := ε) β β' hβ f hf D.toBase h.poincare)
      (hcut (ε := ε) β β' hβ f hf D.toBase h.poincare h.poincare_mem)
  have hN : Nonempty ((h.poincare.pullbackAlong N).L ≅ (Psi (ε := ε) β β' hβ f hf D.toBase
    h.poincare).L) :=
    h.classify_spec _ _ _
  refine ⟨N, fun t a => ?_, fun t x y => ?_, fun t => ?_⟩
  · exact keyA h β β' hβ f hf N hN t a
  · exact keyB h β β' hβ f hf N hN t x y
  · exact congrArg Subtype.val (keyC h β β' hβ f hf N hN t)
end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
end ProofImplementation
