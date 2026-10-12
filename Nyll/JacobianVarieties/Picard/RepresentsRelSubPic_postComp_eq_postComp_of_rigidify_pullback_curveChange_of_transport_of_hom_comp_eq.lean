/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_eq_postComp_of_rigidify_pullback_curveChange_of_transport_of_hom_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback

/-! Transport of Picard morphisms through commuting curve isomorphisms. -/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PostCompositionTransport


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard


universe u

noncomputable section

namespace RTNAux

/-- An invertible module over the spectrum of a field is trivial. -/
theorem nonempty_iso_unit_of_field {k : Type u} [Field k] (Q : (Spec (CommRingCat.of k)).Modules)
    (hQ : Scheme.Modules.IsInvertible Q) : Nonempty (Q ≅ 𝟙_ (Spec (CommRingCat.of k)).Modules) := by
  obtain ⟨U, hx, ⟨eU⟩⟩ := hQ.1 default
  have hU : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [Subsingleton.elim y default]
    exact hx
  subst hU
  let X := Spec (CommRingCat.of k)
  let i : (⊤ : X.Opens).toScheme ≅ X := X.topIso
  have hi : i.inv ≫ (⊤ : X.Opens).ι = 𝟙 X := by
    rw [← Scheme.topIso_hom]; exact i.inv_hom_id
  exact ⟨((Scheme.Modules.pullbackId _).app Q).symm ≪≫
    (Scheme.Modules.pullbackCongr hi.symm).app Q ≪≫
    ((Scheme.Modules.pullbackComp _ _).app Q).symm ≪≫
    (Scheme.Modules.pullback i.inv).mapIso eU ≪≫
    Scheme.Modules.pullbackUnitIso i.inv⟩

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}

/-- Geometric fibres of the module are algebraically equivalent to zero. -/
def CutL (c : C ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : (pullback c t).Modules) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
    IsAlgEquivZero (fibreAt c t s) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t)
      s)).obj L)

/-- Forget the rigidification in fibrewise algebraic equivalence to zero. -/
theorem cutL_of_mem {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M) : CutL c t M.L := hM

/-- Fibrewise algebraic equivalence to zero is preserved by curve pullback. -/
theorem cutL_curveChange (f : C' ⟶ C) (hf : f ≫ c = c') {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    {L : (pullback c t).Modules} (hL : CutL c t L) :
    CutL c' t ((Scheme.Modules.pullback (curveChange f hf t)).obj L) := by
  intro k _ _ s
  let e : Limits.pullback (pullback.snd c' t) s ⟶ Limits.pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ (curveChange f hf t) (𝟙 _) (𝟙 T)
      (by rw [Category.comp_id, curveChange_snd]) (by rw [Category.id_comp, Category.comp_id])
  have he : e ≫ fibreAt c t s = fibreAt c' t s := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c' t) s ≫ curveChange f hf t := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hL k s).pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L).symm

/-- Rigidification preserves fibrewise algebraic equivalence to zero. -/
theorem ofInvertible_cut {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'} {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) {L : (pullback c' t).Modules} (hL :
      Scheme.Modules.IsInvertible L)
    (hcut : CutL c' t L) : FibrewiseAlgEquivZero (RigidifiedLineBundle.ofInvertible (ε := ε') L hL)
      := by
  intro k _ _ s
  let φ := pullback.fst (pullback.snd c' t) s
  have hφ : φ ≫ pullback.snd c' t = fibreAt c' t s ≫ s := pullback.condition
  obtain ⟨e0⟩ := nonempty_iso_unit_of_field _
    ((Scheme.Modules.IsInvertible.dual (hL.pullback (rigSection c' t ε'))).1.pullback s)
  have e1 : (Scheme.Modules.pullback φ).obj
      ((Scheme.Modules.pullback (pullback.snd c' t)).obj (rigCorrection ε' t L)) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr hφ).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback (fibreAt c' t s)).mapIso e0 ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _
  have e2 : (Scheme.Modules.pullback φ).obj (RigidifiedLineBundle.ofInvertible (ε := ε') L hL).L ≅
      (Scheme.Modules.pullback φ).obj L :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ whiskerLeftIso _ e1 ≪≫ ρ_ _
  exact (hcut k s).of_iso e2.symm

/-- Isomorphic underlying line bundles have the same classifying point. -/
theorem classify_congr {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {P : SubPicCondition c ε}
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t) (hM : P.P t M) (hM' : P.P t M') (i : Nonempty (M.L ≅ M'.L))
      :
    h.classify t M hM = h.classify t M' hM' :=
  h.classify_unique t M' hM' _ ⟨(h.classify_spec t M hM).some ≪≫ i.some⟩

end RTNAux

end

end JacobianVarieties.Picard.Proofs.PostCompositionTransport

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

universe u

open JacobianVarieties.Picard.Proofs.PostCompositionTransport.RTNAux in
/-- Transport of Picard morphisms through commuting curve isomorphisms. -/
theorem postComp_eq_postComp_of_rigidify_pullback_curveChange_of_transport_of_hom_comp_eq
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec
      (CommRingCat.of R))) c'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε'
      (algEquivZeroCut c' ε') D')
    (f : C' ⟶ C) (hf : f ≫ c = c')
    (ν : SchemeHomOver D.toBase D'.toBase)
    (hν : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν)).L ≅
          Scheme.Modules.rigidify (rigSection c' t ε') (pullback.snd c' t)
            ((Scheme.Modules.pullback (curveChange f hf t)).obj (h.poincare.pullbackAlong a).L)))
    (W : C ≅ C) (hW' : W.inv ≫ c = c)
    (α : C' ≅ C') (hα : α.hom ≫ c' = c') (hα' : α.inv ≫ c' = c')
    (hcomm : α.hom ≫ f = f ≫ W.hom)
    (θW : SchemeHomOver D.toBase D.toBase)
    (hθW : (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c ε t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c) W.inv hW' t)).obj
          M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c t)).obj Q) →
        postComp θW (h.classify t M hM) = h.classify t N hN))
    (θα : SchemeHomOver D'.toBase D'.toBase)
    (hθα : (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c' ε' t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c' ε' t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c') (c' := c') α.inv hα'
          t)).obj M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c' t)).obj Q) →
        postComp θα (h'.classify t M hM) = h'.classify t N hN)) :
    postComp ν θW = postComp θα ν := by
  classical
  have hcomm' : α.inv ≫ f = f ≫ W.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hcomm, Category.assoc, W.hom_inv_id, Category.comp_id]
  have hνcl : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
      (hM : FibrewiseAlgEquivZero M),
      postComp ν (h.classify t M hM) =
        h'.classify t (RigidifiedLineBundle.ofInvertible (ε := ε')
          ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L) (M.isInvertible.pullback _))
          (ofInvertible_cut t _ (cutL_curveChange f hf t (cutL_of_mem M hM))) := by
    intro T t M hM
    refine h'.classify_unique t _ _ _ ⟨?_⟩
    exact (hν t (h.classify t M hM)).some ≪≫
      Scheme.Modules.rigidifyMapIso _ _ ((Scheme.Modules.pullback (curveChange f hf t)).mapIso
        (h.classify_spec t M hM).some)
  let LW : (pullback c D.toBase).Modules :=
    (Scheme.Modules.pullback (curveChange (c := c) (c' := c) W.inv hW' D.toBase)).obj h.poincare.L
  have hLW : Scheme.Modules.IsInvertible LW := h.poincare.isInvertible.pullback _
  have hLWcut : CutL c D.toBase LW := cutL_curveChange W.inv hW' _ (cutL_of_mem h.poincare
    h.poincare_mem)
  let NW : RigidifiedLineBundle c ε D.toBase := RigidifiedLineBundle.ofInvertible (ε := ε) LW hLW
  have hNW : FibrewiseAlgEquivZero NW := ofInvertible_cut _ hLW hLWcut
  have hQW : Scheme.Modules.IsInvertible (rigCorrection ε D.toBase LW) :=
    (Scheme.Modules.IsInvertible.dual (hLW.pullback _)).1
  have hid : h.classify D.toBase h.poincare h.poincare_mem = ⟨𝟙 _, Category.id_comp _⟩ :=
    (h.classify_unique D.toBase _ _ _ ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_id c
      D.toBase)).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _⟩).symm
  have hθW' : θW = h.classify D.toBase NW hNW := by
    have key := hθW D.toBase h.poincare h.poincare_mem NW hNW (rigCorrection ε D.toBase LW) hQW
      ⟨Iso.refl _⟩
    rw [hid] at key
    rw [← key]
    apply Subtype.ext
    exact (Category.id_comp _).symm
  have hL := hνcl D.toBase NW hNW
  rw [← hθW'] at hL
  let Lf : (pullback c' D.toBase).Modules := (Scheme.Modules.pullback (curveChange f hf
    D.toBase)).obj h.poincare.L
  have hLf : Scheme.Modules.IsInvertible Lf := h.poincare.isInvertible.pullback _
  have hLfcut : CutL c' D.toBase Lf := cutL_curveChange f hf _ (cutL_of_mem h.poincare
    h.poincare_mem)
  have hν₀ : ν = h'.classify D.toBase (RigidifiedLineBundle.ofInvertible (ε := ε') Lf hLf)
      (ofInvertible_cut _ hLf hLfcut) := by
    have key := hνcl D.toBase h.poincare h.poincare_mem
    rw [hid] at key
    rw [← key]
    apply Subtype.ext
    exact (Category.id_comp _).symm
  let Lα : (pullback c' D.toBase).Modules :=
    (Scheme.Modules.pullback (curveChange (c := c') (c' := c') α.inv hα' D.toBase)).obj
      (RigidifiedLineBundle.ofInvertible (ε := ε') Lf hLf).L
  have hLα : Scheme.Modules.IsInvertible Lα := (RigidifiedLineBundle.ofInvertible (ε := ε') Lf
    hLf).isInvertible.pullback _
  have hLαcut : CutL c' D.toBase Lα :=
    cutL_curveChange α.inv hα' _ (cutL_of_mem _ (ofInvertible_cut _ hLf hLfcut))
  have hR : postComp θα ν = h'.classify D.toBase (RigidifiedLineBundle.ofInvertible (ε := ε') Lα
    hLα)
      (ofInvertible_cut _ hLα hLαcut) := by
    rw [hν₀]
    exact hθα D.toBase _ (ofInvertible_cut _ hLf hLfcut) _ (ofInvertible_cut _ hLα hLαcut)
      (rigCorrection ε' D.toBase Lα) (Scheme.Modules.IsInvertible.dual (hLα.pullback _)).1
        ⟨Iso.refl _⟩
  rw [hL, hR]
  apply classify_congr
  have hcc : curveChange f hf D.toBase ≫ curveChange (c := c) (c' := c) W.inv hW' D.toBase =
      curveChange (c := c') (c' := c') α.inv hα' D.toBase ≫ curveChange f hf D.toBase := by
    apply pullback.hom_ext <;>
      simp only [curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        pullback.lift_snd,
        Category.comp_id, hcomm']
  let L₀ : (pullback c' D.toBase).Modules :=
    (Scheme.Modules.pullback (curveChange (c := c') (c' := c') α.inv hα' D.toBase)).obj Lf
  have hL₀ : Scheme.Modules.IsInvertible L₀ := hLf.pullback _
  have hP2 : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (curveChange f hf D.toBase)).obj LW) := hLW.pullback _
  let eQ : (Scheme.Modules.pullback (curveChange f hf D.toBase)).obj
        ((Scheme.Modules.pullback (pullback.snd c D.toBase)).obj (rigCorrection ε D.toBase LW)) ≅
      (Scheme.Modules.pullback (pullback.snd c' D.toBase)).obj (rigCorrection ε D.toBase LW) :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr (curveChange_snd f hf
      D.toBase)).app _
  obtain ⟨iA⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε')
    (NW.isInvertible.pullback _)
    ((hQW.pullback _).tensor hP2)
    (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ β_ _ _ ≪≫ (eQ ⊗ᵢ Iso.refl _))
  obtain ⟨iB⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackSnd_tensor_iso (ε := ε') (t :=
    D.toBase) hQW hP2
  obtain ⟨iC⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε') hP2 hL₀
    ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hcc).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm)
  let ε'' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c' := ⟨ε'.1 ≫ α.hom,
    by rw [Category.assoc, hα]; exact ε'.2⟩
  have hε'' : ε''.1 ≫ α.inv = ε'.1 := by
    change (ε'.1 ≫ α.hom) ≫ α.inv = ε'.1
    rw [Category.assoc, α.hom_inv_id, Category.comp_id]
  have hσ'' : rigSection c' D.toBase ε'' ≫ curveChange (c := c') (c' := c') α.inv hα' D.toBase =
      𝟙 _ ≫ rigSection c' D.toBase ε' :=
    (rigSection_curveChange α.inv hα' hε'' D.toBase).trans (Category.id_comp _).symm
  have hq'' : curveChange (c := c') (c' := c') α.inv hα' D.toBase ≫ pullback.snd c' D.toBase =
      pullback.snd c' D.toBase ≫ 𝟙 _ :=
    (curveChange_snd _ _ _).trans (Category.comp_id _).symm
  obtain ⟨iD⟩ := Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso (𝟙 _)
    (curveChange (c := c') (c' := c') α.inv hα' D.toBase) hσ'' hq'' hLf
  have hD'' : Scheme.Modules.IsInvertible
      (Scheme.Modules.dual ((Scheme.Modules.pullback (rigSection c' D.toBase ε'')).obj L₀)) :=
    (Scheme.Modules.IsInvertible.dual (hL₀.pullback _)).1
  obtain ⟨iE⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε') hLα
    ((hD''.pullback _).tensor hL₀)
    (iD ≪≫ β_ _ _)
  obtain ⟨iF⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackSnd_tensor_iso (ε := ε') (t :=
    D.toBase) hD'' hL₀
  exact ⟨iA ≪≫ iB ≪≫ iC ≪≫ iF.symm ≪≫ iE.symm⟩
end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
end ProofImplementation
