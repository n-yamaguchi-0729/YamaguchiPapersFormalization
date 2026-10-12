/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_pullbackHom_eq_of_transport_of_hom_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Tactic.Choose
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_tensor_inverse

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup

/-!
# Transport of Picard pullback morphisms

Pullback morphisms commute with the classified transport of rigidified line bundles.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PullbackHomTransport

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard

universe u

noncomputable section

namespace Sub2c

section Monoidal

variable {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]

/-- Tensor inverses of isomorphic objects are isomorphic via the given inverse evaluations. -/
def inverseIso {X X' Q Q' : 𝒞} (eX : X ≅ X') (hQ : X ⊗ Q ≅ 𝟙_ 𝒞) (hQ' : X' ⊗ Q' ≅ 𝟙_ 𝒞) : Q ≅ Q' :=
  (ρ_ Q).symm ≪≫ whiskerLeftIso Q hQ'.symm ≪≫ (α_ Q X' Q').symm ≪≫
    whiskerRightIso ((β_ Q X') ≪≫ whiskerRightIso eX.symm Q ≪≫ hQ) Q' ≪≫ λ_ Q'

/-- Transport the given tensor-inverse evaluation along an isomorphism of its first factor. -/
def inverseOfIso {X Y Q : 𝒞} (eX : X ≅ Y) (hQ : X ⊗ Q ≅ 𝟙_ 𝒞) : Y ⊗ Q ≅ 𝟙_ 𝒞 :=
  whiskerRightIso eX.symm Q ≪≫ hQ

end Monoidal

section Modules

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

theorem rigSection_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    rigSection c t ε ≫ pullback.snd c t = 𝟙 T := by
  simp only [rigSection, pullback.lift_snd]

/-- Pulling a base module to the curve and then back along the section recovers that module. -/
def sectionPullbackIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (Q : T.Modules) :
    (Scheme.Modules.pullback (rigSection c t ε)).obj ((Scheme.Modules.pullback (pullback.snd c
      t)).obj Q) ≅ Q :=
  (Scheme.Modules.pullbackComp _ _).app Q ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_snd t ε)).app Q ≪≫
    (Scheme.Modules.pullbackId _).app Q

theorem baseChangeSnd_snd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) : baseChangeSnd c ψ ≫ pullback.snd c t = pullback.snd c t' ≫ ψ.1 := by
  simp only [baseChangeSnd, pullback.lift_snd]

/-- Pullback from the base commutes with a change of the parameter scheme. -/
def baseChangePullbackIso {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (Q : T.Modules) :
    (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj ((Scheme.Modules.pullback (pullback.snd c
      t)).obj Q) ≅
      (Scheme.Modules.pullback (pullback.snd c t')).obj ((Scheme.Modules.pullback ψ.1).obj Q) :=
  (Scheme.Modules.pullbackComp _ _).app Q ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_snd ψ)).app Q ≪≫
    ((Scheme.Modules.pullbackComp _ _).app Q).symm

end Modules

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

section Twist

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

/-- A chosen tensor inverse of the line bundle restricted to the second rigidifying section. -/
noncomputable def qinv {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) : T.Modules :=
  (M.isInvertible.pullback (rigSection c t ε₂)).exists_tensor_inverse.choose

theorem qinv_isInvertible {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    Scheme.Modules.IsInvertible (qinv ε₁ ε₂ M) :=
  (M.isInvertible.pullback (rigSection c t ε₂)).exists_tensor_inverse.choose_spec.1

/-- The chosen inverse evaluates the restriction at the second section to the unit module. -/
noncomputable def qinvIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    (Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L ⊗ qinv ε₁ ε₂ M ≅ 𝟙_ _ :=
  (M.isInvertible.pullback (rigSection c t ε₂)).exists_tensor_inverse.choose_spec.2.some

/-- Change the rigidifying section by tensoring with the inverse of its restriction. -/
noncomputable def twist {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    RigidifiedLineBundle c ε₂ t where
  L := M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (qinv ε₁ ε₂ M)
  isInvertible := M.isInvertible.tensor ((qinv_isInvertible ε₁ ε₂ M).pullback _)
  rigidified := ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    whiskerLeftIso _ (sectionPullbackIso t ε₂ _) ≪≫ qinvIso ε₁ ε₂ M⟩

theorem twist_L {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t)
    :
    (twist ε₁ ε₂ M).L = M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (qinv ε₁ ε₂ M) := rfl

/-- Identify the rigidification twist using any specified tensor-inverse evaluation. -/
def twistIsoOfInverse {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t)
    (Q : T.Modules) (hQ : (Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L ⊗ Q ≅ 𝟙_ _) :
    (twist ε₁ ε₂ M).L ≅ M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj Q :=
  whiskerLeftIso M.L ((Scheme.Modules.pullback _).mapIso (inverseIso (Iso.refl _) (qinvIso ε₁ ε₂ M)
    hQ))

theorem twist_congr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε₁ t)
    (e : Nonempty (M.L ≅ M'.L)) : Nonempty ((twist ε₁ ε₂ M).L ≅ (twist ε₁ ε₂ M').L) :=
  ⟨e.some ⊗ᵢ (Scheme.Modules.pullback _).mapIso
    (inverseIso ((Scheme.Modules.pullback _).mapIso e.some) (qinvIso ε₁ ε₂ M) (qinvIso ε₁ ε₂ M'))⟩

theorem twist_natural {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε₁ t) :
    Nonempty (((twist ε₁ ε₂ M).pullbackAlong ψ).L ≅ (twist ε₁ ε₂ (M.pullbackAlong ψ)).L) := by
  have hX : (Scheme.Modules.pullback (rigSection c t' ε₂)).obj (M.pullbackAlong ψ).L ≅
      (Scheme.Modules.pullback ψ.1).obj ((Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L) :=
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
      (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε₂ ψ)).app M.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M.L).symm
  have hQ : (Scheme.Modules.pullback ψ.1).obj ((Scheme.Modules.pullback (rigSection c t ε₂)).obj
    M.L) ⊗
      (Scheme.Modules.pullback ψ.1).obj (qinv ε₁ ε₂ M) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
      (Scheme.Modules.pullback ψ.1).mapIso (qinvIso ε₁ ε₂ M) ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso _
  have hq : (Scheme.Modules.pullback ψ.1).obj (qinv ε₁ ε₂ M) ≅ qinv ε₁ ε₂ (M.pullbackAlong ψ) :=
    inverseIso hX.symm hQ (qinvIso ε₁ ε₂ (M.pullbackAlong ψ))
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    whiskerLeftIso _ (baseChangePullbackIso ψ _ ≪≫ (Scheme.Modules.pullback _).mapIso hq)⟩

theorem twist_cut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε₁ t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (twist ε₁ ε₂ M) := by
  intro k _ _ s
  let φ := pullback.fst (pullback.snd c t) s
  have hφ : φ ≫ pullback.snd c t = fibreAt c t s ≫ s := pullback.condition
  obtain ⟨e0⟩ := nonempty_iso_unit_of_field _ ((qinv_isInvertible ε₁ ε₂ M).pullback s)
  have e1 : (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback (pullback.snd c t)).obj (qinv
    ε₁ ε₂ M)) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr hφ).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback (fibreAt c t s)).mapIso e0 ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _
  have e2 : (Scheme.Modules.pullback φ).obj (twist ε₁ ε₂ M).L ≅ (Scheme.Modules.pullback φ).obj M.L
    :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ whiskerLeftIso _ e1 ≪≫ ρ_ _
  exact (hM k s).of_iso e2.symm

end Twist

section Rep

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

theorem classify_congr {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {P : SubPicCondition c ε}
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t) (hM : P.P t M) (hM' : P.P t M') (i : Nonempty (M.L ≅ M'.L))
      :
    h.classify t M hM = h.classify t M' hM' :=
  h.classify_unique t M' hM' _ ⟨(h.classify_spec t M hM).some ≪≫ i.some⟩

end Rep

end Sub2c

namespace I2

section Transform

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of
    R))) c')
  (f : C' ⟶ C) (g : C ⟶ C') (hf : f ≫ c = c') (hg : g ≫ c' = c) (hgf : g ≫ f = 𝟙 C)

/-- Transport the section along the specified morphism of curves. -/
def epsT : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c' :=
  ⟨ε.1 ≫ g, by rw [Category.assoc, hg]; exact ε.2⟩

include hgf in
theorem epsT_comp : (epsT ε g hg).1 ≫ f = ε.1 := by
  change (ε.1 ≫ g) ≫ f = ε.1
  rw [Category.assoc, hgf, Category.comp_id]

/-- Pull back a rigidified line bundle and adjust its rigidifying section. -/
def Phi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c' ε' t :=
  Sub2c.twist (epsT ε g hg) ε' (M.pullbackCurve f hf (epsT_comp ε f g hg hgf))

theorem Phi_L {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    (Phi ε ε' f g hf hg hgf t M).L =
      (Scheme.Modules.pullback (curveChange f hf t)).obj M.L ⊗
        (Scheme.Modules.pullback (pullback.snd c' t)).obj
          (Sub2c.qinv (epsT ε g hg) ε' (M.pullbackCurve f hf (epsT_comp ε f g hg hgf))) := rfl

theorem Phi_congr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t)
    (i : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((Phi ε ε' f g hf hg hgf t M).L ≅ (Phi ε ε' f g hf hg hgf t M').L) :=
  Sub2c.twist_congr _ _ t _ _ (RigidifiedLineBundle.pullbackCurve_congr f hf (epsT_comp ε f g hg
    hgf) i)

theorem Phi_natural {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t) :
    Nonempty (((Phi ε ε' f g hf hg hgf t M).pullbackAlong ψ).L ≅
      (Phi ε ε' f g hf hg hgf t' (M.pullbackAlong ψ)).L) := by
  obtain ⟨i1⟩ := Sub2c.twist_natural (epsT ε g hg) ε' ψ (M.pullbackCurve f hf (epsT_comp ε f g hg
    hgf))
  obtain ⟨i2⟩ := Sub2c.twist_congr (epsT ε g hg) ε' t' _ _
    ⟨M.pullbackCurvePullbackAlongIso f hf (epsT_comp ε f g hg hgf) ψ⟩
  exact ⟨i1 ≪≫ i2⟩

theorem Phi_cut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Phi ε ε' f g hf hg hgf t M) :=
  Sub2c.twist_cut _ _ t _ (FibrewiseAlgEquivZero.pullbackCurve f hf (epsT_comp ε f g hg hgf) hM)

end Transform

end I2

end
end JacobianVarieties.Picard.Proofs.PullbackHomTransport

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

open _root_.JacobianVarieties.Picard.Proofs.PullbackHomTransport
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard
universe u

/-- Pullback morphisms commute with the classified transport of rigidified line bundles. -/
theorem schemeHomOverComp_pullbackHom_eq_of_transport_of_hom_comp_eq
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec
      (CommRingCat.of R))) c'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε'
      (algEquivZeroCut c' ε') D')
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    (W : C ≅ C) (hW : W.hom ≫ c = c) (hW' : W.inv ≫ c = c)
    (α : C' ≅ C') (hα' : α.inv ≫ c' = c')
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
    postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') θW =
      postComp θα (RepresentsRelSubPic.pullbackHom f hf hε h h') := by
  classical
  have hcomm' : α.inv ≫ f = f ≫ W.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hcomm, Category.assoc, W.hom_inv_id, Category.comp_id]
  let NW : RigidifiedLineBundle c ε D.toBase := I2.Phi ε ε W.inv W.hom hW' hW W.hom_inv_id D.toBase
    h.poincare
  have hNW : FibrewiseAlgEquivZero NW :=
    I2.Phi_cut ε ε W.inv W.hom hW' hW W.hom_inv_id D.toBase h.poincare h.poincare_mem
  let Q : D.P.Modules := Sub2c.qinv (I2.epsT ε W.hom hW) ε
    (h.poincare.pullbackCurve W.inv hW' (I2.epsT_comp ε W.inv W.hom hW W.hom_inv_id))
  have hQ : Scheme.Modules.IsInvertible Q := Sub2c.qinv_isInvertible _ _ _
  have hid : h.classify D.toBase h.poincare h.poincare_mem = ⟨𝟙 _, Category.id_comp _⟩ :=
    (h.classify_unique D.toBase _ _ _ ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_id c
      D.toBase)).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _⟩).symm
  have hθW' : θW = h.classify D.toBase NW hNW := by
    have key := hθW D.toBase h.poincare h.poincare_mem NW hNW Q hQ ⟨Iso.refl _⟩
    rw [hid] at key
    rw [← key]
    apply Subtype.ext
    exact (Category.id_comp _).symm
  have hL : postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') θW =
      h'.classify D.toBase (NW.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε
        hNW) := by
    rw [hθW']
    exact RepresentsRelSubPic.postComp_pullbackHom_classify f hf hε h h' D.toBase NW hNW
  have hcc : curveChange f hf D.toBase ≫ curveChange (c := c) (c' := c) W.inv hW' D.toBase =
      curveChange (c := c') (c' := c') α.inv hα' D.toBase ≫ curveChange f hf D.toBase := by
    apply pullback.hom_ext <;>
      simp only [curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        pullback.lift_snd,
        Category.comp_id, hcomm']
  have hR : postComp θα (RepresentsRelSubPic.pullbackHom f hf hε h h') =
      h'.classify D.toBase (NW.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε
        hNW) := by
    refine hθα D.toBase (h.poincare.pullbackCurve f hf hε)
      (FibrewiseAlgEquivZero.pullbackCurve f hf hε h.poincare_mem) _ _ Q hQ ⟨?_⟩
    exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hcc).app _ ≪≫
          ((Scheme.Modules.pullbackComp _ _).app _).symm) ⊗ᵢ
        ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr (curveChange_snd
          f hf D.toBase)).app _))
  exact hL.trans hR.symm
end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
