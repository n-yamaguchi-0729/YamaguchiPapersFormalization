/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange
/-!
Restriction maps on Picard points commute with a compatible base change.
The proof compares the pulled-back Poincare bundles using explicit pullback isomorphisms.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.RestrictedBaseChange

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.GoodReductionJacobian
open _root_.CategoryTheory.MonoidalCategory

noncomputable section

namespace TwistNatAux

variable {R : Type u} [CommRing R] {κ : Type u} [CommRing κ] [Algebra R κ]

local notation "𝔰" => specMap R κ

section Basic

/-- The first projection of the rigidifying section. -/
@[reassoc] theorem rigSection_fst'' {C T : Scheme.{u}} (cc : C ⟶ Spec (CommRingCat.of κ))
    (t : T ⟶ Spec (CommRingCat.of κ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) cc) : rigSection cc t e ≫ pullback.fst cc t =
      t ≫ e.1 :=
  pullback.lift_fst _ _ _

/-- The second projection of the rigidifying section. -/
@[reassoc] theorem rigSection_snd'' {C T : Scheme.{u}} (cc : C ⟶ Spec (CommRingCat.of κ))
    (t : T ⟶ Spec (CommRingCat.of κ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) cc) : rigSection cc t e ≫ pullback.snd cc t =
      𝟙 T :=
  pullback.lift_snd _ _ _

/-- Changing the base leaves the first pullback projection unchanged. -/
@[reassoc] theorem baseChangeSnd_fst'' {S : Type u} [CommRing S] {C T T' : Scheme.{u}}
    (cc : C ⟶ Spec (CommRingCat.of S))
    {t : T ⟶ Spec (CommRingCat.of S)} {t' : T' ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver t' t) : baseChangeSnd cc ψ ≫ pullback.fst cc t = pullback.fst cc t' :=
  BaseChange.baseChangeSnd_fst' _ cc ψ

/-- The second projection after a change of base. -/
@[reassoc] theorem baseChangeSnd_snd'' {S : Type u} [CommRing S] {C T T' : Scheme.{u}}
    (cc : C ⟶ Spec (CommRingCat.of S))
    {t : T ⟶ Spec (CommRingCat.of S)} {t' : T' ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver t' t) : baseChangeSnd cc ψ ≫ pullback.snd cc t = pullback.snd cc t' ≫ ψ.1 :=
  BaseChange.baseChangeSnd_snd' _ cc ψ

/-- The first projection of the base-changed section. -/
@[reassoc] theorem sectionBaseChange_fst'' {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    (sectionBaseChange κ e).1 ≫ pullback.fst c 𝔰 = 𝔰 ≫ e.1 :=
  sectionBaseChange_coe_fst κ e

/-- The second projection of the base-changed section. -/
@[reassoc] theorem sectionBaseChange_snd'' {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    (sectionBaseChange κ e).1 ≫ pullback.snd c 𝔰 = 𝟙 _ :=
  sectionBaseChange_coe_snd κ e

/-- The first projection after changing the curve. -/
@[reassoc] theorem curveChange_fst'' {S : Type u} [CommRing S] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of S)}
    {c' : C' ⟶ Spec (CommRingCat.of S)} (f : C' ⟶ C) (hf : f ≫ c = c')
    (t : T ⟶ Spec (CommRingCat.of S)) : curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫
      f := by
  unfold curveChange; rw [pullback.lift_fst]

/-- Changing the curve preserves the second projection. -/
@[reassoc] theorem curveChange_snd'' {S : Type u} [CommRing S] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of S)}
    {c' : C' ⟶ Spec (CommRingCat.of S)} (f : C' ⟶ C) (hf : f ≫ c = c')
    (t : T ⟶ Spec (CommRingCat.of S)) : curveChange f hf t ≫ pullback.snd c t = pullback.snd c' t :=
  curveChange_snd f hf t

end Basic

section Points

variable {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) (τ : SchemeHomOver (specMap R κ)
  (specMap R κ))

/-- Replace the base coordinate of a point while keeping its curve coordinate. -/
def flatPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : T ⟶ pullback y 𝔰)
    (hb : b ≫ pullback.snd y 𝔰 = t ≫ τ.1) : SchemeHomOver t (pullback.snd y 𝔰) :=
  ⟨pullback.lift (b ≫ pullback.fst y 𝔰) t (by
      rw [Category.assoc, pullback.condition, reassoc_of% hb, τ.2]),
    pullback.lift_snd _ _ _⟩

/-- The flattened point has the original first coordinate. -/
@[reassoc] theorem flatPt_coe_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ))
    (b : T ⟶ pullback y 𝔰)
    (hb : b ≫ pullback.snd y 𝔰 = t ≫ τ.1) : (flatPt y τ t b hb).1 ≫ pullback.fst y 𝔰 = b ≫
      pullback.fst y 𝔰 :=
  pullback.lift_fst _ _ _

/-- The flattened point lies over the specified base map. -/
@[reassoc] theorem flatPt_coe_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ))
    (b : T ⟶ pullback y 𝔰)
    (hb : b ≫ pullback.snd y 𝔰 = t ≫ τ.1) : (flatPt y τ t b hb).1 ≫ pullback.snd y 𝔰 = t :=
  pullback.lift_snd _ _ _

/-- Changing the base of the flattened point recovers the original map. -/
theorem flatPt_comp_baseChangeSnd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ))
    (b : T ⟶ pullback y 𝔰)
    (hb : b ≫ pullback.snd y 𝔰 = t ≫ τ.1) : (flatPt y τ t b hb).1 ≫ baseChangeSnd y τ = b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeSnd_fst'', flatPt_coe_fst]
  · simp only [Category.assoc, baseChangeSnd_snd'', flatPt_coe_snd_assoc, hb]

/-- Change the base coordinate of a point by the specified endomorphism. -/
def twistPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)}
    (a : SchemeHomOver t (pullback.snd y 𝔰)) :
    SchemeHomOver (t ≫ τ.1) (pullback.snd y 𝔰) :=
  ⟨a.1 ≫ baseChangeSnd y τ, by rw [Category.assoc, baseChangeSnd_snd'', reassoc_of% a.2]⟩

/-- The underlying map of a twisted point. -/
@[scoped simp] theorem twistPt_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)}
    (a : SchemeHomOver t (pullback.snd y 𝔰)) :
    (twistPt y τ a).1 = a.1 ≫ baseChangeSnd y τ := rfl

/-- Twisting preserves the first coordinate. -/
@[reassoc] theorem twistPt_coe_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)}
    (a : SchemeHomOver t (pullback.snd y 𝔰)) :
    (twistPt y τ a).1 ≫ pullback.fst y 𝔰 = a.1 ≫ pullback.fst y 𝔰 := by
  rw [twistPt_coe, Category.assoc, baseChangeSnd_fst'']

end Points

section Pi

variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (τ : SchemeHomOver (specMap R κ)
  (specMap R κ))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ))

/-- Compare the two iterated pullbacks after twisting the base coordinate. -/
def piHom : pullback (baseChange R c κ) (t ≫ τ.1) ⟶ pullback (baseChange R c κ) t :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst c 𝔰) (pullback.snd _ _ ≫ t) (by
      simp only [Category.assoc, pullback.condition, pullback.condition_assoc, τ.2]))
    (pullback.snd _ _) (by rw [pullback.lift_snd])

/-- The inverse comparison between the iterated pullbacks. -/
def piInv : pullback (baseChange R c κ) t ⟶ pullback (baseChange R c κ) (t ≫ τ.1) :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst c 𝔰) (pullback.snd _ _ ≫ t ≫ τ.1) (by
      simp only [Category.assoc, pullback.condition, pullback.condition_assoc, τ.2]))
    (pullback.snd _ _) (by rw [pullback.lift_snd])

/-- The comparison preserves the outer second projection. -/
@[reassoc (attr := simp)] theorem piHom_snd : piHom c τ t ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _
/-- The inverse comparison preserves the outer second projection. -/
@[reassoc (attr := simp)] theorem piInv_snd : piInv c τ t ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _
/-- The comparison preserves the inner first projection. -/
@[reassoc (attr := simp)] theorem piHom_fst_fst :
    piHom c τ t ≫ pullback.fst _ _ ≫ pullback.fst c 𝔰 = pullback.fst _ _ ≫ pullback.fst c 𝔰 := by
  rw [piHom, pullback.lift_fst_assoc, pullback.lift_fst]
/-- The inverse comparison preserves the inner first projection. -/
@[reassoc (attr := simp)] theorem piInv_fst_fst :
    piInv c τ t ≫ pullback.fst _ _ ≫ pullback.fst c 𝔰 = pullback.fst _ _ ≫ pullback.fst c 𝔰 := by
  rw [piInv, pullback.lift_fst_assoc, pullback.lift_fst]
/-- The inner base coordinate after the comparison. -/
@[reassoc (attr := simp)] theorem piHom_fst_snd :
    piHom c τ t ≫ pullback.fst _ _ ≫ pullback.snd c 𝔰 = pullback.snd _ _ ≫ t := by
  rw [piHom, pullback.lift_fst_assoc, pullback.lift_snd]
/-- The inner base coordinate after the inverse comparison. -/
@[reassoc (attr := simp)] theorem piInv_fst_snd :
    piInv c τ t ≫ pullback.fst _ _ ≫ pullback.snd c 𝔰 = pullback.snd _ _ ≫ t ≫ τ.1 := by
  rw [piInv, pullback.lift_fst_assoc, pullback.lift_snd]

/-- The isomorphism between the two iterated pullbacks. -/
def piIso : pullback (baseChange R c κ) (t ≫ τ.1) ≅ pullback (baseChange R c κ) t where
  hom := piHom c τ t
  inv := piInv c τ t
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, piInv_fst_fst, piHom_fst_fst]
      · simp only [Category.assoc, Category.id_comp, piInv_fst_snd, piHom_snd_assoc]
        exact pullback.condition.symm
    · simp only [Category.assoc, piInv_snd, piHom_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, piHom_fst_fst, piInv_fst_fst]
      · simp only [Category.assoc, Category.id_comp, piHom_fst_snd, piInv_snd_assoc]
        exact pullback.condition.symm
    · simp only [Category.assoc, piHom_snd, piInv_snd, Category.id_comp]

/-- The forward map of the iterated pullback isomorphism. -/
@[scoped simp] theorem piIso_hom : (piIso c τ t).hom = piHom c τ t := rfl
/-- The inverse map of the iterated pullback isomorphism. -/
@[scoped simp] theorem piIso_inv : (piIso c τ t).inv = piInv c τ t := rfl

/-- The iterated pullback comparison respects the rigidifying section. -/
theorem rigSection_piHom (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    rigSection (baseChange R c κ) (t ≫ τ.1) (sectionBaseChange κ e) ≫ piHom c τ t =
      rigSection (baseChange R c κ) t (sectionBaseChange κ e) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, piHom_fst_fst, rigSection_fst''_assoc, sectionBaseChange_fst'',
        reassoc_of% τ.2]
    · simp only [Category.assoc, piHom_fst_snd, rigSection_snd''_assoc, rigSection_fst''_assoc,
        sectionBaseChange_snd'', Category.comp_id]
  · simp only [Category.assoc, piHom_snd, rigSection_snd'']

end Pi

section Transport

/-- Compare an iterated module pullback with pullback along the composite. -/
def objIso {P Q S : Scheme.{u}} (A : P ⟶ Q) (B : Q ⟶ S) (C : P ⟶ S) (h : A ≫ B = C) (L : S.Modules)
    :
    (Scheme.Modules.pullback A).obj ((Scheme.Modules.pullback B).obj L) ≅ (Scheme.Modules.pullback
      C).obj L :=
  (Scheme.Modules.pullbackComp A B).app L ≪≫ (Scheme.Modules.pullbackCongr h).app L

/-- Cancel pullback along an isomorphism and its inverse. -/
def invHomIso {P Q : Scheme.{u}} (e : P ≅ Q) (N : Q.Modules) :
    (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj N) ≅ N :=
  objIso e.inv e.hom (𝟙 Q) e.inv_hom_id N ≪≫ (Scheme.Modules.pullbackId Q).app N

/-- Compare module pullbacks around a commutative square. -/
def squareIso {P Q P' Q' : Scheme.{u}} (A : P ⟶ Q) (B : Q ⟶ Q') (A' : P ⟶ P') (B' : P' ⟶ Q')
    (h : A ≫ B = A' ≫ B')
    (L : Q'.Modules) :
    (Scheme.Modules.pullback A).obj ((Scheme.Modules.pullback B).obj L) ≅
      (Scheme.Modules.pullback A').obj ((Scheme.Modules.pullback B').obj L) :=
  objIso A B _ h L ≪≫ (objIso A' B' _ rfl L).symm

/-- Transport rigidification through an isomorphism preserving the section and base. -/
def rigidifyTransport {P₁ P₂ T : Scheme.{u}} (e : P₁ ≅ P₂) (σ₁ : T ⟶ P₁) (σ₂ : T ⟶ P₂)
    (hσ : σ₁ ≫ e.hom = σ₂)
    (q₁ : P₁ ⟶ T) (q₂ : P₂ ⟶ T) (hq : e.hom ≫ q₂ = q₁) (N : P₂.Modules) :
    (Scheme.Modules.pullback e.inv).obj (Scheme.Modules.rigidify σ₁ q₁ ((Scheme.Modules.pullback
      e.hom).obj N)) ≅
      Scheme.Modules.rigidify σ₂ q₂ N :=
  Scheme.Modules.pullbackTensorObjIso e.inv _ _ ≪≫
    (invHomIso e N ⊗ᵢ
      (objIso e.inv q₁ q₂ (by rw [← hq, Iso.inv_hom_id_assoc]) _ ≪≫
        (Scheme.Modules.pullback q₂).mapIso (Scheme.Modules.dualMapIso (objIso σ₁ e.hom σ₂ hσ N))))

end Transport

section Poincare

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)} {e : SchemeHomOver (𝟙 (Spec
  (CommRingCat.of R))) c}
  {G : RelativePic0Designation R c} (hGR : RepresentsRelSubPic c e (algEquivZeroCut c e) G)
  (hG : RepresentsRelSubPic (baseChange R c κ) (sectionBaseChange κ e)
    (algEquivZeroCut (baseChange R c κ) (sectionBaseChange κ e)) (G.baseChange κ))
  (hPG : Nonempty (hG.poincare.L ≅ (BaseChange.ofR c e κ
    (hGR.poincare.pullbackAlong ⟨pullback.fst G.toBase (specMap R κ), pullback.condition⟩)).L))
  (τ : SchemeHomOver (specMap R κ) (specMap R κ))

/-- Map an iterated base change to the original universal family. -/
def qMap {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)}
    (p : SchemeHomOver t (G.baseChange κ).toBase) :
    pullback (baseChange R c κ) t ⟶ pullback c G.toBase :=
  baseChangeSnd (baseChange R c κ) p ≫ (BaseChange.κ c κ (G.baseChange κ).toBase).hom ≫
    baseChangeSnd c (⟨pullback.fst G.toBase (specMap R κ), pullback.condition⟩ :
      SchemeHomOver ((G.baseChange κ).toBase ≫ specMap R κ) G.toBase)

/-- The curve coordinate of the map to the universal family. -/
theorem qMap_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)}
    (p : SchemeHomOver t (G.baseChange κ).toBase) :
    qMap p ≫ pullback.fst c G.toBase = pullback.fst _ _ ≫ pullback.fst c 𝔰 := by
  simp only [qMap, Category.assoc, baseChangeSnd_fst'', BaseChange.κ_hom_fst,
    baseChangeSnd_fst''_assoc]

/-- The parameter coordinate of the map to the universal family. -/
theorem qMap_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)}
    (p : SchemeHomOver t (G.baseChange κ).toBase) :
    qMap p ≫ pullback.snd c G.toBase = pullback.snd _ _ ≫ p.1 ≫ pullback.fst G.toBase 𝔰 := by
  simp only [qMap, Category.assoc, baseChangeSnd_snd'', reassoc_of% (BaseChange.κ_hom_snd c κ
    (G.baseChange κ).toBase),
    baseChangeSnd_snd''_assoc]

include hPG in
/-- Compare the base-changed Poincare bundle with its original pullback. -/
theorem nonempty_poincare_pullbackAlong_iso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)}
    (p : SchemeHomOver t (G.baseChange κ).toBase) :
    Nonempty ((hG.poincare.pullbackAlong p).L ≅ (Scheme.Modules.pullback (qMap p)).obj
      hGR.poincare.L) := by
  obtain ⟨eP⟩ := hPG
  exact ⟨(Scheme.Modules.pullback _).mapIso eP ≪≫ objIso _ _ _ rfl _ ≪≫ objIso _ _ _ rfl _⟩

include hPG in
/-- Compare Poincare bundles at points with the same original coordinate. -/
theorem nonempty_poincare_pullbackAlong_iso_of_fst_eq {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of κ)}
    (p : SchemeHomOver (t ≫ τ.1) (G.baseChange κ).toBase) (q : SchemeHomOver t (G.baseChange
      κ).toBase)
    (hpq : p.1 ≫ pullback.fst G.toBase 𝔰 = q.1 ≫ pullback.fst G.toBase 𝔰) :
    Nonempty ((hG.poincare.pullbackAlong p).L ≅
      (Scheme.Modules.pullback (piHom c τ t)).obj (hG.poincare.pullbackAlong q).L) := by
  have hQ : piHom c τ t ≫ qMap q = qMap p := by
    apply pullback.hom_ext
    · rw [Category.assoc, qMap_fst, qMap_fst, piHom_fst_fst]
    · rw [Category.assoc, qMap_snd, qMap_snd, piHom_snd_assoc, hpq]
  obtain ⟨e₁⟩ := nonempty_poincare_pullbackAlong_iso hGR hG hPG p
  obtain ⟨e₂⟩ := nonempty_poincare_pullbackAlong_iso hGR hG hPG q
  exact ⟨e₁ ≪≫ (objIso _ _ _ hQ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso e₂.symm⟩

end Poincare

section Curves

variable {𝔛 𝔛₀ : Scheme.{u}} {x : 𝔛 ⟶ Spec (CommRingCat.of R)} {x₀ : 𝔛₀ ⟶ Spec (CommRingCat.of R)}
  (f : pullback x₀ (specMap R κ) ⟶ pullback x (specMap R κ)) (hf : f ≫ baseChange R x κ =
    baseChange R x₀ κ)
  (τ : SchemeHomOver (specMap R κ) (specMap R κ))
  (hcomm : baseChangeSnd x₀ τ ≫ f = f ≫ baseChangeSnd x τ)

/-- The iterated pullback comparison cancels the change of base. -/
theorem piHom_fst_baseChangeSnd {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of κ)) :
    piHom c τ t ≫ pullback.fst _ _ ≫ baseChangeSnd c τ = pullback.fst _ _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeSnd_fst'', piHom_fst_fst]
  · simp only [Category.assoc, baseChangeSnd_snd'', piHom_fst_snd_assoc]
    exact pullback.condition.symm

include hcomm in
/-- A compatible curve map preserves its first coordinate under base change. -/
theorem baseChangeSnd_f_fst : baseChangeSnd x₀ τ ≫ f ≫ pullback.fst x 𝔰 = f ≫ pullback.fst x 𝔰 := by
  rw [reassoc_of% hcomm, baseChangeSnd_fst'']

include hcomm in
/-- Changing the curve commutes with the iterated pullback comparison. -/
theorem curveChange_piHom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) :
    curveChange f hf (t ≫ τ.1) ≫ piHom x τ t = piHom x₀ τ t ≫ curveChange f hf t := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, piHom_fst_fst,
        curveChange_fst''_assoc,
        curveChange_fst''_assoc, ← piHom_fst_baseChangeSnd τ x₀ t, Category.assoc, Category.assoc,
        baseChangeSnd_f_fst f τ hcomm]
    · have h₁ : pullback.fst (baseChange R x κ) t ≫ pullback.snd x 𝔰 = pullback.snd _ _ ≫ t :=
        pullback.condition
      rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, piHom_fst_snd,
        curveChange_snd''_assoc,
        h₁, curveChange_snd''_assoc, piHom_snd_assoc]
  · rw [Category.assoc, Category.assoc, piHom_snd, curveChange_snd'', curveChange_snd'', piHom_snd]

include hcomm in
/-- The commuting comparison square gives an isomorphism of module pullbacks. -/
theorem nonempty_curveChange_piHom_iso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ))
    (M : (pullback (baseChange R x κ) t).Modules) :
    Nonempty ((Scheme.Modules.pullback (curveChange f hf (t ≫ τ.1))).obj ((Scheme.Modules.pullback
      (piHom x τ t)).obj M) ≅
      (Scheme.Modules.pullback (piHom x₀ τ t)).obj ((Scheme.Modules.pullback (curveChange f hf
        t)).obj M)) :=
  ⟨squareIso _ _ _ _ (curveChange_piHom f hf τ hcomm t) M⟩

end Curves

section Core

variable {𝔛 𝔛₀ : Scheme.{u}} {x : 𝔛 ⟶ Spec (CommRingCat.of R)} {x₀ : 𝔛₀ ⟶ Spec (CommRingCat.of R)}
  {εR : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x} {ε₀R : SchemeHomOver (𝟙 (Spec
    (CommRingCat.of R))) x₀}
  {D_R : RelativePic0Designation R x} {D₀ : RelativePic0Designation R x₀}
  (hD_R : RepresentsRelSubPic x εR (algEquivZeroCut x εR) D_R)
  (hD₀ : RepresentsRelSubPic x₀ ε₀R (algEquivZeroCut x₀ ε₀R) D₀)
  (hD : RepresentsRelSubPic (baseChange R x κ) (sectionBaseChange κ εR)
    (algEquivZeroCut (baseChange R x κ) (sectionBaseChange κ εR)) (D_R.baseChange κ))
  (hPD : Nonempty (hD.poincare.L ≅ (BaseChange.ofR x εR κ
    (hD_R.poincare.pullbackAlong ⟨pullback.fst D_R.toBase (specMap R κ), pullback.condition⟩)).L))
  (hD' : RepresentsRelSubPic (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)
    (algEquivZeroCut (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)) (D₀.baseChange κ))
  (hPD' : Nonempty (hD'.poincare.L ≅ (BaseChange.ofR x₀ ε₀R κ
    (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap R κ), pullback.condition⟩)).L))
  (f : pullback x₀ (specMap R κ) ⟶ pullback x (specMap R κ)) (hf : f ≫ baseChange R x κ =
    baseChange R x₀ κ)
  (τ : SchemeHomOver (specMap R κ) (specMap R κ))
  (hcomm : baseChangeSnd x₀ τ ≫ f = f ≫ baseChangeSnd x τ)
  (ν : SchemeHomOver (D_R.baseChange κ).toBase (D₀.baseChange κ).toBase)
  (hν : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D_R.baseChange
    κ).toBase),
    Nonempty ((hD'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν)).L ≅
      Scheme.Modules.rigidify (rigSection (baseChange R x₀ κ) t (sectionBaseChange κ ε₀R))
        (pullback.snd (baseChange R x₀ κ) t)
        ((Scheme.Modules.pullback (curveChange f hf t)).obj (hD.poincare.pullbackAlong a).L)))

/-- The composite from a twisted point has the twisted base coordinate. -/
theorem twist_comp_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)}
    (a : SchemeHomOver t (D_R.baseChange κ).toBase) :
    ((twistPt D_R.toBase τ a).1 ≫ ν.1) ≫ pullback.snd D₀.toBase 𝔰 = t ≫ τ.1 := by
  rw [Category.assoc]
  exact (congrArg (fun k => (twistPt D_R.toBase τ a).1 ≫ k) ν.2).trans (twistPt D_R.toBase τ a).2

include hD_R hD₀ hPD hPD' hcomm hν in
/-- Poincare classification identifies the flattened twisted image with the original image. -/
theorem flatPt_twist_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)}
    (a : SchemeHomOver t (D_R.baseChange κ).toBase) :
    flatPt D₀.toBase τ t ((twistPt D_R.toBase τ a).1 ≫ ν.1) (twist_comp_snd τ ν a) =
      NeronModelInfra.schemeHomOverComp a ν := by
  apply hD'.ext_of_iso t
  let b : SchemeHomOver (t ≫ τ.1) (D₀.baseChange κ).toBase :=
    NeronModelInfra.schemeHomOverComp (twistPt D_R.toBase τ a) ν
  obtain ⟨e₁⟩ := nonempty_poincare_pullbackAlong_iso_of_fst_eq hD₀ hD' hPD' τ b
    (flatPt D₀.toBase τ t ((twistPt D_R.toBase τ a).1 ≫ ν.1) (twist_comp_snd τ ν a))
    (by rw [flatPt_coe_fst]; rfl)
  obtain ⟨e₂⟩ := hν (t ≫ τ.1) (twistPt D_R.toBase τ a)
  obtain ⟨e₃⟩ := nonempty_poincare_pullbackAlong_iso_of_fst_eq hD_R hD hPD τ (twistPt D_R.toBase τ
    a) a
    (twistPt_coe_fst D_R.toBase τ a)
  obtain ⟨e₄⟩ := nonempty_curveChange_piHom_iso f hf τ hcomm t (hD.poincare.pullbackAlong a).L
  obtain ⟨e₅⟩ := hν t a
  refine ⟨(invHomIso (piIso x₀ τ t) _).symm ≪≫ (Scheme.Modules.pullback (piInv x₀ τ t)).mapIso
    e₁.symm ≪≫
    (Scheme.Modules.pullback (piInv x₀ τ t)).mapIso e₂ ≪≫
    (Scheme.Modules.pullback (piInv x₀ τ t)).mapIso
      (Scheme.Modules.rigidifyMapIso _ _ ((Scheme.Modules.pullback _).mapIso e₃ ≪≫ e₄)) ≪≫
    rigidifyTransport (piIso x₀ τ t) _ _ (rigSection_piHom x₀ τ t ε₀R) _ _ (piHom_snd x₀ τ t) _ ≪≫
      e₅.symm⟩

include hD_R hD₀ hPD hPD' hcomm hν in
/-- A map characterized by Poincare pullback commutes with the base endomorphism. -/
theorem comm_of_characterisation :
    baseChangeSnd D_R.toBase τ ≫ ν.1 = ν.1 ≫ baseChangeSnd D₀.toBase τ := by
  have key := flatPt_twist_eq hD_R hD₀ hD hPD hD' hPD' f hf τ hcomm ν hν
    (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver (D_R.baseChange κ).toBase (D_R.baseChange κ).toBase)
  have e := flatPt_comp_baseChangeSnd D₀.toBase τ _ _ (twist_comp_snd τ ν
    (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver (D_R.baseChange κ).toBase (D_R.baseChange κ).toBase))
  rw [key] at e
  change (𝟙 _ ≫ ν.1) ≫ baseChangeSnd D₀.toBase τ = (𝟙 _ ≫ baseChangeSnd D_R.toBase τ) ≫ ν.1 at e
  simpa only [Category.id_comp, Category.assoc] using e.symm

end Core

section Clause1

variable {𝔛 𝔛₀ : Scheme.{u}} {x : 𝔛 ⟶ Spec (CommRingCat.of R)} {x₀ : 𝔛₀ ⟶ Spec (CommRingCat.of R)}
  {εR : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x} {ε₀R : SchemeHomOver (𝟙 (Spec
    (CommRingCat.of R))) x₀}
  {D_R : RelativePic0Designation R x} {D₀ : RelativePic0Designation R x₀}
  (hD : RepresentsRelSubPic (baseChange R x κ) (sectionBaseChange κ εR)
    (algEquivZeroCut (baseChange R x κ) (sectionBaseChange κ εR)) (D_R.baseChange κ))
  (hD' : RepresentsRelSubPic (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)
    (algEquivZeroCut (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)) (D₀.baseChange κ))
  (f : pullback x₀ (specMap R κ) ⟶ pullback x (specMap R κ)) (hf : f ≫ baseChange R x κ =
    baseChange R x₀ κ)
  (hε : (sectionBaseChange κ ε₀R).1 ≫ f = (sectionBaseChange κ εR).1)

/-- The Picard pullback map is characterized by rigidified curve pullback. -/
theorem characterisation_pullbackHom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ))
    (a : SchemeHomOver t (D_R.baseChange κ).toBase) :
    Nonempty ((hD'.poincare.pullbackAlong
        (NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom f hf hε hD hD'))).L ≅
      Scheme.Modules.rigidify (rigSection (baseChange R x₀ κ) t (sectionBaseChange κ ε₀R))
        (pullback.snd (baseChange R x₀ κ) t)
        ((Scheme.Modules.pullback (curveChange f hf t)).obj (hD.poincare.pullbackAlong a).L)) := by
  have hmem : (algEquivZeroCut (baseChange R x κ) (sectionBaseChange κ εR)).P t
    (hD.poincare.pullbackAlong a) :=
    (algEquivZeroCut _ _).pullback_mem _ _ a _ hD.poincare_mem
  have ha : a = hD.classify t (hD.poincare.pullbackAlong a) hmem := hD.classify_unique t _ hmem a
    ⟨Iso.refl _⟩
  have hc : NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom f hf hε hD hD') =
      postComp (RepresentsRelSubPic.pullbackHom f hf hε hD hD') a := rfl
  have h₂ := RepresentsRelSubPic.postComp_pullbackHom_classify f hf hε hD hD' t
    (hD.poincare.pullbackAlong a) hmem
  rw [← ha] at h₂
  obtain ⟨e₁⟩ := hD'.classify_spec t ((hD.poincare.pullbackAlong a).pullbackCurve f hf hε)
    (FibrewiseAlgEquivZero.pullbackCurve f hf hε hmem)
  obtain ⟨e₂⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    ((hD.poincare.pullbackAlong a).pullbackCurve f hf hε)
  rw [hc, h₂]
  exact ⟨e₁ ≪≫ e₂.symm⟩

end Clause1

end TwistNatAux

attribute [local simp] TwistNatAux.twistPt_coe
attribute [local simp] TwistNatAux.piIso_hom
attribute [local simp] TwistNatAux.piIso_inv

end

attribute [local simp] TwistNatAux.twistPt_coe
attribute [local simp] TwistNatAux.piIso_hom
attribute [local simp] TwistNatAux.piIso_inv

open TwistNatAux in
/-- Picard restriction and maps with its Poincare characterization commute with base change. -/
theorem _root_.AlgebraicGeometry.RelPicard.baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp
    {R : Type u} [CommRing R] (κ : Type u) [CommRing κ] [Algebra R κ]
    {𝔛 𝔛₀ : Scheme.{u}} {x : 𝔛 ⟶ Spec (CommRingCat.of R)} {x₀ : 𝔛₀ ⟶ Spec (CommRingCat.of R)}
    {εR : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x} {ε₀R : SchemeHomOver (𝟙 (Spec
      (CommRingCat.of R))) x₀}
    {D_R : RelativePic0Designation R x} {D₀ : RelativePic0Designation R x₀}
    (hD_R : RepresentsRelSubPic x εR (algEquivZeroCut x εR) D_R)
    (hD₀ : RepresentsRelSubPic x₀ ε₀R (algEquivZeroCut x₀ ε₀R) D₀)
    (hD : RepresentsRelSubPic (baseChange R x κ) (sectionBaseChange κ εR)
      (algEquivZeroCut (baseChange R x κ) (sectionBaseChange κ εR)) (D_R.baseChange κ))
    (hPD : Nonempty (hD.poincare.L ≅ (BaseChange.ofR x εR κ
      (hD_R.poincare.pullbackAlong ⟨pullback.fst D_R.toBase (specMap R κ), pullback.condition⟩)).L))
    (hD' : RepresentsRelSubPic (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)
      (algEquivZeroCut (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)) (D₀.baseChange κ))
    (hPD' : Nonempty (hD'.poincare.L ≅ (BaseChange.ofR x₀ ε₀R κ
      (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap R κ), pullback.condition⟩)).L))
    (f : pullback x₀ (specMap R κ) ⟶ pullback x (specMap R κ)) (hf : f ≫ baseChange R x κ =
      baseChange R x₀ κ)
    (τ : SchemeHomOver (specMap R κ) (specMap R κ))
    (hcomm : baseChangeSnd x₀ τ ≫ f = f ≫ baseChangeSnd x τ) :
    (∀ hε : (sectionBaseChange κ ε₀R).1 ≫ f = (sectionBaseChange κ εR).1,
      baseChangeSnd D_R.toBase τ ≫ (RepresentsRelSubPic.pullbackHom f hf hε hD hD').1 =
        (RepresentsRelSubPic.pullbackHom f hf hε hD hD').1 ≫ baseChangeSnd D₀.toBase τ) ∧
    (∀ ν : SchemeHomOver (D_R.baseChange κ).toBase (D₀.baseChange κ).toBase,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D_R.baseChange
        κ).toBase),
        Nonempty ((hD'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν)).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange R x₀ κ) t (sectionBaseChange κ ε₀R))
            (pullback.snd (baseChange R x₀ κ) t)
            ((Scheme.Modules.pullback (curveChange f hf t)).obj (hD.poincare.pullbackAlong a).L))) →
      baseChangeSnd D_R.toBase τ ≫ ν.1 = ν.1 ≫ baseChangeSnd D₀.toBase τ) := by
  refine ⟨fun hε => ?_, fun ν hν => ?_⟩
  · exact comm_of_characterisation hD_R hD₀ hD hPD hD' hPD' f hf τ hcomm _
      (fun t a => characterisation_pullbackHom (κ := κ) hD hD' f hf hε t a)
  · exact comm_of_characterisation hD_R hD₀ hD hPD hD' hPD' f hf τ hcomm ν (fun t a => hν t a)
end JacobianVarieties.Picard.Proofs.RestrictedBaseChange
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
attribute [-simp]
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
