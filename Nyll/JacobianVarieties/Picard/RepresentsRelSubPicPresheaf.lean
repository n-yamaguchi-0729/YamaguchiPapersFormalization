/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelSubPicPresheaf.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation

import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
/-!
# Representations of the relative sub-Picard presheaf

A representing relative Picard designation classifies the permitted rigidified line-bundle
classes and determines a representation of their presheaf. Conversely, a presheaf
representation compatible with the zero class supplies the designation's universal bundle.
-/

noncomputable section

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian Opposite

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

namespace RepresentsRelSubPic

variable {P : SubPicCondition c ε} {D : RelativePic0Designation R c}

/-- The permitted line-bundle class obtained by pulling back the universal bundle. -/
def pullbackClass (h : RepresentsRelSubPic c ε P D) (X : Over (Spec (CommRingCat.of R)))
    (g : X ⟶ Over.mk D.toBase) : (relSubPicPresheaf c ε P).obj (op X) :=
  ⟨Quotient.mk _ (h.poincare.pullbackAlong ⟨g.left, Over.w g⟩),
    P.pullback_mem _ _ _ _ h.poincare_mem⟩

/-- The classifying morphism of a permitted rigidified line-bundle class. -/
noncomputable def classifyClass (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : RigidifiedLineBundle.Classes c ε t)
    (hx : P.onClasses t x) :
    SchemeHomOver t D.toBase :=
  h.classify t x.out (by rwa [← Quotient.out_eq x] at hx)

theorem eq_classifyClass (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : RigidifiedLineBundle.Classes c ε t)
    (hx : P.onClasses t x)
    (g : SchemeHomOver t D.toBase) (hg : Quotient.mk _ (h.poincare.pullbackAlong g) = x) :
    g = h.classifyClass t x hx := by
  refine h.classify_unique t _ _ g ?_
  rw [← Quotient.out_eq x] at hg
  exact Quotient.exact hg

theorem mk_pullbackAlong_classifyClass (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : RigidifiedLineBundle.Classes c ε t)
    (hx : P.onClasses t x) :
    Quotient.mk _ (h.poincare.pullbackAlong (h.classifyClass t x hx)) = x := by
  conv_rhs => rw [← Quotient.out_eq x]
  exact Quotient.sound (h.classify_spec t _ _)

/-- The presheaf representation induced by the universal rigidified line bundle. -/
noncomputable def representableBy (h : RepresentsRelSubPic c ε P D) :
    (relSubPicPresheaf c ε P).RepresentableBy (Over.mk D.toBase) where
  homEquiv {X} :=
    { toFun := fun g => h.pullbackClass X g
      invFun := fun x =>
        Over.homMk (h.classifyClass X.hom x.1 x.2).1 (h.classifyClass X.hom x.1 x.2).2
      left_inv := fun g => Over.OverMorphism.ext (congrArg Subtype.val
        (h.eq_classifyClass X.hom _ _ ⟨g.left, Over.w g⟩ rfl)).symm
      right_inv := fun x => Subtype.ext (h.mk_pullbackAlong_classifyClass X.hom x.1 x.2) }
  homEquiv_comp {X X'} f g := by
    apply Subtype.ext
    apply Quotient.sound
    exact ⟨(h.poincare.pullbackAlongPullbackAlongIso ⟨g.left, Over.w g⟩ ⟨f.left, Over.w f⟩).symm⟩

end RepresentsRelSubPic


namespace RepresentsRelSubPic

variable {P : SubPicCondition c ε} {D : RelativePic0Designation R c}

theorem nonempty_of_representableBy
    (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk D.toBase))
    (h0 : (e.homEquiv (Over.homMk D.zeroSection D.zeroSection_toBase :
        Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk D.toBase)).1 =
      relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _))) :
    Nonempty (RepresentsRelSubPic c ε P D) := by
  let u := e.homEquiv (𝟙 (Over.mk D.toBase))
  let Q : RigidifiedLineBundle c ε D.toBase := u.1.out
  have hQ : P.P D.toBase Q := by
    have h2 : P.onClasses D.toBase u.1 := u.2
    rwa [← Quotient.out_eq u.1] at h2
  have key : ∀ (X : Over (Spec (CommRingCat.of R))) (g : X ⟶ Over.mk D.toBase),
      (e.homEquiv g).1 = Quotient.mk _ (Q.pullbackAlong ⟨g.left, Over.w g⟩) := by
    intro X g
    have hc := e.homEquiv_comp g (𝟙 _)
    rw [Category.comp_id] at hc
    rw [hc, relSubPicPresheaf_map_coe]
    change RigidifiedLineBundle.classesMap _ u.1 = _
    conv_lhs => rw [← Quotient.out_eq u.1]
    rfl
  refine ⟨{ poincare := Q, poincare_mem := hQ, univ := ?_, zero := ?_ }⟩
  · intro T t M hM
    let x : (relSubPicPresheaf c ε P).obj (op (Over.mk t)) := ⟨Quotient.mk _ M, hM⟩
    let g : Over.mk t ⟶ Over.mk D.toBase := e.homEquiv.symm x
    have hg : e.homEquiv g = x := e.homEquiv.apply_symm_apply x
    refine ⟨⟨g.left, Over.w g⟩, ?_, fun g'' hg'' => ?_⟩
    · have h1 : (e.homEquiv g).1 = Quotient.mk _ M := congrArg Subtype.val hg
      rw [key] at h1
      exact Quotient.exact h1
    · have h2 : e.homEquiv (Over.homMk g''.1 g''.2 : Over.mk t ⟶ Over.mk D.toBase) = x := by
        apply Subtype.ext
        rw [key]
        exact Quotient.sound hg''
      have h3 : (Over.homMk g''.1 g''.2 : Over.mk t ⟶ Over.mk D.toBase) = g :=
        e.homEquiv.injective (h2.trans hg.symm)
      exact Subtype.ext (congrArg (fun k => k.left) h3)
  · have h1 := h0
    rw [key] at h1
    exact Quotient.exact h1

end RepresentsRelSubPic


end AlgebraicGeometry.RelPicard

end
