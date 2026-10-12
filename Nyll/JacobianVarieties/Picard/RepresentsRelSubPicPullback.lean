/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.JacobianVarieties.Picard.Designation

import Nyll.AlgebraicCurves.Geometry.Picard.Pullback

/-!
# Pullback on representing Picard schemes

Classify pullback of the Poincare bundle to obtain the induced morphism of Picard schemes.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)

namespace RepresentsRelSubPic

variable {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
  (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')

/-- The morphism of representing Picard schemes that classifies pullback along the curve map. -/
def pullbackHom : SchemeHomOver D.toBase D'.toBase :=
  h'.classify D.toBase (h.poincare.pullbackCurve f hf hε)
    (FibrewiseAlgEquivZero.pullbackCurve f hf hε h.poincare_mem)

theorem postComp_pullbackHom_classify {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : (algEquivZeroCut c ε).P t M) :
    postComp (pullbackHom f hf hε h h') (h.classify t M hM) =
      h'.classify t (M.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε hM) := by
  refine h'.classify_unique t _ _ _ ⟨?_⟩
  exact (h'.poincare.pullbackAlongPullbackAlongIso' _ _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (h'.classify_spec D.toBase _ _).some ≪≫
    (h.poincare.pullbackCurvePullbackAlongIso f hf hε _) ≪≫
    (Scheme.Modules.pullback _).mapIso (h.classify_spec t M hM).some

theorem pullbackHom_unique (g : SchemeHomOver D.toBase D'.toBase)
    (hg : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
      (hM : (algEquivZeroCut c ε).P t M),
      postComp g (h.classify t M hM) =
        h'.classify t (M.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε hM)) :
    g = pullbackHom f hf hε h h' := by
  have hid : h.classify D.toBase h.poincare h.poincare_mem = ⟨𝟙 _, Category.id_comp _⟩ :=
    (h.classify_unique D.toBase _ _ _
        ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_id c D.toBase)).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _⟩).symm
  have := hg D.toBase h.poincare h.poincare_mem
  rw [hid] at this
  refine Eq.trans ?_ this
  apply Subtype.ext
  exact (Category.id_comp g.1).symm

theorem zeroSection_pullbackHom :
    D.zeroSection ≫ (pullbackHom f hf hε h h').1 = D'.zeroSection := by
  have key := h'.ext_of_iso (𝟙 _)
    (postComp (pullbackHom f hf hε h h') ⟨D.zeroSection, D.zeroSection_toBase⟩)
    ⟨D'.zeroSection, D'.zeroSection_toBase⟩ ⟨?_⟩
  · exact congrArg Subtype.val key
  · exact (h'.poincare.pullbackAlongPullbackAlongIso' _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso (h'.classify_spec D.toBase _ _).some ≪≫
      (h.poincare.pullbackCurvePullbackAlongIso f hf hε _) ≪≫
      (Scheme.Modules.pullback _).mapIso h.zero.some ≪≫
      RigidifiedLineBundle.unitPullbackCurveIso f hf hε _ ≪≫ h'.zero.some.symm

theorem existsUnique_pullbackHom :
    ∃! fstar : SchemeHomOver D.toBase D'.toBase,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
        (hM : (algEquivZeroCut c ε).P t M),
        postComp fstar (h.classify t M hM) =
          h'.classify t (M.pullbackCurve f hf hε)
            (FibrewiseAlgEquivZero.pullbackCurve f hf hε hM) :=
  ⟨pullbackHom f hf hε h h', fun t M hM => postComp_pullbackHom_classify f hf hε h h' t M hM,
    fun g hg => pullbackHom_unique f hf hε h h' g hg⟩

end RepresentsRelSubPic

end AlgebraicGeometry.RelPicard

end
