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
import Nyll.AlgebraicCurves.Geometry.Picard.SubPicCondition

/-!
Presheaves of rigidified line-bundle classes satisfying a pullback-stable Picard condition.
-/

noncomputable section

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian Opposite

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

namespace RigidifiedLineBundle

/-- The underlying line-bundle isomorphism comparing iterated pullback with pullback along a
composite.
-/
noncomputable def pullbackAlongPullbackAlongIso {T T' T'' : Scheme.{u}} {t : T ⟶ Spec
    (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {t'' : T'' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (ψ : SchemeHomOver t' t) (φ : SchemeHomOver t'' t') :
    ((M.pullbackAlong ψ).pullbackAlong φ).L ≅ (M.pullbackAlong (postComp ψ φ)).L :=
  (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c ψ φ)).app M.L

/-- The underlying line-bundle isomorphism from pullback along the identity to the original
bundle.
-/
noncomputable def pullbackAlongIdIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) :
    (M.pullbackAlong ⟨𝟙 T, Category.id_comp t⟩).L ≅ M.L :=
  (Scheme.Modules.pullbackCongr (baseChangeSnd_id c t)).app M.L ≪≫
    (Scheme.Modules.pullbackId _).app M.L

end RigidifiedLineBundle

namespace SubPicCondition

/-- The Picard condition descended to isomorphism classes of rigidified line bundles. -/
def onClasses (P : SubPicCondition c ε) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    RigidifiedLineBundle.Classes c ε t → Prop :=
  Quotient.lift (P.P t) fun M M' h => propext ⟨P.congr t M M' h, P.congr t M' M ⟨h.some.symm⟩⟩

@[simp] theorem onClasses_mk (P : SubPicCondition c ε) {T : Scheme.{u}} (t : T ⟶ Spec
    (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) : P.onClasses t (Quotient.mk _ M) ↔ P.P t M := Iff.rfl

theorem onClasses_classesMap (P : SubPicCondition c ε) {T T' : Scheme.{u}} {t : T ⟶ Spec
    (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) (x :
      RigidifiedLineBundle.Classes c ε t)
    (hx : P.onClasses t x) : P.onClasses t' (RigidifiedLineBundle.classesMap ψ x) := by
  induction x using Quotient.ind
  exact P.pullback_mem _ _ ψ _ hx

end SubPicCondition

/-- The subfunctor of relative Picard classes satisfying the given condition. -/
def relSubPicSubfunctor (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec
    (CommRingCat.of R))) c)
    (P : SubPicCondition c ε) : Subfunctor (relPicardPresheaf c ε) where
  obj X := {x | P.onClasses X.unop.hom x}
  map φ := fun x hx => P.onClasses_classesMap ⟨φ.unop.left, Over.w φ.unop⟩ x hx

/-- The presheaf of relative Picard classes satisfying the given condition. -/
def relSubPicPresheaf (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec
    (CommRingCat.of R))) c)
    (P : SubPicCondition c ε) : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1) :=
  (relSubPicSubfunctor c ε P).toFunctor


@[simp] theorem relSubPicPresheaf_map_coe {P : SubPicCondition c ε} {X X' : (Over (Spec
    (CommRingCat.of R)))ᵒᵖ}
    (φ : X ⟶ X') (x : (relSubPicPresheaf c ε P).obj X) :
    ((relSubPicPresheaf c ε P).map φ x).1 = RigidifiedLineBundle.classesMap ⟨φ.unop.left, Over.w
      φ.unop⟩ x.1 :=
  rfl


end AlgebraicGeometry.RelPicard

end
