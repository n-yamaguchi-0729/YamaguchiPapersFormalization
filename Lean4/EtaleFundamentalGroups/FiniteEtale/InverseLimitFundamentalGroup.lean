/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.InverseLimitDiagram
import EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
import ProCGroups.InverseSystems.StagewiseIso

/-!
# The original fundamental-group maps in the pullback inverse system

The canonical pullback-fiber isomorphisms identify stage automorphisms with
the original geometric-point fundamental groups.  The intertwining equation
retains the given scheme transition and the cone-induced point equality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open ProCGroups.InverseSystems

namespace CategoryTheory.PreGaloisCategory

universe u₀ v₀ u₁ v₁ w

private theorem conjAut_autHomOfCompIso
    {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
    (H : C₀ ⥤ C₁) {F₀ G₀ : C₀ ⥤ FintypeCat.{w}}
    {F₁ G₁ : C₁ ⥤ FintypeCat.{w}}
    (r : H ⋙ F₁ ≅ F₀) (e₀ : F₀ ≅ G₀) (e₁ : F₁ ≅ G₁)
    (t : H ⋙ G₁ ≅ G₀) (h : r ≪≫ e₀ = isoWhiskerLeft H e₁ ≪≫ t)
    (a : Aut F₁) :
    e₀.conjAut (autHomOfCompIso H r a) =
      autHomOfCompIso H t (e₁.conjAut a) := by
  have hw :
      (isoWhiskerLeft H e₁).conjAut
          (((whiskeringLeft C₀ C₁ FintypeCat.{w}).obj H).mapAut F₁ a) =
        (((whiskeringLeft C₀ C₁ FintypeCat.{w}).obj H).mapAut G₁ (e₁.conjAut a)) := by
    apply Iso.ext
    apply NatTrans.ext
    funext A
    simp only [Iso.conjAut_hom, Iso.conj_apply, NatTrans.comp_app]
    rfl
  change e₀.conjAut
      (r.conjAut (((whiskeringLeft C₀ C₁ FintypeCat.{w}).obj H).mapAut F₁ a)) =
    t.conjAut (((whiskeringLeft C₀ C₁ FintypeCat.{w}).obj H).mapAut G₁ (e₁.conjAut a))
  rw [← Iso.trans_conjAut, h, Iso.trans_conjAut, hw]

end CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

/-- Transport of the target geometric point preserves the original
fundamental-group homomorphism and its canonical pullback comparison. -/
theorem fundamentalGroupHom_transport
    {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]
    (f : X ⟶ Y) (point : Spec (.of Ω) ⟶ X) (eta : Spec (.of Ω) ⟶ Y)
    (h : point ≫ f = eta) (a : π₁ᵉᵗ(point)) :
    autHomOfCompIso (pullback f)
        (pullbackFiberIso f point ≪≫ eqToIso (congrArg fiber h)) a =
      h ▸ fundamentalGroupHom f point a := by
  subst eta
  change autHomOfCompIso (pullback f) (pullbackFiberIso f point ≪≫ Iso.refl _) a =
    autHomOfCompIso (pullback f) (pullbackFiberIso f point) a
  rw [Iso.trans_refl]

namespace InverseLimitDiagram

variable {I : Type u} [Preorder I]
variable (D : Iᵒᵖ ⥤ Scheme.{u}) (s : Cone D)
variable {Ω : Type u} [Field Ω] (point : Spec (.of Ω) ⟶ s.pt)

/-- The prescribed point on the original stage. -/
def stagePoint (i : I) : Spec (.of Ω) ⟶ D.obj (Opposite.op i) :=
  point ≫ s.π.app (Opposite.op i)

/-- The point compatibility is exactly the cone equation. -/
theorem stagePoint_comp {i j : I} (hij : i ≤ j) :
    stagePoint D s point j ≫ transitionMap D hij = stagePoint D s point i :=
  (Category.assoc point (s.π.app (Opposite.op j)) (transitionMap D hij)).trans
    (congrArg (fun p ↦ point ≫ p) (s.w (homOfLE hij).op))

/-- The original pullback-fiber comparison at a cone leg. -/
def stageFiberIso (i : I) :
    toLimit D s i ⋙ fiber point ≅ fiber (stagePoint D s point i) :=
  pullbackFiberIso (s.π.app (Opposite.op i)) point

/-- The canonical fiber comparison of the original transition, with its
cone-induced equality of geometric points. -/
def pointedTransitionIso {i j : I} (hij : i ≤ j) :
    transition D hij ⋙ fiber (stagePoint D s point j) ≅
      fiber (stagePoint D s point i) :=
  pullbackFiberIso (transitionMap D hij) (stagePoint D s point j) ≪≫
    eqToIso (congrArg fiber (stagePoint_comp D s point hij))

/-- The point comparisons commute with the actual pullback cone comparison. -/
theorem stageFiberIso_coherence {i j : I} (hij : i ≤ j) :
    isoWhiskerRight (comparison D s hij) (fiber point) ≪≫
      associator (transition D hij) (toLimit D s j) (fiber point) ≪≫
      isoWhiskerLeft (transition D hij) (stageFiberIso D s point j) ≪≫
      pointedTransitionIso D s point hij = stageFiberIso D s point i := by
  exact pullbackCompositeFiberIsoOfEq_eq_pullbackFiberIso
    (s.π.app (Opposite.op j)) (transitionMap D hij) (s.π.app (Opposite.op i))
    (s.w (homOfLE hij).op).symm point (stagePoint_comp D s point hij)

/-- Under the actual fiber comparisons, restriction is the original
fundamental-group homomorphism with the original point transport. -/
theorem stageAutRestriction_eq_fundamentalGroupHom {i j : I} (hij : i ≤ j)
    (a : Aut (toLimit D s j ⋙ fiber point)) :
    (stageFiberIso D s point i).conjAut
        (stageAutRestriction (stage D) (toLimit D s) (transition D) (comparison D s)
          (fiber point) hij a) =
      stagePoint_comp D s point hij ▸
        fundamentalGroupHom (transitionMap D hij) (stagePoint D s point j)
          ((stageFiberIso D s point j).conjAut a) := by
  let q : toLimit D s i ⋙ fiber point ≅
      transition D hij ⋙ toLimit D s j ⋙ fiber point :=
    isoWhiskerRight (comparison D s hij) (fiber point) ≪≫
      associator (transition D hij) (toLimit D s j) (fiber point)
  let b : transition D hij ⋙ toLimit D s j ⋙ fiber point ≅
      fiber (stagePoint D s point i) :=
    isoWhiskerLeft (transition D hij) (stageFiberIso D s point j) ≪≫
      pointedTransitionIso D s point hij
  have hc : q ≪≫ b = stageFiberIso D s point i := by
    exact (Iso.trans_assoc _ _ _).trans (stageFiberIso_coherence D s point hij)
  have htransport : q.symm ≪≫ stageFiberIso D s point i = b :=
    (congrArg (fun t ↦ q.symm ≪≫ t) hc.symm).trans (Iso.symm_self_id_assoc q b)
  have hgroup := conjAut_autHomOfCompIso (transition D hij) q.symm
    (stageFiberIso D s point i) (stageFiberIso D s point j)
    (pointedTransitionIso D s point hij) htransport a
  exact hgroup.trans (fundamentalGroupHom_transport (transitionMap D hij)
    (stagePoint D s point j) (stagePoint D s point i) (stagePoint_comp D s point hij)
    ((stageFiberIso D s point j).conjAut a))

/-- Global restriction followed by the canonical stage comparison is exactly
the original fundamental-group map of that cone leg. -/
theorem globalAutRestriction_eq_fundamentalGroupHom (i : I) (a : π₁ᵉᵗ(point)) :
    (stageFiberIso D s point i).conjAut
        (globalAutRestriction (stage D) (toLimit D s) (fiber point) i a) =
      fundamentalGroupHom (s.π.app (Opposite.op i)) point a := rfl

end InverseLimitDiagram

end AlgebraicGeometry.FiniteEtale
