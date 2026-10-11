/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitStages
import Nyll.SchemeTheory.FiniteEtale.InverseLimitEquality
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Faithfulness of the finite étale model localization

Equality after base change is detected after an actual later refinement.
The existing calculus-of-fractions criterion then proves faithfulness of
the comparison functor.  No individual stage pullback is assumed faithful.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteEtale.InverseLimitModel

universe u

variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable (F : Iᵒᵖ ⥤ Scheme.{u}) (s : Cone F) (hs : IsLimit s)
variable [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (F.map h)]
variable [∀ i : Iᵒᵖ, CompactSpace (F.obj i)]

include hs

/-- Two actual model arrows which agree at the limit agree after a
cartesian refinement of their original source. -/
theorem exists_refinement_map_eq
    {A B : InverseLimitModel F} (f g : A ⟶ B)
    (hfg : (baseChange F s).map f = (baseChange F s).map g) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ A.right),
      refinementHom F A h ≫ f = refinementHom F A h ≫ g := by
  let i := A.right
  let q : i ⟶ B.right := f.right
  let Bq : FiniteEtale (F.obj i) := (pullback (F.map q)).obj (stageObj F B)
  have hg : g.left ≫ B.hom = A.hom ≫ F.map q :=
    g.w.trans (congrArg (fun a ↦ A.hom ≫ F.map a) (Subsingleton.elim g.right q))
  let f₀ : stageObj F A ⟶ Bq := MorphismProperty.Over.homMk
    (Limits.pullback.lift f.left A.hom f.w) (Limits.pullback.lift_snd _ _ _)
  let g₀ : stageObj F A ⟶ Bq := MorphismProperty.Over.homMk
    (Limits.pullback.lift g.left A.hom hg) (Limits.pullback.lift_snd _ _ _)
  let af : A ⟶ refinementObj F B q := (stageInclusion F i).map f₀
  let ag : A ⟶ refinementObj F B q := (stageInclusion F i).map g₀
  let d : refinementObj F B q ⟶ B := refinementHom F B q
  have hfacf : af ≫ d = f := by
    apply MorphismProperty.Comma.Hom.ext
    · exact Limits.pullback.lift_fst _ _ _
    · exact Category.id_comp q
  have hfacg : ag ≫ d = g := by
    apply MorphismProperty.Comma.Hom.ext
    · exact Limits.pullback.lift_fst _ _ _
    · exact Subsingleton.elim _ _
  have : IsIso ((baseChange F s).map d) :=
    baseChange_inverts_cartesian F s d (refinementHom_cartesian F B q)
  have hv : (baseChange F s).map af = (baseChange F s).map ag := by
    apply (cancel_mono ((baseChange F s).map d)).1
    calc
      (baseChange F s).map af ≫ (baseChange F s).map d =
          (baseChange F s).map (af ≫ d) := ((baseChange F s).map_comp af d).symm
      _ = (baseChange F s).map f := congrArg (baseChange F s).map hfacf
      _ = (baseChange F s).map g := hfg
      _ = (baseChange F s).map (ag ≫ d) := congrArg (baseChange F s).map hfacg.symm
      _ = (baseChange F s).map ag ≫ (baseChange F s).map d :=
        (baseChange F s).map_comp ag d
  have hf₀ : (baseChange F s).map af = (pullback (s.π.app i)).map f₀ :=
    (Functor.congr_hom (stageInclusion_comp_baseChange F s i) f₀).trans
      ((Category.id_comp _).trans (Category.comp_id _))
  have hg₀ : (baseChange F s).map ag = (pullback (s.π.app i)).map g₀ :=
    (Functor.congr_hom (stageInclusion_comp_baseChange F s i) g₀).trans
      ((Category.id_comp _).trans (Category.comp_id _))
  obtain ⟨j, h, hh⟩ := exists_inverse_limit_stage_map_eq F s hs i f₀ g₀
    (hf₀.symm.trans (hv.trans hg₀))
  have hv' : refinementHom F A h ≫ af = refinementHom F A h ≫ ag :=
    ((transition F h).naturality f₀).symm.trans
      ((congrArg
        (fun a ↦ (stageInclusion F j).map a ≫ (transition F h).app Bq) hh).trans
        ((transition F h).naturality g₀))
  refine ⟨j, h, ?_⟩
  calc
    refinementHom F A h ≫ f = refinementHom F A h ≫ (af ≫ d) :=
      congrArg (fun a ↦ refinementHom F A h ≫ a) hfacf.symm
    _ = (refinementHom F A h ≫ af) ≫ d := (Category.assoc _ _ _).symm
    _ = (refinementHom F A h ≫ ag) ≫ d := congrArg (fun a ↦ a ≫ d) hv'
    _ = refinementHom F A h ≫ (ag ≫ d) := Category.assoc _ _ _
    _ = refinementHom F A h ≫ g := congrArg (fun a ↦ refinementHom F A h ≫ a) hfacg

/-- The actual comparison from the model localization is faithful, by
geometric eventual equality and the existing fraction criterion. -/
theorem localizedBaseChange_faithful : (localizedBaseChange F s).Faithful := by
  let Q := (cartesian F).Q
  let G := localizedBaseChange F s
  have hbase : ∀ {A B : InverseLimitModel F} (f g : A ⟶ B),
      G.map (Q.map f) = G.map (Q.map g) → Q.map f = Q.map g := by
    intro A B f g h
    have hf : G.map (Q.map f) = (baseChange F s).map f :=
      (Functor.congr_hom (q_comp_localizedBaseChange F s) f).trans
        ((Category.id_comp _).trans (Category.comp_id _))
    have hg : G.map (Q.map g) = (baseChange F s).map g :=
      (Functor.congr_hom (q_comp_localizedBaseChange F s) g).trans
        ((Category.id_comp _).trans (Category.comp_id _))
    obtain ⟨j, a, ha⟩ := exists_refinement_map_eq F s hs f g (hf.symm.trans (h.trans hg))
    exact (MorphismProperty.map_eq_iff_precomp Q (cartesian F) f g).2
      ⟨refinementObj F A a, refinementHom F A a, refinementHom_cartesian F A a, ha⟩
  have hop : G.op.Faithful :=
    Functor.faithful_of_comp_of_hasLeftCalculusOfFractions Q.op (cartesian F).op G.op
      (fun {A B} f g h ↦ congrArg Quiver.Hom.op
        (hbase f.unop g.unop (congrArg Quiver.Hom.unop h)))
  constructor
  intro A B f g h
  exact Quiver.Hom.op_inj (G.op.map_injective (congrArg Quiver.Hom.op h))

end AlgebraicGeometry.FiniteEtale.InverseLimitModel
