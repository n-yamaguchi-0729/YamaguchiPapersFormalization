/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso

/-!
# Kernels and fixed fibers under a change of fiber functor

A natural isomorphism transports the kernel of restriction to another fiber
functor. It also transports fixed points of the induced automorphisms. These
are the two compatibility statements needed to use arbitrary geometric paths.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

universe u v u' v' w

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

/-- Changing the source and target fiber comparisons preserves the kernel of
restriction along a functor. -/
theorem autHomOfCompIso_conj_eq_one_of_eq_one
    (H : C ⥤ C') {F G : C' ⥤ FintypeCat.{w}}
    {F₀ G₀ : C ⥤ FintypeCat.{w}}
    (t : F ≅ G) (s : H ⋙ F ≅ F₀) (r : H ⋙ G ≅ G₀)
    (a : Aut F) (ha : autHomOfCompIso H s a = 1) :
    autHomOfCompIso H r (continuousConjAut t a) = 1 := by
  let P := (Functor.whiskeringLeft C C' FintypeCat.{w}).obj H
  have hp : P.mapIso a = (1 : Aut (H ⋙ F)) := by
    apply s.conjAut.injective
    exact ha.trans (map_one s.conjAut).symm
  change r.conjAut (P.mapIso (t.conjAut a)) = 1
  have hconj : P.mapIso (t.conjAut a) =
      (Functor.isoWhiskerLeft H t).conjAut (P.mapIso a) :=
    Functor.map_conjAut P t a
  exact (congrArg r.conjAut hconj).trans
    ((congrArg (fun b : Aut (H ⋙ F) =>
      r.conjAut ((Functor.isoWhiskerLeft H t).conjAut b)) hp).trans
      ((congrArg r.conjAut (map_one (Functor.isoWhiskerLeft H t).conjAut)).trans
        (map_one r.conjAut)))

/-- A fixed fiber after conjugating by a natural isomorphism was already fixed
before transport. -/
theorem fiber_fixed_of_conj_fixed
    {F G : C ⥤ FintypeCat.{w}} (t : F ≅ G) (a : Aut F)
    (W : C) (ha : ∀ w : G.obj W, continuousConjAut t a • w = w) :
    ∀ w : F.obj W, a • w = w := by
  intro w
  have h := ha ((t.app W).hom w)
  change t.hom.app W (a.hom.app W (t.inv.app W (t.hom.app W w))) =
    t.hom.app W w at h
  have hfixed : t.hom.app W (a.hom.app W w) = t.hom.app W w := by
    simpa only [← Iso.app_hom, ← Iso.app_inv, FintypeCat.hom_inv_id_apply] using h
  exact (ConcreteCategory.bijective_of_isIso (t.hom.app W)).injective hfixed

end CategoryTheory.PreGaloisCategory
