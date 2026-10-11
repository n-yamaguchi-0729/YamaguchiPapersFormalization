/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import EtaleCohomology.Sites.ZariskiRestriction
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Types.Basic

/-!
# Equality of étale sections on an actual Zariski neighborhood

An étale neighborhood covers its open image. The small-site sheaf separation
axiom therefore turns equality on that neighborhood into equality on its
actual open image in the original scheme.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace EtaleCohomology

/-- Equality after restriction to an étale neighborhood gives equality on
an actual open neighborhood of each point in its image. -/
theorem exists_zariski_neighborhood_sections_eq_of_etale_map_eq
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (Type u))
    (U : X.Opens) (a b : F.obj.obj (op ((zariskiToEtale X).obj U)))
    (V : X.Etale) (g : V ⟶ (zariskiToEtale X).obj U)
    (hab : F.obj.map g.op a = F.obj.map g.op b) (v : V.left) :
    ∃ (W : X.Opens) (hWU : W ≤ U), V.hom v ∈ W ∧
      F.obj.map ((zariskiToEtale X).map (homOfLE hWU)).op a =
        F.obj.map ((zariskiToEtale X).map (homOfLE hWU)).op b := by
  let W : X.Opens := (etaleOpenImage X).obj V
  have hWU : W ≤ U := by
    rintro x ⟨t, rfl⟩
    have ht : U.ι (g.left t) = V.hom t :=
      (Scheme.Hom.comp_apply g.left U.ι t).symm.trans
        (congrArg (fun h : V.left ⟶ X => h t) g.w)
    rw [← ht]
    exact (g.left t).property
  let k : V ⟶ (zariskiToEtale X).obj W := (etaleOpenImageAdjunction X).unit.app V
  let j : (zariskiToEtale X).obj W ⟶ (zariskiToEtale X).obj U :=
    (zariskiToEtale X).map (homOfLE hWU)
  have hkg : k ≫ j = g := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono U.ι).mp
    exact (k ≫ j).w.trans g.w.symm
  have hk (t : V.left) : W.ι (k.left t) = V.hom t :=
    (Scheme.Hom.comp_apply k.left W.ι t).symm.trans
      (congrArg (fun h : V.left ⟶ X => h t) k.w)
  let Z : PUnit.{u + 1} → X.Etale := fun _ => V
  let p : ∀ c : PUnit.{u + 1}, Z c ⟶ (zariskiToEtale X).obj W := fun _ => k
  have hCover : Sieve.ofArrows Z p ∈ X.smallEtaleTopology ((zariskiToEtale X).obj W) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff p).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨t, ht⟩ : ∃ t : V.left, V.hom t = x.val := x.property
    refine Set.mem_iUnion.mpr ⟨PUnit.unit, t, ?_⟩
    apply Subtype.ext
    exact (hk t).trans ht
  have habk : F.obj.map k.op (F.obj.map j.op a) =
      F.obj.map k.op (F.obj.map j.op b) := by
    rw [← F.obj.map_comp_apply, ← F.obj.map_comp_apply, ← op_comp, hkg]
    exact hab
  refine ⟨W, hWU, ⟨v, rfl⟩, ?_⟩
  apply F.isSeparated ((zariskiToEtale X).obj W) (Sieve.ofArrows Z p) hCover
  intro T m hm
  obtain ⟨c, d, rfl⟩ := (Sieve.mem_ofArrows_iff Z p m).mp hm
  change F.obj.map (d ≫ k).op (F.obj.map j.op a) =
    F.obj.map (d ≫ k).op (F.obj.map j.op b)
  rw [op_comp, F.obj.map_comp_apply, F.obj.map_comp_apply, habk]

end EtaleCohomology
