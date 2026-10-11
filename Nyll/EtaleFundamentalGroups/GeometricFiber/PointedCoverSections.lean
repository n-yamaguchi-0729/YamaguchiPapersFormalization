/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Mathlib.CategoryTheory.Galois.Full

/-!
# Pointed sections of actual finite étale covers

A monodromy-fixed geometric point of a finite étale cover gives an actual
section with that value. Connectedness makes this section unique.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

/-- A fixed point of the actual geometric fiber determines a unique section
of the original finite étale cover with the specified geometric value. -/
theorem existsUnique_section_of_fixed_point
    (W : FiniteEtale X) (z : Spec (.of Ω) ⟶ W.left) (hz : z ≫ W.hom = xi)
    (hfixed : ∀ g : Aut (fiber xi), g •
      ((fiberObjEquivHom xi W).symm (Over.homMk z hz)) =
        (fiberObjEquivHom xi W).symm (Over.homMk z hz)) :
    ∃! s : X ⟶ W.left, s ≫ W.hom = 𝟙 X ∧ xi ≫ s = z := by
  have : IsFiniteEtale (𝟙 X) := {}
  let T : FiniteEtale X := FiniteEtale.mk (𝟙 X)
  have : ConnectedSpace T.left := inferInstanceAs (ConnectedSpace X)
  have : IsConnected T := isConnected_of_connectedSpace_left T
  let F := fiber xi
  let x : F.obj T := (fiberObjEquivHom xi T).symm
    (Over.homMk xi (Category.comp_id xi))
  let w : F.obj W := (fiberObjEquivHom xi W).symm (Over.homMk z hz)
  have hx : fiberObjEquivHom xi T x = Over.homMk xi (Category.comp_id xi) :=
    (fiberObjEquivHom xi T).apply_symm_apply _
  have hw : fiberObjEquivHom xi W w = Over.homMk z hz :=
    (fiberObjEquivHom xi W).apply_symm_apply _
  let M := functorToAction F
  let q : M.obj T ⟶ M.obj W :=
    { hom := FintypeCat.homMk (fun _ => w)
      comm := fun g => by
        apply ConcreteCategory.hom_ext
        intro a
        exact (hfixed g).symm }
  let s : T ⟶ W := M.preimage q
  have hs : F.map s x = w := by
    have hh := congrArg (fun h : M.obj T ⟶ M.obj W => h.hom x) (M.map_preimage q)
    exact hh
  have hpoint : xi ≫ s.left = z := by
    have hh := fiberObjEquivHom_naturality xi s x
    rw [hs, hx, hw] at hh
    exact congrArg (fun h : Over.mk xi ⟶ W.toComma => h.left) hh
  refine ⟨s.left, ⟨s.w, hpoint⟩, ?_⟩
  intro t ht
  let t' : T ⟶ W := MorphismProperty.Over.homMk t ht.1
  have htw : F.map t' x = w := by
    apply (fiberObjEquivHom xi W).injective
    have hh := fiberObjEquivHom_naturality xi t' x
    rw [hx] at hh
    exact hh.symm.trans ((Over.OverMorphism.ext ht.2).trans hw.symm)
  have heq : t' = s :=
    evaluation_injective_of_isConnected F T W x (htw.trans hs.symm)
  exact congrArg (fun h : T ⟶ W => h.left) heq

end AlgebraicGeometry.FiniteEtale
