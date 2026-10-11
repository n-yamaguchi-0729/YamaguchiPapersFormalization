/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.SchemeTheory.FiniteEtale.Basic
import Mathlib.CategoryTheory.Galois.Full

/-!
# Sections of a finite etale cover and fixed points of its actual fiber

Fullness of the actual geometric fiber action functor descends a fixed point
to a section. No connectedness of the covering scheme is assumed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

variable {X : Scheme.{u}}
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

local instance : IsFiniteEtale (𝟙 X) := by constructor

private theorem identityFiber_subsingleton :
    Subsingleton ((fiber xi).obj (FiniteEtale.mk (𝟙 X))) := by
  constructor
  intro x y
  apply (fiberObjEquivHom xi _).injective
  apply Over.OverMorphism.ext
  have hx := (fiberObjEquivHom xi (FiniteEtale.mk (𝟙 X)) x).w
  have hy := (fiberObjEquivHom xi (FiniteEtale.mk (𝟙 X)) y).w
  simp only [FiniteEtale.mk_hom, Over.mk_hom] at hx hy
  exact hx.trans hy.symm

variable [ConnectedSpace X]

/-- A finite etale cover admits an actual section exactly when its actual
geometric fiber has a fixed point under the fundamental group. -/
theorem exists_section_iff_exists_fiber_fixed (W : FiniteEtale X) :
    (∃ s : X ⟶ W.left, s ≫ W.hom = 𝟙 X) ↔
      ∃ q : (fiber xi).obj W, ∀ g : Aut (fiber xi), g • q = q := by
  let E : FiniteEtale X := FiniteEtale.mk (𝟙 X)
  let H := functorToAction (fiber xi)
  constructor
  · rintro ⟨s, hs⟩
    let m : E ⟶ W := MorphismProperty.Over.homMk s hs
    let e : (fiber xi).obj E := (fiberObjEquivHom xi E).symm
      (Over.homMk xi (Category.comp_id xi))
    have : Subsingleton ((fiber xi).obj E) := identityFiber_subsingleton xi
    refine ⟨(fiber xi).map m e, ?_⟩
    intro g
    have hcomm := ConcreteCategory.congr_hom (g.hom.naturality m) e
    change g • (fiber xi).map m e = (fiber xi).map m (g • e) at hcomm
    exact hcomm.trans (congrArg ((fiber xi).map m) (Subsingleton.elim _ _))
  · rintro ⟨q, hq⟩
    let m : H.obj E ⟶ H.obj W := {
      hom := FintypeCat.homMk (fun _ => q)
      comm := fun g => by
        apply ConcreteCategory.hom_ext
        intro a
        exact (hq g).symm }
    let s : E ⟶ W := H.preimage m
    exact ⟨s.left, s.w⟩

end AlgebraicGeometry.FiniteEtale
