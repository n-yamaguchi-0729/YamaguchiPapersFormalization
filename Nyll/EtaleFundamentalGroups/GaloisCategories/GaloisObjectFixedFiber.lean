/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient

/-!
# The kernel of a Galois quotient fixes its entire fiber

The point stabilizer of a Galois object fixes every point because its deck
transformations act transitively and commute with the fundamental group.

The proof below was extracted unchanged from
`EtaleFundamentalGroups.FiniteEtale.TrivialBaseChangeAlgebra`.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

/-- The kernel of a pointed Galois quotient fixes the entire fiber, not just
the chosen point. Transitivity of cover automorphisms supplies every other point. -/
theorem fiber_fixed_of_galoisObjectQuotient_eq_one
    {C : Type*} [Category C] [GaloisCategory C]
    (F : C ⥤ FintypeCat) [FiberFunctor F]
    (W : C) [IsGalois W] (w₀ : F.obj W) (g : Aut F)
    (hg : galoisObjectQuotientMonoidHom F (Aut F) W w₀ g = 1)
    (w : F.obj W) : g • w = w := by
  have hg₀ : g • w₀ = w₀ := by
    have hm := MonoidHom.mem_ker.mpr hg
    rw [galoisObjectQuotientMonoidHom_ker] at hm
    exact hm
  let σ : Aut W := (evaluationEquivOfIsGalois F W w₀).symm w
  have hσ : F.map σ.hom w₀ = w := evaluationEquivOfIsGalois_symm_fiber F W w₀ w
  calc
    g • w = g • F.map σ.hom w₀ := congrArg (fun x => g • x) hσ.symm
    _ = F.map σ.hom (g • w₀) := mulAction_naturality F g σ.hom w₀
    _ = F.map σ.hom w₀ := congrArg (F.map σ.hom) hg₀
    _ = w := hσ

end CategoryTheory.PreGaloisCategory
