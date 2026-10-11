/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.Monodromy
import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantSet
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Topology.Category.FinTopCat

/-!
# Global sections and fixed geometric monodromy points

For a finite locally constant étale sheaf on a connected scheme, existence of
a global section is equivalent to existence of a fixed point in its actual
finite monodromy representation. The reverse implication uses fullness of
the proved monodromy equivalence, not a descent hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits EtaleCohomology
open scoped FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

private abbrev unitSheaf : Sheaf X.smallEtaleTopology (Type u) :=
  Sheaf.terminal X.smallEtaleTopology Types.isTerminalPUnit

private abbrev unitLocallyConstant : EtaleFiniteLocallyConstantSetSheaf X :=
  ⟨unitSheaf, (IsEtaleFiniteLocallyConstantSet.constant (X := X) PUnit.{u + 1}).of_iso
    (sheafificationIso (unitSheaf (X := X))).symm⟩

private def unitMonodromyIso :
    ↥(((finiteLocallyConstantSetMonodromy ξ).functor.obj unitLocallyConstant).obj.V) ≅
      PUnit.{u + 1} :=
  (finiteLocallyConstantSetMonodromyStalkIso ξ).app unitLocallyConstant ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso
      (isColimitConstCocone (Scheme.pointSmallEtale ξ).fiber.Elementsᵒᵖ PUnit.{u + 1})

/-- A finite local system has a global section exactly when its geometric
monodromy has a fixed point. Only connectedness and a geometric point are used. -/
theorem nonempty_globalSection_iff_monodromy_fixed
    (F : EtaleFiniteLocallyConstantSetSheaf X) :
    Nonempty ((Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ F.obj.obj) ↔
      ∃ q : ((finiteLocallyConstantSetMonodromy ξ).functor.obj F).obj.V,
        ∀ g : Aut (FiniteEtale.fiber ξ), g • q = q := by
  let M := (finiteLocallyConstantSetMonodromy ξ).functor
  let U := unitLocallyConstant (X := X)
  let e := unitMonodromyIso ξ
  constructor
  · rintro ⟨d⟩
    let f : U ⟶ F := ObjectProperty.homMk (⟨d⟩ : U.obj ⟶ F.obj)
    let q₀ := e.inv PUnit.unit
    refine ⟨(M.map f).hom.hom q₀, ?_⟩
    intro g
    have hq : g • q₀ = q₀ := e.toEquiv.injective (Subsingleton.elim _ _)
    have hf := ConcreteCategory.congr_hom ((M.map f).hom.comm g) q₀
    change (M.map f).hom.hom (g • q₀) = g • (M.map f).hom.hom q₀ at hf
    exact hf.symm.trans (congrArg (fun q => (M.map f).hom.hom q) hq)
  · rintro ⟨q, hq⟩
    let f : M.obj U ⟶ M.obj F := ObjectProperty.homMk
      { hom := FintypeCat.homMk (fun _ => q)
        comm := fun g => by
          apply ConcreteCategory.hom_ext
          intro a
          exact (hq g).symm }
    exact ⟨(M.preimage f).hom.hom⟩

end EtaleFundamentalGroups.Cohomology
