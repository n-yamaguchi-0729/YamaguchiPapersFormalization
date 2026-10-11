/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.FiniteAbelianStalk
import EtaleFundamentalGroups.Cohomology.FiniteLocallyConstantHom
import EtaleFundamentalGroups.Cohomology.FiniteLocallyConstantExact

/-!
# Descent of exact sequences of finite abelian representations

The finite étale representing covers and their abelian sheaves carry the
original maps on actual geometric stalks. Consequently an exact sequence of
finite continuous representations descends to an exact sequence of actual
étale sheaves, with no extra descent or comparison assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
  (M N P : Type u) [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Fintype M] [Fintype N] [Fintype P]
  [DistribMulAction (Aut (FiniteEtale.fiber ξ)) M]
  [DistribMulAction (Aut (FiniteEtale.fiber ξ)) N]
  [DistribMulAction (Aut (FiniteEtale.fiber ξ)) P]
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [DiscreteTopology M] [DiscreteTopology N] [DiscreteTopology P]
  [ContinuousSMul (Aut (FiniteEtale.fiber ξ)) M]
  [ContinuousSMul (Aut (FiniteEtale.fiber ξ)) N]
  [ContinuousSMul (Aut (FiniteEtale.fiber ξ)) P]
  (α : M →+ N) (β : N →+ P)
  (hα : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : M), α (g • x) = g • α x)
  (hβ : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : N), β (g • x) = g • β x)
  (w : (AddCommGrpCat.ofHom α) ≫ AddCommGrpCat.ofHom β = 0)

include w in
/-- A zero composite of equivariant homomorphisms remains zero on the actual
descended abelian sheaves. -/
theorem finiteAbelianMonodromySheafMap_comp_zero :
    finiteAbelianMonodromySheafMap ξ M N α hα ≫
      finiteAbelianMonodromySheafMap ξ N P β hβ = 0 := by
  apply hom_ext_finiteLocallyConstant_abelianStalk ξ _ _
    (finiteAbelianMonodromySheaf_isFiniteLocallyConstant ξ M)
    (finiteAbelianMonodromySheaf_isFiniteLocallyConstant ξ P)
  rw [Functor.map_comp, Functor.map_zero]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  apply (finiteAbelianMonodromyStalkAddEquiv ξ P).injective
  exact (finiteAbelianMonodromyStalkEquiv_map ξ N P β hβ _).trans
    ((congrArg β (finiteAbelianMonodromyStalkEquiv_map ξ M N α hα x)).trans
      ((ConcreteCategory.congr_hom w (finiteAbelianMonodromyStalkEquiv ξ M x)).trans
        (map_zero (finiteAbelianMonodromyStalkAddEquiv ξ P)).symm))

/-- The actual short complex obtained by descending finite abelian
representations and their two equivariant maps. -/
def finiteAbelianMonodromyComplex :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  ShortComplex.mk (finiteAbelianMonodromySheafMap ξ M N α hα)
    (finiteAbelianMonodromySheafMap ξ N P β hβ)
    (finiteAbelianMonodromySheafMap_comp_zero ξ M N P α β hα hβ w)

/-- Its geometric stalk is the original short complex of finite abelian groups. -/
def finiteAbelianMonodromyComplex_stalkIso :
    (finiteAbelianMonodromyComplex ξ M N P α β hα hβ w).map
        (Scheme.pointSmallEtale ξ).sheafFiber ≅
      ShortComplex.mk (AddCommGrpCat.ofHom α) (AddCommGrpCat.ofHom β) w := by
  refine ShortComplex.isoMk
    (finiteAbelianMonodromyStalkAddEquiv ξ M).toAddCommGrpIso
    (finiteAbelianMonodromyStalkAddEquiv ξ N).toAddCommGrpIso
    (finiteAbelianMonodromyStalkAddEquiv ξ P).toAddCommGrpIso ?_ ?_
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact (finiteAbelianMonodromyStalkEquiv_map ξ M N α hα x).symm
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact (finiteAbelianMonodromyStalkEquiv_map ξ N P β hβ x).symm

/-- Descent of a short exact sequence of finite continuous abelian
representations is short exact in the ambient category of étale abelian sheaves. -/
theorem finiteAbelianMonodromyComplex_shortExact
    (h : (ShortComplex.mk (AddCommGrpCat.ofHom α) (AddCommGrpCat.ofHom β) w).ShortExact) :
    (finiteAbelianMonodromyComplex ξ M N P α β hα hβ w).ShortExact :=
  shortExact_of_finiteLocallyConstant_abelianStalk ξ _
    (finiteAbelianMonodromySheaf_isFiniteLocallyConstant ξ M)
    (finiteAbelianMonodromySheaf_isFiniteLocallyConstant ξ N)
    (finiteAbelianMonodromySheaf_isFiniteLocallyConstant ξ P)
    (ShortComplex.shortExact_of_iso
      (finiteAbelianMonodromyComplex_stalkIso ξ M N P α β hα hβ w).symm h)

end EtaleFundamentalGroups.Cohomology
