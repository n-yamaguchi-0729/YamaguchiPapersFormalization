/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.FiniteAbelianRepresenter
import EtaleCohomology.Constructible.FiniteEtaleSheaf
import EtaleCohomology.Constructible.FiniteLocallyConstantEquivalence
import SchemeTheory.FiniteEtale.Forget.FiniteLimits
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits

/-!
# Abelian étale sheaves from finite monodromy

The abelian operations constructed on the finite étale representing cover
give an actual sheaf of abelian groups on the small étale site. The underlying
set sheaf is the represented sheaf of that cover. All group operations are
transported through finite-product-preserving functors.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

variable (X : Scheme.{u})

private instance finiteEtaleCartesian : CartesianMonoidalCategory (FiniteEtale X) :=
  .ofHasFiniteProducts

private instance finiteEtaleBraided : BraidedCategory (FiniteEtale X) :=
  .ofCartesianMonoidalCategory

private instance etaleCartesian : CartesianMonoidalCategory X.Etale :=
  .ofHasFiniteProducts

private instance etaleBraided : BraidedCategory X.Etale :=
  .ofCartesianMonoidalCategory

private instance finiteEtaleToEtalePreservesFiniteLimits :
    PreservesFiniteLimits (EtaleCohomology.finiteEtaleToEtale X) := by
  let U := Scheme.Etale.forget X
  have : U.Full := (Scheme.Etale.forgetFullyFaithful X).full
  have : U.Faithful := (Scheme.Etale.forgetFullyFaithful X).faithful
  have : PreservesFiniteLimits (EtaleCohomology.finiteEtaleToEtale X ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits (FiniteEtale.forget X))
  exact preservesFiniteLimits_of_reflects_of_preserves _ U

private instance finiteEtaleToEtaleBraided :
    (EtaleCohomology.finiteEtaleToEtale X).Braided :=
  .ofChosenFiniteProducts _

private def abelianRepresentablePresheaf (G : CommGrp X.Etale) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (Additive (U.unop ⟶ G.X))
  map f := AddCommGrpCat.ofHom (((yonedaGrpObj G.X).map f).hom.toAdditive)
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    exact Category.id_comp f
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro h
    exact Category.assoc g.unop f.unop h

private def abelianRepresentableSheaf (G : CommGrp X.Etale) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  ⟨abelianRepresentablePresheaf X G, by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{u})
    change Presheaf.IsSheaf X.smallEtaleTopology (yoneda.obj G.X)
    exact (X.smallEtaleTopology.yoneda.obj G.X).property⟩

private def abelianRepresentableSheafMap {G H : CommGrp X.Etale} (f : G ⟶ H) :
    abelianRepresentableSheaf X G ⟶ abelianRepresentableSheaf X H where
  hom :=
    { app U := AddCommGrpCat.ofHom (((yonedaGrp.map f.hom).app U).hom.toAdditive)
      naturality U V g := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro h
        exact Category.assoc g.unop h f.hom.hom.hom }

variable {X} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
  (M : Type u) [AddCommGroup M] [Fintype M]
  [DistribMulAction (Aut (FiniteEtale.fiber ξ)) M]
  [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Aut (FiniteEtale.fiber ξ)) M]

private def finiteAbelianGroupOnEtale : CommGrp X.Etale := by
  exact (EtaleCohomology.finiteEtaleToEtale X).mapCommGrp.obj
    (finiteAbelianGroupObject ξ M)

/-- The actual abelian sheaf obtained by descending a finite continuous abelian
representation of the étale fundamental group. -/
def finiteAbelianMonodromySheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  abelianRepresentableSheaf X (finiteAbelianGroupOnEtale ξ M)

/-- Forgetting the abelian structure recovers the sheaf represented by the
finite étale cover constructed from the given representation. -/
def finiteAbelianMonodromySheafUnderlyingIso :
    (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj
        (finiteAbelianMonodromySheaf ξ M) ≅
      (EtaleCohomology.finiteEtaleSheaf X).obj (finiteAbelianCover ξ M) :=
  Iso.refl _

/-- The descended abelian sheaf has a finite locally constant underlying set sheaf. -/
theorem finiteAbelianMonodromySheaf_isFiniteLocallyConstant :
    EtaleCohomology.IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj
        (finiteAbelianMonodromySheaf ξ M)) :=
  (EtaleCohomology.finiteEtaleSheaf_isEtaleFiniteLocallyConstantSet
    (finiteAbelianCover ξ M)).of_iso (finiteAbelianMonodromySheafUnderlyingIso ξ M).symm

/-- The underlying actual abelian stalk is the geometric fiber of its finite
étale representing cover. -/
def finiteAbelianMonodromyFiberIso :
    ↥((Scheme.pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u}) |>.obj
      (finiteAbelianMonodromySheaf ξ M)) ≅
      ↥((FiniteEtale.fiber ξ).obj (finiteAbelianCover ξ M)) := by
  let Φ := Scheme.pointSmallEtale ξ
  exact
    ((Φ.sheafFiberCompIso (forget AddCommGrpCat.{u})).app
        (finiteAbelianMonodromySheaf ξ M)).symm ≪≫
      (EtaleCohomology.finiteEtaleSheafFiberIso ξ).app (finiteAbelianCover ξ M)

/-- The actual geometric stalk of the descended sheaf has the given underlying
finite set, via the represented-sheaf comparison and the Galois counit. -/
def finiteAbelianMonodromyStalkEquiv :
    ↥((Scheme.pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u}) |>.obj
      (finiteAbelianMonodromySheaf ξ M)) ≃ M :=
  (finiteAbelianMonodromyFiberIso ξ M).toEquiv.trans (finiteAbelianCoverFiberEquiv ξ M)

variable (N : Type u) [AddCommGroup N] [Fintype N]
  [DistribMulAction (Aut (FiniteEtale.fiber ξ)) N]
  [TopologicalSpace N] [DiscreteTopology N]
  [ContinuousSMul (Aut (FiniteEtale.fiber ξ)) N]

/-- An equivariant additive map descends to a morphism of the actual abelian
étale sheaves constructed from the two representations. -/
def finiteAbelianMonodromySheafMap (α : M →+ N)
    (hα : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : M), α (g • x) = g • α x) :
    finiteAbelianMonodromySheaf ξ M ⟶ finiteAbelianMonodromySheaf ξ N :=
  abelianRepresentableSheafMap X
    ((EtaleCohomology.finiteEtaleToEtale X).mapCommGrp.map
      (finiteAbelianGroupMap ξ M N α hα))

/-- The underlying morphism of sheaves is induced by the actual map between
the finite étale representing covers. -/
theorem finiteAbelianMonodromySheafMap_underlying (α : M →+ N)
    (hα : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : M), α (g • x) = g • α x) :
    (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).map
        (finiteAbelianMonodromySheafMap ξ M N α hα) =
      (EtaleCohomology.finiteEtaleSheaf X).map
        (finiteAbelianGroupMap ξ M N α hα).hom.hom.hom := rfl

open scoped CategoryTheory.Obj in
/-- Descent to abelian sheaves preserves addition of equivariant maps. -/
theorem finiteAbelianMonodromySheafMap_add (α β : M →+ N)
    (hα : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : M), α (g • x) = g • α x)
    (hβ : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : M), β (g • x) = g • β x) :
    finiteAbelianMonodromySheafMap ξ M N (α + β) (fun g x =>
      (congrArg₂ (· + ·) (hα g x) (hβ g x)).trans (smul_add g (α x) (β x)).symm) =
        finiteAbelianMonodromySheafMap ξ M N α hα +
          finiteAbelianMonodromySheafMap ξ M N β hβ := by
  let : CommGrpObj (finiteAbelianCover ξ N) := finiteAbelianCoverGroup ξ N
  let F := EtaleCohomology.finiteEtaleToEtale X
  let f := (finiteAbelianGroupMap ξ M N α hα).hom.hom.hom
  let g := (finiteAbelianGroupMap ξ M N β hβ).hom.hom.hom
  have h := congrArg F.map (finiteAbelianGroupMap_add ξ M N α β hα hβ)
  have hm := F.map_mul f g
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact (congrArg (s.toMul ≫ ·) (h.trans hm)).trans
    (MonObj.comp_mul s.toMul (F.map f) (F.map g))

/-- Under the actual stalk comparisons, the descended morphism induces the
original additive equivariant map on the given finite groups. -/
theorem finiteAbelianMonodromyStalkEquiv_map (α : M →+ N)
    (hα : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : M), α (g • x) = g • α x)
    (x : (Scheme.pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u}) |>.obj
      (finiteAbelianMonodromySheaf ξ M)) :
    finiteAbelianMonodromyStalkEquiv ξ N
        ((Scheme.pointSmallEtale ξ).sheafFiber.map
          (finiteAbelianMonodromySheafMap ξ M N α hα) x) =
      α (finiteAbelianMonodromyStalkEquiv ξ M x) := by
  let Φ := Scheme.pointSmallEtale ξ
  let E := Φ.sheafFiberCompIso (forget AddCommGrpCat.{u})
  let L := EtaleCohomology.finiteEtaleSheafFiberIso ξ
  let φ := finiteAbelianMonodromySheafMap ξ M N α hα
  let c : finiteAbelianCover ξ M ⟶ finiteAbelianCover ξ N :=
    (finiteAbelianGroupMap ξ M N α hα).hom.hom.hom
  have hE := E.inv.naturality φ
  have hL := L.hom.naturality c
  have hκ : (forget AddCommGrpCat.{u}).map (Φ.sheafFiber.map φ) ≫
        (finiteAbelianMonodromyFiberIso ξ N).hom =
      (finiteAbelianMonodromyFiberIso ξ M).hom ≫
        (forget FintypeCat).map ((FiniteEtale.fiber ξ).map c) := by
    change _ ≫ ((E.app (finiteAbelianMonodromySheaf ξ N)).inv ≫
        (L.app (finiteAbelianCover ξ N)).hom) =
      ((E.app (finiteAbelianMonodromySheaf ξ M)).inv ≫
        (L.app (finiteAbelianCover ξ M)).hom) ≫ _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (L.app (finiteAbelianCover ξ N)).hom) hE).trans
        ((Category.assoc _ _ _).trans
          ((congrArg ((E.app (finiteAbelianMonodromySheaf ξ M)).inv ≫ ·) hL).trans
            (Category.assoc _ _ _).symm)))
  have hv := congrArg (fun f :
    ↥(Φ.sheafFiber (A := AddCommGrpCat.{u}) |>.obj (finiteAbelianMonodromySheaf ξ M)) ⟶
      ↥((FiniteEtale.fiber ξ).obj (finiteAbelianCover ξ N)) => f x) hκ
  exact (congrArg (finiteAbelianCoverFiberEquiv ξ N) hv).trans
    (finiteAbelianGroupMap_fiber ξ M N α hα _)

end EtaleFundamentalGroups.Cohomology
