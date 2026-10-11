/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.GaloisCategory
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Algebra.Category.Grp.Limits

/-!+# Representing finite abelian monodromy

A finite abelian group with continuous action of the actual étale fundamental
group determines a finite étale cover. Its group structure is constructed from
the represented presheaf of equivariant functions, using the full Galois
equivalence. No descent of the group operations is assumed as an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory Opposite
open scoped FintypeCatDiscrete CategoryTheory.MonObj

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
  (M : Type u) [AddCommGroup M] [Fintype M]
  [DistribMulAction (Aut (FiniteEtale.fiber ξ)) M]
  [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Aut (FiniteEtale.fiber ξ)) M]

/-- The finite continuous set action underlying a finite abelian representation. -/
def finiteAbelianSetAction : ContAction FintypeCat.{u} (Aut (FiniteEtale.fiber ξ)) :=
  ⟨Action.FintypeCat.ofMulAction _ (FintypeCat.of M), ⟨by
    change @Continuous (Aut (FiniteEtale.fiber ξ) × M) M
      (@instTopologicalSpaceProd _ _ _ ⊥) ⊥ (fun p => p.1 • p.2)
    rw [← DiscreteTopology.eq_bot (t := (inferInstance : TopologicalSpace M))]
    exact continuous_smul⟩⟩

/-- Equivariant functions on geometric fibers form a presheaf of abelian groups. -/
def finiteAbelianEquivariantPresheaf : (FiniteEtale X)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj Y := CommGrpCat.of
    (Multiplicative (MulActionHom (id : Aut (FiniteEtale.fiber ξ) → _)
      ((FiniteEtale.fiber ξ).obj Y.unop) M))
  map {Y Z} f := by
    let f' : MulActionHom (id : Aut (FiniteEtale.fiber ξ) → _)
        ((FiniteEtale.fiber ξ).obj Y.unop) M →+
        MulActionHom (id : Aut (FiniteEtale.fiber ξ) → _)
          ((FiniteEtale.fiber ξ).obj Z.unop) M :=
      { toFun := fun a =>
          { toFun := fun x => a ((FiniteEtale.fiber ξ).map f.unop x)
            map_smul' := fun g x => by
              exact (congrArg a
                (mulAction_naturality (FiniteEtale.fiber ξ) g f.unop x).symm).trans
                  (a.map_smul' g _) }
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact CommGrpCat.ofHom f'.toMultiplicative
  map_id Y := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply MulActionHom.ext
    intro x
    exact congrArg a (congrArg (fun k => k x) ((FiniteEtale.fiber ξ).map_id Y.unop))
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply MulActionHom.ext
    intro x
    exact congrArg a
      (congrArg (fun k => k x) ((FiniteEtale.fiber ξ).map_comp g.unop f.unop))

private def equivariantHomEquiv (Y : FiniteEtale X) :
    ((functorToContAction (FiniteEtale.fiber ξ)).obj Y ⟶ finiteAbelianSetAction ξ M) ≃
      MulActionHom (id : Aut (FiniteEtale.fiber ξ) → _)
        ((FiniteEtale.fiber ξ).obj Y) M where
  toFun f :=
    { toFun := f.hom.hom
      map_smul' := fun g x => congrArg (fun k => k x) (f.hom.comm g) }
  invFun f := ObjectProperty.homMk
    { hom := FintypeCat.homMk f
      comm := fun g => by
        apply ConcreteCategory.hom_ext
        intro x
        exact f.map_smul' g x }
  left_inv f := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    rfl
  right_inv f := by
    apply MulActionHom.ext
    intro x
    rfl

/-- The actual finite étale cover supplied by the Galois equivalence. -/
def finiteAbelianCover : FiniteEtale X :=
  (functorToContAction (FiniteEtale.fiber ξ)).asEquivalence.inverse.obj
    (finiteAbelianSetAction ξ M)

/-- The Galois counit identifies the actual geometric fiber of the constructed
cover with the original finite representation. -/
def finiteAbelianCoverFiberEquiv : (FiniteEtale.fiber ξ).obj (finiteAbelianCover ξ M) ≃ M :=
  (((forget₂ (ContAction FintypeCat.{u} (Aut (FiniteEtale.fiber ξ))) FintypeCat) ⋙
      forget FintypeCat).mapIso
    ((functorToContAction (FiniteEtale.fiber ξ)).asEquivalence.counitIso.app
      (finiteAbelianSetAction ξ M))).toEquiv

/-- The equivariant-function presheaf is represented by the constructed cover. -/
def finiteAbelianRepresentableBy :
    (finiteAbelianEquivariantPresheaf ξ M ⋙ forget CommGrpCat).RepresentableBy
      (finiteAbelianCover ξ M) := by
  let F := functorToContAction (FiniteEtale.fiber ξ)
  let e := F.asEquivalence.counitIso.app (finiteAbelianSetAction ξ M)
  exact
    { homEquiv := F.asEquivalence.fullyFaithfulFunctor.homEquiv.trans
        ((Iso.homCongr (Iso.refl _) e).trans (equivariantHomEquiv ξ M _))
      homEquiv_comp := fun f g => by
        apply MulActionHom.ext
        intro x
        change (F.map (f ≫ g) ≫ e.hom).hom.hom x =
          (F.map g ≫ e.hom).hom.hom ((FiniteEtale.fiber ξ).map f x)
        rw [F.map_comp]
        rfl }

/-- The abelian group operations on a finite monodromy representation descend
to its finite étale cover by representability. -/
abbrev finiteAbelianCoverGroup :
    let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
    let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
    CommGrpObj (finiteAbelianCover ξ M) := by
  let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
  let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
  exact CommGrpObj.ofRepresentableBy _ (finiteAbelianEquivariantPresheaf ξ M)
    (finiteAbelianRepresentableBy ξ M)

/-- The descended finite étale cover with its constructed abelian group structure. -/
abbrev finiteAbelianGroupObject :
    let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
    let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
    CommGrp (FiniteEtale X) := by
  let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
  let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
  let h := finiteAbelianCoverGroup ξ M
  exact { X := finiteAbelianCover ξ M, grp := h.toGrpObj, comm := h.toIsCommMonObj }

variable (N : Type u) [AddCommGroup N] [Fintype N]
  [DistribMulAction (Aut (FiniteEtale.fiber ξ)) N]
  [TopologicalSpace N] [DiscreteTopology N]
  [ContinuousSMul (Aut (FiniteEtale.fiber ξ)) N]

/-- An equivariant additive map acts pointwise on the represented presheaves. -/
def finiteAbelianEquivariantMap (α : M →+ N)
    (hα : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : M), α (g • x) = g • α x) :
    finiteAbelianEquivariantPresheaf ξ M ⟶ finiteAbelianEquivariantPresheaf ξ N where
  app Y := by
    let f : MulActionHom (id : Aut (FiniteEtale.fiber ξ) → _)
        ((FiniteEtale.fiber ξ).obj Y.unop) M →+
        MulActionHom (id : Aut (FiniteEtale.fiber ξ) → _)
          ((FiniteEtale.fiber ξ).obj Y.unop) N :=
      { toFun := fun a =>
          { toFun := fun x => α (a x)
            map_smul' := fun g x => (congrArg α (a.map_smul' g x)).trans (hα g (a x)) }
        map_zero' := MulActionHom.ext fun _ => α.map_zero
        map_add' := fun a b => MulActionHom.ext fun x => α.map_add (a x) (b x) }
    exact CommGrpCat.ofHom f.toMultiplicative
  naturality Y Z f := rfl

/-- Equivariant additive maps descend to actual homomorphisms of the represented
finite étale abelian groups. -/
def finiteAbelianGroupMap (α : M →+ N)
    (hα : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : M), α (g • x) = g • α x) :
    let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
    let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
    finiteAbelianGroupObject ξ M ⟶ finiteAbelianGroupObject ξ N := by
  let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
  let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
  let F₁ := finiteAbelianEquivariantPresheaf ξ M ⋙ forget₂ CommGrpCat GrpCat
  let F₂ := finiteAbelianEquivariantPresheaf ξ N ⋙ forget₂ CommGrpCat GrpCat
  let e₁ : yonedaGrp.obj (finiteAbelianGroupObject ξ M).toGrp ≅ F₁ :=
    yonedaGrpObjIsoOfRepresentableBy _ F₁ (finiteAbelianRepresentableBy ξ M)
  let e₂ : yonedaGrp.obj (finiteAbelianGroupObject ξ N).toGrp ≅ F₂ :=
    yonedaGrpObjIsoOfRepresentableBy _ F₂ (finiteAbelianRepresentableBy ξ N)
  exact InducedCategory.homMk (yonedaGrpFullyFaithful.preimage
    (e₁.hom ≫ Functor.whiskerRight (finiteAbelianEquivariantMap ξ M N α hα)
      (forget₂ CommGrpCat GrpCat) ≫ e₂.inv))

/-- The descended map acts on every represented section by the original
equivariant additive map. -/
theorem finiteAbelianGroupMap_representable (α : M →+ N)
    (hα : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : M), α (g • x) = g • α x)
    (Y : FiniteEtale X) (f : Y ⟶ finiteAbelianCover ξ M) :
    let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
    let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
    (finiteAbelianRepresentableBy ξ N).homEquiv
        (f ≫ (finiteAbelianGroupMap ξ M N α hα).hom.hom.hom) =
      (finiteAbelianEquivariantMap ξ M N α hα).app (op Y)
        ((finiteAbelianRepresentableBy ξ M).homEquiv f) := by
  let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
  let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
  let G₁ := finiteAbelianGroupObject ξ M
  let G₂ := finiteAbelianGroupObject ξ N
  let F₁ := finiteAbelianEquivariantPresheaf ξ M ⋙ forget₂ CommGrpCat GrpCat
  let F₂ := finiteAbelianEquivariantPresheaf ξ N ⋙ forget₂ CommGrpCat GrpCat
  let e₁ : yonedaGrp.obj G₁.toGrp ≅ F₁ :=
    yonedaGrpObjIsoOfRepresentableBy _ F₁ (finiteAbelianRepresentableBy ξ M)
  let e₂ : yonedaGrp.obj G₂.toGrp ≅ F₂ :=
    yonedaGrpObjIsoOfRepresentableBy _ F₂ (finiteAbelianRepresentableBy ξ N)
  let τ := e₁.hom ≫ Functor.whiskerRight (finiteAbelianEquivariantMap ξ M N α hα)
    (forget₂ CommGrpCat GrpCat) ≫ e₂.inv
  have h := congrArg (fun t : yonedaGrp.obj G₁.toGrp ⟶ yonedaGrp.obj G₂.toGrp =>
    t.app (op Y) f) (yonedaGrpFullyFaithful.map_preimage τ)
  change f ≫ (finiteAbelianGroupMap ξ M N α hα).hom.hom.hom =
    (finiteAbelianRepresentableBy ξ N).homEquiv.symm
      ((finiteAbelianEquivariantMap ξ M N α hα).app (op Y)
        ((finiteAbelianRepresentableBy ξ M).homEquiv f)) at h
  exact (congrArg (finiteAbelianRepresentableBy ξ N).homEquiv h).trans
    ((finiteAbelianRepresentableBy ξ N).homEquiv.apply_symm_apply _)

/-- The map on geometric fibers of descended finite étale groups is the
original additive equivariant map, under the actual Galois counit. -/
theorem finiteAbelianGroupMap_fiber (α : M →+ N)
    (hα : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : M), α (g • x) = g • α x)
    (x : (FiniteEtale.fiber ξ).obj (finiteAbelianCover ξ M)) :
    let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
    let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
    finiteAbelianCoverFiberEquiv ξ N
        ((FiniteEtale.fiber ξ).map (finiteAbelianGroupMap ξ M N α hα).hom.hom.hom x) =
      α (finiteAbelianCoverFiberEquiv ξ M x) := by
  let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
  let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
  have h := congrArg (fun f : MulActionHom (id : Aut (FiniteEtale.fiber ξ) → _)
    ((FiniteEtale.fiber ξ).obj (finiteAbelianCover ξ M)) N => f x)
      (finiteAbelianGroupMap_representable ξ M N α hα _ (𝟙 _))
  change finiteAbelianCoverFiberEquiv ξ N
      ((FiniteEtale.fiber ξ).map
        (𝟙 _ ≫ (finiteAbelianGroupMap ξ M N α hα).hom.hom.hom) x) =
    α (finiteAbelianCoverFiberEquiv ξ M ((FiniteEtale.fiber ξ).map (𝟙 _) x)) at h
  rw [Category.id_comp] at h
  have hid : (FiniteEtale.fiber ξ).map (𝟙 (finiteAbelianCover ξ M)) x = x :=
    congrArg (fun f : (FiniteEtale.fiber ξ).obj (finiteAbelianCover ξ M) ⟶
      (FiniteEtale.fiber ξ).obj (finiteAbelianCover ξ M) => f x)
        ((FiniteEtale.fiber ξ).map_id (finiteAbelianCover ξ M))
  exact h.trans (congrArg (fun z => α (finiteAbelianCoverFiberEquiv ξ M z)) hid)

/-- Descent respects the pointwise sum of equivariant additive maps. On the
underlying finite étale covers this is the internal abelian group product. -/
theorem finiteAbelianGroupMap_add (α β : M →+ N)
    (hα : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : M), α (g • x) = g • α x)
    (hβ : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : M), β (g • x) = g • β x) :
    let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
    let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
    let : CommGrpObj (finiteAbelianCover ξ N) := finiteAbelianCoverGroup ξ N
    (finiteAbelianGroupMap ξ M N (α + β) (fun g x =>
      (congrArg₂ (· + ·) (hα g x) (hβ g x)).trans (smul_add g (α x) (β x)).symm)).hom.hom.hom =
        (finiteAbelianGroupMap ξ M N α hα).hom.hom.hom *
          (finiteAbelianGroupMap ξ M N β hβ).hom.hom.hom := by
  let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
  let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
  let : CommGrpObj (finiteAbelianCover ξ N) := finiteAbelianCoverGroup ξ N
  let hsum := fun g x =>
    (congrArg₂ (· + ·) (hα g x) (hβ g x)).trans (smul_add g (α x) (β x)).symm
  let r := finiteAbelianRepresentableBy ξ N
  let e := yonedaGrpObjIsoOfRepresentableBy _
    (finiteAbelianEquivariantPresheaf ξ N ⋙ forget₂ CommGrpCat GrpCat) r
  have hmap (δ : M →+ N)
      (hδ : ∀ (g : Aut (FiniteEtale.fiber ξ)) (x : M), δ (g • x) = g • δ x) :
      r.homEquiv (finiteAbelianGroupMap ξ M N δ hδ).hom.hom.hom =
        (finiteAbelianEquivariantMap ξ M N δ hδ).app (op (finiteAbelianCover ξ M))
          ((finiteAbelianRepresentableBy ξ M).homEquiv (𝟙 _)) := by
    have h := finiteAbelianGroupMap_representable ξ M N δ hδ _ (𝟙 _)
    rw [Category.id_comp] at h
    exact h
  apply r.homEquiv.injective
  change r.homEquiv (finiteAbelianGroupMap ξ M N (α + β) hsum).hom.hom.hom = _
  rw [hmap]
  have hm := (e.hom.app (op (finiteAbelianCover ξ M))).hom.map_mul
    (finiteAbelianGroupMap ξ M N α hα).hom.hom.hom
    (finiteAbelianGroupMap ξ M N β hβ).hom.hom.hom
  change r.homEquiv (_ * _) = r.homEquiv _ * r.homEquiv _ at hm
  exact (congrArg₂ (· * ·) (hmap α hα) (hmap β hβ)).symm.trans hm.symm

end EtaleFundamentalGroups.Cohomology
