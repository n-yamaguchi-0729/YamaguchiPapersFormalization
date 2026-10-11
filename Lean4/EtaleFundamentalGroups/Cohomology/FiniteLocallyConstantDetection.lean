/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.Monodromy
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Detecting finite local-system isomorphisms at a geometric point

On a connected scheme, bijectivity at one geometric stalk detects an
isomorphism of finite locally constant sheaves. This is deduced from the
actual monodromy equivalence and its comparison with the geometric stalk.
The abelian version forgets the group structure only to detect the inverse.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology
open scoped FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- One geometric stalk detects isomorphisms of finite locally constant
set sheaves on a connected scheme. -/
theorem isIso_of_bijective_finiteLocallyConstant_stalk
    {F G : EtaleFiniteLocallyConstantSetSheaf X} (f : F ⟶ G)
    (hf : Function.Bijective ((Scheme.pointSmallEtale ξ).sheafFiber.map f.hom)) :
    IsIso f := by
  let M := (finiteLocallyConstantSetMonodromy ξ).functor
  let e := finiteLocallyConstantSetMonodromyStalkIso ξ
  have hstalk : IsIso ((Scheme.pointSmallEtale ξ).sheafFiber.map f.hom) :=
    (CategoryTheory.isIso_iff_bijective _).mpr hf
  have hset : IsIso ((M.map f).hom.hom) := by
    have h : IsIso ((forget FintypeCat).map (M.map f).hom.hom) :=
      (NatIso.isIso_map_iff e f).mpr hstalk
    exact isIso_of_reflects_iso ((M.map f).hom.hom) (forget FintypeCat)
  have haction : IsIso (M.map f).hom := Action.isIso_of_hom_isIso (M.map f).hom
  let I := ObjectProperty.ι (Action.isContinuous FintypeCat (Aut (FiniteEtale.fiber ξ)))
  have hi : IsIso (I.map (M.map f)) := haction
  have hcontinuous : IsIso (M.map f) := isIso_of_reflects_iso (M.map f) I
  exact isIso_of_reflects_iso f M

/-- A map of abelian sheaves whose underlying finite local systems have a
bijective geometric stalk is an isomorphism of abelian sheaves. -/
theorem isIso_of_bijective_finiteLocallyConstant_abelianStalk
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (f : F ⟶ G)
    (hF : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F))
    (hG : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj G))
    (hf : Function.Bijective ((Scheme.pointSmallEtale ξ).sheafFiber.map f)) :
    IsIso f := by
  let U := sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})
  let f' : (⟨U.obj F, hF⟩ : EtaleFiniteLocallyConstantSetSheaf X) ⟶ ⟨U.obj G, hG⟩ :=
    ObjectProperty.homMk (U.map f)
  let e := (Scheme.pointSmallEtale ξ).sheafFiberCompIso (forget AddCommGrpCat.{u})
  have hab : IsIso ((Scheme.pointSmallEtale ξ).sheafFiber.map f) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hf
  have hforget : IsIso (((Scheme.pointSmallEtale ξ).sheafFiber ⋙
      forget AddCommGrpCat.{u}).map f) :=
    (forget AddCommGrpCat.{u}).map_isIso ((Scheme.pointSmallEtale ξ).sheafFiber.map f)
  have hset : IsIso ((Scheme.pointSmallEtale ξ).sheafFiber.map (U.map f)) :=
    (NatIso.isIso_map_iff e f).mpr hforget
  have hlocal : IsIso f' := isIso_of_bijective_finiteLocallyConstant_stalk ξ f'
    ((CategoryTheory.isIso_iff_bijective _).mp hset)
  have hu : IsIso (U.map f) := (ObjectProperty.ι _).map_isIso f'
  have happ (V : X.Etaleᵒᵖ) : IsIso (f.hom.app V) := by
    have hcomp : IsIso ((U.map f).hom.app V) := inferInstance
    have : IsIso ((forget AddCommGrpCat.{u}).map (f.hom.app V)) := hcomp
    exact isIso_of_reflects_iso (f.hom.app V) (forget AddCommGrpCat.{u})
  have hnat : IsIso f.hom := NatIso.isIso_of_isIso_app f.hom
  have : IsIso ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).map f) := hnat
  exact isIso_of_reflects_iso f (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u})

end EtaleFundamentalGroups.Cohomology
