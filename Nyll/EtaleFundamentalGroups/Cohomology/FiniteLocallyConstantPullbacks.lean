/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.Monodromy
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteLocallyConstantDetection
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.PreservesLimits

/-!
# Pullbacks of finite local systems detected on a geometric stalk

The finite étale realization preserves finite limits, and the Galois fiber
functor reflects them. Hence a square of finite locally constant abelian
sheaves is cartesian if its actual geometric stalk square is cartesian.
This detects kernels without assuming descent of exactness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits EtaleCohomology
open scoped FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

private theorem finiteEtaleSheaf_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (finiteEtaleSheaf X) := by
  let U := Scheme.Etale.forget X
  have : U.Full := (Scheme.Etale.forgetFullyFaithful X).full
  have : U.Faithful := (Scheme.Etale.forgetFullyFaithful X).faithful
  have : PreservesFiniteLimits (finiteEtaleToEtale X ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits (FiniteEtale.forget X))
  have : PreservesFiniteLimits (finiteEtaleToEtale X) :=
    preservesFiniteLimits_of_reflects_of_preserves _ U
  exact inferInstanceAs
    (PreservesFiniteLimits (finiteEtaleToEtale X ⋙ X.smallEtaleTopology.yoneda))

private theorem localSystemInclusion_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X))) := by
  let e := finiteEtaleEquivFiniteLocallyConstantSetSheaf X
  let I := ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X))
  have : PreservesFiniteLimits (finiteEtaleSheaf X) :=
    finiteEtaleSheaf_preservesFiniteLimits X
  let h : e.inverse ⋙ finiteEtaleSheaf X ≅ I :=
    (Functor.associator e.inverse e.functor I).symm ≪≫
      Functor.isoWhiskerRight e.counitIso I ≪≫ I.leftUnitor
  exact preservesFiniteLimits_of_natIso h

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

private theorem localSystemStalk_reflectsPullbacks :
    ReflectsLimitsOfShape WalkingCospan
      (ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X)) ⋙
        (Scheme.pointSmallEtale ξ).sheafFiber) := by
  let e := finiteEtaleEquivFiniteLocallyConstantSetSheaf X
  have : ReflectsLimitsOfShape WalkingCospan (FiniteEtale.fiber ξ) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  let h : (e.inverse ⋙ FiniteEtale.fiber ξ) ⋙ forget FintypeCat ≅
      ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X)) ⋙
        (Scheme.pointSmallEtale ξ).sheafFiber :=
    finiteLocallyConstantSetMonodromyStalkIso ξ
  exact reflectsLimitsOfShape_of_natIso h

/-- A square of finite locally constant abelian sheaves is a pullback if
its square at one geometric point is a pullback of actual abelian stalks. -/
theorem isPullback_of_finiteLocallyConstant_abelianStalk
    {P F G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (a : P ⟶ F) (b : P ⟶ G) (f : F ⟶ H) (g : G ⟶ H)
    (w : a ≫ f = b ≫ g)
    (hP : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj P))
    (hF : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F))
    (hG : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj G))
    (hH : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj H))
    (hp : IsPullback ((Scheme.pointSmallEtale ξ).sheafFiber.map a)
      ((Scheme.pointSmallEtale ξ).sheafFiber.map b)
      ((Scheme.pointSmallEtale ξ).sheafFiber.map f)
      ((Scheme.pointSmallEtale ξ).sheafFiber.map g)) :
    IsPullback a b f g := by
  let U := sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})
  let I := ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X))
  let Φ := (Scheme.pointSmallEtale ξ).sheafFiber (A := Type u)
  let a' : (⟨U.obj P, hP⟩ : EtaleFiniteLocallyConstantSetSheaf X) ⟶ ⟨U.obj F, hF⟩ :=
    ObjectProperty.homMk (U.map a)
  let b' : (⟨U.obj P, hP⟩ : EtaleFiniteLocallyConstantSetSheaf X) ⟶ ⟨U.obj G, hG⟩ :=
    ObjectProperty.homMk (U.map b)
  let f' : (⟨U.obj F, hF⟩ : EtaleFiniteLocallyConstantSetSheaf X) ⟶ ⟨U.obj H, hH⟩ :=
    ObjectProperty.homMk (U.map f)
  let g' : (⟨U.obj G, hG⟩ : EtaleFiniteLocallyConstantSetSheaf X) ⟶ ⟨U.obj H, hH⟩ :=
    ObjectProperty.homMk (U.map g)
  let e := (Scheme.pointSmallEtale ξ).sheafFiberCompIso (forget AddCommGrpCat.{u})
  have hs : IsPullback ((I ⋙ Φ).map a') ((I ⋙ Φ).map b')
      ((I ⋙ Φ).map f') ((I ⋙ Φ).map g') :=
    (hp.map (forget AddCommGrpCat.{u})).of_iso
      (e.app P).symm (e.app F).symm (e.app G).symm (e.app H).symm
      (e.inv.naturality a) (e.inv.naturality b) (e.inv.naturality f) (e.inv.naturality g)
  have : ReflectsLimitsOfShape WalkingCospan (I ⋙ Φ) :=
    localSystemStalk_reflectsPullbacks ξ
  have hw : a' ≫ f' = b' ≫ g' := by
    apply ObjectProperty.hom_ext
    exact (U.map_comp a f).symm.trans ((congrArg U.map w).trans (U.map_comp b g))
  have hl := hs.of_map (I ⋙ Φ) hw
  have : PreservesFiniteLimits I := localSystemInclusion_preservesFiniteLimits X
  let Q := sheafToPresheaf X.smallEtaleTopology (Type u)
  have : PreservesFiniteLimits (U ⋙ Q) :=
    inferInstanceAs (PreservesFiniteLimits
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
        (Functor.whiskeringRight X.Etaleᵒᵖ AddCommGrpCat.{u} (Type u)).obj
          (forget AddCommGrpCat.{u})))
  have : PreservesFiniteLimits U := preservesFiniteLimits_of_reflects_of_preserves U Q
  have : ReflectsLimit (cospan f g) U := reflectsLimit_of_reflectsIsomorphisms _ U
  exact (hl.map I).of_map U w

end EtaleFundamentalGroups.Cohomology
