/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.Monodromy
import EtaleFundamentalGroups.Cohomology.FiniteLocallyConstantDetection
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Surjectivity detected at one geometric stalk

For finite local systems on a connected scheme, a surjective stalk map at
one geometric point gives an epimorphism of actual abelian sheaves. Faithful
Galois fiber functors reflect epimorphisms and every geometric fiber functor
preserves them. The conservative family of geometric points then detects
the epimorphism in the ambient category of all abelian sheaves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology
open scoped FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

private abbrev localSystemStalk : EtaleFiniteLocallyConstantSetSheaf X ⥤ Type u :=
  ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X)) ⋙
    (Scheme.pointSmallEtale ξ).sheafFiber

private def localSystemStalkIso :
    ((finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse ⋙ FiniteEtale.fiber ξ) ⋙
      forget FintypeCat ≅ localSystemStalk ξ :=
  finiteLocallyConstantSetMonodromyStalkIso ξ

private theorem localSystemStalk_faithful : (localSystemStalk ξ).Faithful :=
  Functor.Faithful.of_iso (localSystemStalkIso ξ)

private theorem localSystemStalk_preservesEpis :
    (localSystemStalk ξ).PreservesEpimorphisms :=
  Functor.PreservesEpimorphisms.of_iso (localSystemStalkIso ξ)

/-- Surjectivity of a map of finite local systems at one geometric stalk
implies surjectivity at every geometric stalk on the connected base. -/
theorem surjective_finiteLocallyConstant_stalk_of_surjective
    {F G : EtaleFiniteLocallyConstantSetSheaf X} (f : F ⟶ G)
    (hf : Function.Surjective ((Scheme.pointSmallEtale ξ).sheafFiber.map f.hom))
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (ζ : Spec (.of Ω') ⟶ X) :
    Function.Surjective ((Scheme.pointSmallEtale ζ).sheafFiber.map f.hom) := by
  have : (localSystemStalk ξ).Faithful := localSystemStalk_faithful ξ
  have hmap : Epi ((localSystemStalk ξ).map f) :=
    (CategoryTheory.epi_iff_surjective _).mpr hf
  have : Epi f := (localSystemStalk ξ).epi_of_epi_map hmap
  have : (localSystemStalk ζ).PreservesEpimorphisms := localSystemStalk_preservesEpis ζ
  have hζ : Epi ((localSystemStalk ζ).map f) := inferInstance
  exact (CategoryTheory.epi_iff_surjective _).mp hζ

/-- A surjective geometric stalk detects an epimorphism of abelian sheaves
whose underlying set sheaves are finite locally constant. -/
theorem epi_of_surjective_finiteLocallyConstant_abelianStalk
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (f : F ⟶ G)
    (hF : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F))
    (hG : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj G))
    (hf : Function.Surjective ((Scheme.pointSmallEtale ξ).sheafFiber.map f)) :
    Epi f := by
  let U := sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})
  let f' : (⟨U.obj F, hF⟩ : EtaleFiniteLocallyConstantSetSheaf X) ⟶ ⟨U.obj G, hG⟩ :=
    ObjectProperty.homMk (U.map f)
  let e := (Scheme.pointSmallEtale ξ).sheafFiberCompIso (forget AddCommGrpCat.{u})
  have hf' : Function.Surjective ((Scheme.pointSmallEtale ξ).sheafFiber.map (U.map f)) := by
    intro y
    obtain ⟨x, hx⟩ := hf ((e.app G).hom y)
    refine ⟨(e.app F).inv x, (e.app G).toEquiv.injective ?_⟩
    have hn := congrArg (fun k => k ((e.app F).inv x)) (e.hom.naturality f)
    exact hn.trans ((congrArg ((Scheme.pointSmallEtale ξ).sheafFiber.map f)
      ((e.app F).toEquiv.apply_symm_apply x)).trans hx)
  apply (((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyReflectEpimorphisms
    AddCommGrpCat.{u}).epi_iff f).mpr
  rintro ⟨_, ⟨x⟩⟩
  let ζ := (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
    ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
  let Φ := Scheme.pointSmallEtale ζ
  let d := Φ.sheafFiberCompIso (forget AddCommGrpCat.{u})
  have hζ := surjective_finiteLocallyConstant_stalk_of_surjective ξ f' hf' ζ
  apply (AddCommGrpCat.epi_iff_surjective (Φ.sheafFiber.map f)).mpr
  intro y
  obtain ⟨z, hz⟩ := hζ ((d.app G).inv y)
  refine ⟨(d.app F).hom z, ?_⟩
  have hn := congrArg (fun k => k z) (d.hom.naturality f)
  exact hn.symm.trans ((congrArg (d.app G).hom hz).trans
    ((d.app G).toEquiv.apply_symm_apply y))

end EtaleFundamentalGroups.Cohomology
