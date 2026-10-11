/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.Monodromy
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Morphisms of finite local systems detected on a geometric stalk

The monodromy equivalence makes one geometric stalk faithful on finite local
systems on a connected scheme. The comparison with the underlying set stalk
then detects equality of morphisms of the actual abelian sheaves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology
open scoped FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- Morphisms of finite locally constant abelian sheaves on a connected scheme
are determined by their maps on one actual geometric stalk. -/
theorem hom_ext_finiteLocallyConstant_abelianStalk
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (f g : F ⟶ G)
    (hF : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F))
    (hG : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj G))
    (h : (Scheme.pointSmallEtale ξ).sheafFiber.map f =
      (Scheme.pointSmallEtale ξ).sheafFiber.map g) : f = g := by
  let U := sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})
  let I := ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X))
  let Φ := (Scheme.pointSmallEtale ξ).sheafFiber (A := Type u)
  have : (I ⋙ Φ).Faithful :=
    Functor.Faithful.of_iso (finiteLocallyConstantSetMonodromyStalkIso ξ)
  let f' : (⟨U.obj F, hF⟩ : EtaleFiniteLocallyConstantSetSheaf X) ⟶ ⟨U.obj G, hG⟩ :=
    ObjectProperty.homMk (U.map f)
  let g' : (⟨U.obj F, hF⟩ : EtaleFiniteLocallyConstantSetSheaf X) ⟶ ⟨U.obj G, hG⟩ :=
    ObjectProperty.homMk (U.map g)
  let e := (Scheme.pointSmallEtale ξ).sheafFiberCompIso (forget AddCommGrpCat.{u})
  have hf'g' : f' = g' := by
    apply (I ⋙ Φ).map_injective
    apply (cancel_mono (e.app G).hom).mp
    exact (e.hom.naturality f).trans
      ((congrArg ((e.app F).hom ≫ ·) (congrArg (forget AddCommGrpCat.{u}).map h)).trans
        (e.hom.naturality g).symm)
  apply U.map_injective
  exact congrArg (fun t => t.hom) hf'g'

end EtaleFundamentalGroups.Cohomology
