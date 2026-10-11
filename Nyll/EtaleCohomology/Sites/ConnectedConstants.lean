/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.ConstantRepresentable
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Logic.Function.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions

/-!
# Constant étale sheaves on connected schemes

A section of a disjoint union of copies of a connected scheme lands in a
unique component. Using the actual constant-sheaf adjunction unit and the
representation by that disjoint union, the constant set-sheaf functor is
fully faithful. The set can be infinite, and the scheme need not be locally
noetherian or lie over a field.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Every section of the disjoint union of copies of a connected scheme is
the inclusion of a unique component. -/
lemma etaleCopiesInj_bijective (X : Scheme.{u}) [ConnectedSpace X] (ι : Type u) :
    Function.Bijective (etaleCopiesInj X ι) := by
  classical
  let x₀ : X := Classical.choice inferInstance
  constructor
  · intro i j hij
    have hp := congrArg (fun f : etaleBaseObject X ⟶ etaleCopies X ι => f.left x₀) hij
    exact congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : ι => X) i j x₀ x₀).mp hp)
  · intro f
    let : TopologicalSpace ι := ⊥
    have : DiscreteTopology ι := ⟨rfl⟩
    let e := sigmaMk (fun _ : ι => X)
    let k : X → ι := fun x => (e.symm (f.left x)).1
    have hc : Continuous k :=
      (continuous_sigma (fun _ : ι => continuous_const)).comp
        (e.symm.continuous.comp f.left.continuous)
    let i : ι := k x₀
    have hr : Set.range f.left ⊆ Set.range (Sigma.ι (fun _ : ι => X) i) := by
      rintro _ ⟨x, rfl⟩
      let y : X := (e.symm (f.left x)).2
      have hi : k x = i := PreconnectedSpace.constant inferInstance hc
      have hz : e.symm (f.left x) = ⟨i, y⟩ := Sigma.ext hi HEq.rfl
      refine ⟨y, ?_⟩
      rw [← sigmaMk_mk, ← hz]
      exact e.apply_symm_apply (f.left x)
    have : IsOpenImmersion (Sigma.ι (fun _ : ι => X) i) :=
      (sigmaOpenCover (fun _ : ι => X)).map_prop i
    let l : X ⟶ X := IsOpenImmersion.lift (Sigma.ι (fun _ : ι => X) i) f.left hr
    have hf : l ≫ Sigma.ι (fun _ : ι => X) i = f.left :=
      IsOpenImmersion.lift_fac (Sigma.ι (fun _ : ι => X) i) f.left hr
    have hl : l = 𝟙 X := by
      have hi : Sigma.ι (fun _ : ι => X) i ≫ (etaleCopies X ι).hom = 𝟙 X :=
        Sigma.ι_comp_desc (fun _ : ι => 𝟙 X) i
      exact (Category.comp_id l).symm.trans
        ((congrArg (fun g : X ⟶ X => l ≫ g) hi.symm).trans
          ((Category.assoc l (Sigma.ι (fun _ : ι => X) i) (etaleCopies X ι).hom).symm.trans
            ((congrArg (fun g : X ⟶ (etaleCopies X ι).left =>
              g ≫ (etaleCopies X ι).hom) hf).trans f.w)))
    refine ⟨i, MorphismProperty.Over.Hom.ext ?_⟩
    exact (Category.id_comp _).symm.trans
      ((congrArg (fun g => g ≫ Sigma.ι (fun _ : ι => X) i) hl).symm.trans hf)

/-- On a connected scheme, global sections recover the set defining a
constant étale sheaf through the actual adjunction unit. -/
lemma etaleConstantSheaf_unit_isIso (X : Scheme.{u}) [ConnectedSpace X] (ι : Type u) :
    IsIso ((constantSheafAdj X.smallEtaleTopology (Type u)
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) X)).unit.app ι) := by
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let η := (constantSheafAdj X.smallEtaleTopology (Type u) hT).unit.app ι
  let e := (etaleCopiesSheafIso X ι).inv.hom.app (op (etaleBaseObject X))
  have he : Function.Bijective e := (CategoryTheory.isIso_iff_bijective e).mp inferInstance
  have hc : (fun i => e (η i)) = etaleCopiesInj X ι :=
    funext (etaleCopiesSheafIso_inv_unit X ι)
  apply (CategoryTheory.isIso_iff_bijective η).mpr
  apply (Function.Bijective.of_comp_iff' he (fun i => η i)).mp
  change Function.Bijective (fun i => e (η i))
  rw [hc]
  exact etaleCopiesInj_bijective X ι

/-- The constant set-sheaf functor on a connected scheme is fully faithful. -/
def etaleConstantSheafFullyFaithful (X : Scheme.{u}) [ConnectedSpace X] :
    (constantSheaf X.smallEtaleTopology (Type u)).FullyFaithful := by
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let adj := constantSheafAdj X.smallEtaleTopology (Type u) hT
  have (ι : Type u) : IsIso (adj.unit.app ι) := etaleConstantSheaf_unit_isIso X ι
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app adj.unit
  exact adj.fullyFaithfulLOfIsIsoUnit

end EtaleCohomology
