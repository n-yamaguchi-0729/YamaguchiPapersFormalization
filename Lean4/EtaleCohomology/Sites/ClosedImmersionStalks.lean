/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.BaseChange
import EtaleCohomology.Sites.ClosedNeighborhoods
import EtaleCohomology.Sites.EmptySections
import EtaleCohomology.Sites.ExtensionByZero
import EtaleCohomology.Sites.PullbackStalks
import EtaleCohomology.Sites.RestrictionStalks
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Sites.Point.Comap
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Stalks of direct image along a closed immersion

At a geometric point of the closed subscheme, the stalk of direct image is
the original stalk. Initiality of the constructed neighborhood functor and
the comparison of colimits supply the natural isomorphism. The result holds
for arbitrary schemes and commutative coefficient rings. Outside the closed
subscheme, restriction to its open complement vanishes, so the stalk is zero.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Restricting direct image to an open subscheme disjoint from the image gives zero.
The morphism defining direct image need not be a closed immersion. -/
lemma openEtaleRestriction_pushforward_isZero_of_disjoint
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hd : Disjoint (Set.range j) (Set.range i))
    (R : Type u) [CommRing R] (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)) :
    IsZero ((openEtaleRestriction j R).obj ((etalePushforward i R).obj F)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u} R)).map_injective
  apply NatTrans.ext
  funext V
  change 𝟙 (F.obj.obj (op ((etaleBaseChange i).obj ((openEtaleInclusion j).obj V.unop)))) = 0
  have hempty : IsEmpty ((etaleBaseChange i).obj ((openEtaleInclusion j).obj V.unop)).left := by
    change IsEmpty ↥(pullback (V.unop.hom ≫ j) i)
    apply Scheme.isEmpty_pullback
    apply Set.disjoint_left.mpr
    rintro x ⟨y, rfl⟩ hi
    exact Set.disjoint_left.mp hd ⟨V.unop.hom y, rfl⟩ hi
  exact (etaleSections_isZero_of_isEmpty _ F).eq_of_src _ _

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z)
  (R : Type u) [CommRing R]

/-- At a geometric point of the closed subscheme, direct image has the original stalk. -/
def etalePushforwardClosedStalkIso :
    etalePushforward i R ⋙ (Scheme.pointSmallEtale (s ≫ i)).sheafFiber ≅
      (Scheme.pointSmallEtale s).sheafFiber := by
  let : RepresentablyFlat (etaleBaseChange i) := flat_of_preservesFiniteLimits _
  let : (Functor.Elements.precomp (etaleBaseChange i) (Scheme.pointSmallEtale s).fiber).Initial :=
    closedNeighborhoodBaseChange_initial i s
  exact Functor.isoWhiskerLeft (etalePushforward i R) (geometricComapSheafFiberIso i s R).symm ≪≫
    Sites.restrictionComapStalkIso (etaleBaseChange i) (etaleBaseChange_coverPreserving i)
      (Scheme.pointSmallEtale s) (ModuleCat.{u} R)

/-- Direct image along a closed immersion has zero stalk outside its image. -/
lemma etalePushforward_stalk_isZero_of_not_mem_range
    (t : Spec (.of Ω) ⟶ X) (z : Spec (.of Ω)) (hz : t z ∉ Set.range i)
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)) :
    IsZero ((Scheme.pointSmallEtale t).sheafFiber.obj ((etalePushforward i R).obj F)) := by
  let U : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hrange : Set.range t ⊆ Set.range U.ι := by
    rintro x ⟨a, rfl⟩
    have ha : t a ∉ Set.range i := by rwa [Subsingleton.elim a z]
    exact ⟨⟨t a, ha⟩, rfl⟩
  let s : Spec (.of Ω) ⟶ U := IsOpenImmersion.lift U.ι t hrange
  have hs : s ≫ U.ι = t := IsOpenImmersion.lift_fac U.ι t hrange
  have hd : Disjoint (Set.range U.ι) (Set.range i) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a, rfl⟩ hi
    exact a.property hi
  let G := (etalePushforward i R).obj F
  have hrestrict : IsZero ((openEtaleRestriction U.ι R).obj G) :=
    openEtaleRestriction_pushforward_isZero_of_disjoint i U.ι hd R F
  have hpull : IsZero ((etalePullback U.ι R).obj G) :=
    ((etalePullbackOpenRestrictionIso U.ι R).app G).isZero_iff.mpr hrestrict
  have hstalk : IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj
      ((etalePullback U.ι R).obj G)) :=
    (Scheme.pointSmallEtale s).sheafFiber.map_isZero hpull
  rw [← hs]
  exact ((etalePullbackStalkIso U.ι s R).app G).isZero_iff.mp hstalk

end EtaleCohomology
