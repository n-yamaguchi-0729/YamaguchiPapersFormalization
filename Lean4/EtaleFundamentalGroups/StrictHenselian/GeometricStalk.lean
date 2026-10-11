/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import EtaleFundamentalGroups.StrictHenselian.PointedEtaleNeighborhoods
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.RingTheory.LocalRing.Basic


/-!
# The local ring of a geometric point on the étale site

For an actual geometric point `s : Spec Ω ⟶ S`, take the filtered colimit
of the rings of global sections on all pointed étale neighborhoods of `s`.
The index category and its filteredness come from `Scheme.pointEtaleNeighborhoods`.
The construction also applies to an arbitrary field-valued point; separable
closedness is needed only when viewing it as a point of the étale topology.
This constructs a commutative ring, its maps from the neighborhoods, and its
evaluation homomorphism to `Ω`; no ring or universal property is postulated.

An element of this ring is a unit exactly when its evaluation is nonzero.
For the nontrivial direction, represent the element on an étale neighborhood
and replace that neighborhood by the basic open where the section is invertible.
The geometric point lifts to this basic open because its value is nonzero.
It follows that the constructed ring is local.

This is the actual étale-stalk construction needed for strict henselization.
The Henselian property, the identification of its residue field with the
separable closure of the original residue field, and the subsequent inertia
comparison are separate statements, not fields assumed by this construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Sections of the actual schemes in the small étale site. -/
def etaleSections (S : Scheme.{u}) : S.Etaleᵒᵖ ⥤ CommRingCat.{u} :=
  (Scheme.Etale.forget S ⋙ Over.forget S).op ⋙ Scheme.Γ

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- The filtered colimit of rings of sections on pointed étale neighborhoods. -/
def geometricStalk : CommRingCat.{u} :=
  (Scheme.pointEtaleNeighborhoods s).presheafFiber.obj (etaleSections S)

/-- For a separably closed field, this is literally the existing presheaf fiber
of the small étale site. Both constructions use the same functor of points
and the same chosen colimit; topology is not used by `presheafFiber`. -/
theorem geometricStalk_eq_smallEtale_presheafFiber [IsSepClosed Ω] :
    geometricStalk s = (Scheme.pointSmallEtale s).presheafFiber.obj (etaleSections S) :=
  rfl

/-- The ring homomorphism from an actual pointed étale neighborhood to the
geometric stalk. -/
def geometricStalkGerm (W : S.Etale)
    (t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W) :
    Γ(W.left, ⊤) ⟶ geometricStalk s :=
  (Scheme.pointEtaleNeighborhoods s).toPresheafFiber W t (etaleSections S)

/-- Evaluation in `Ω`, obtained by descending the section maps along the
geometric points of the neighborhoods. -/
def geometricStalkEvaluation : geometricStalk s ⟶ CommRingCat.of Ω :=
  (Scheme.pointEtaleNeighborhoods s).presheafFiberDesc
    (fun (W : S.Etale) (t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W) =>
      t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom)
    (by
      intro W V f t
      change f.left.appTop ≫ t.left.appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom =
        (t.left ≫ f.left).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
      rw [Scheme.Hom.comp_appTop t.left f.left, Category.assoc]
      rfl)

/-- Evaluation of a germ is evaluation of its representing section. -/
theorem geometricStalkGerm_evaluation (W : S.Etale)
    (t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W) :
    geometricStalkGerm s W t ≫ geometricStalkEvaluation s =
      t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom :=
  (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_presheafFiberDesc _ _ W t

/-- Every element of the constructed colimit is represented on an actual
pointed étale neighborhood. -/
theorem geometricStalk_exists_representative (a : geometricStalk s) :
    ∃ (W : S.Etale) (t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W)
      (z : Γ(W.left, ⊤)), geometricStalkGerm s W t z = a :=
  (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_jointly_surjective a

/-- A finite family of germs has representatives on one actual pointed étale
neighborhood.  The common neighborhood is supplied by cofilteredness of the
category of elements of the geometric-point functor. -/
theorem geometricStalk_exists_representatives {ι : Type*} [Finite ι]
    (a : ι → geometricStalk s) :
    ∃ (W : S.Etale) (t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W)
      (z : ι → Γ(W.left, ⊤)), ∀ i, geometricStalkGerm s W t (z i) = a i := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose W t z hz using fun i => geometricStalk_exists_representative s (a i)
  let F : Discrete ι ⥤ (Scheme.pointEtaleNeighborhoods s).fiber.Elements :=
    Discrete.functor fun i => (Scheme.pointEtaleNeighborhoods s).fiber.elementsMk (W i) (t i)
  obtain ⟨c⟩ := IsCofiltered.cone_nonempty F
  refine ⟨c.pt.obj, c.pt.val,
    (fun i => (etaleSections S).map (c.π.app ⟨i⟩).hom.op (z i)), ?_⟩
  intro i
  have h := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w
    (c.π.app ⟨i⟩).hom c.pt.val (etaleSections S)
  have hval : (Scheme.pointEtaleNeighborhoods s).fiber.map (c.π.app ⟨i⟩).hom c.pt.val =
      t i := (c.π.app ⟨i⟩).map_val
  simp only [hval] at h
  exact (ConcreteCategory.congr_hom h (z i)).trans (hz i)

/-- The constructed ring has distinct zero and one, since it has its actual
evaluation homomorphism to a field. -/
instance geometricStalk_nontrivial : Nontrivial (geometricStalk s) :=
  (geometricStalkEvaluation s).hom.domain_nontrivial

/-- A nonzero value at the geometric point makes a germ invertible: restrict
its representative to its basic open and use the filtered-colimit relation. -/
theorem geometricStalk_isUnit_of_evaluation_ne_zero
    (a : geometricStalk s) (ha : geometricStalkEvaluation s a ≠ 0) :
    IsUnit a := by
  obtain ⟨W, t, z, rfl⟩ := geometricStalk_exists_representative s a
  have heval := ConcreteCategory.congr_hom (geometricStalkGerm_evaluation s W t) z
  have hvalue : (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom (t.left.appTop z) ≠ 0 := by
    change (geometricStalkGerm s W t ≫ geometricStalkEvaluation s) z ≠ 0 at ha
    change (t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom) z ≠ 0
    exact heval ▸ ha
  have hunitValue : IsUnit (t.left.appTop z) := by
    have hunit := (isUnit_iff_ne_zero.mpr hvalue).map
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    change IsUnit (((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv) (t.left.appTop z)) at hunit
    simpa only [Iso.hom_inv_id, CommRingCat.id_apply] using hunit
  let V : W.left.Opens := W.left.basicOpen z
  have hpointRange : Set.range t.left ⊆ Set.range V.ι := by
    apply Set.Subset.trans ?_ (Scheme.Opens.range_ι V).symm.subset
    rintro _ ⟨y, rfl⟩
    change y ∈ t.left ⁻¹ᵁ W.left.basicOpen z
    have hpreimage : t.left ⁻¹ᵁ W.left.basicOpen z =
        (Spec (CommRingCat.of Ω)).basicOpen (t.left.appTop z) :=
      Scheme.preimage_basicOpen_top t.left z
    rw [hpreimage, (Spec (CommRingCat.of Ω)).basicOpen_of_isUnit hunitValue]
    trivial
  let l : Spec (CommRingCat.of Ω) ⟶ V :=
    IsOpenImmersion.lift V.ι t.left hpointRange
  have hl : l ≫ V.ι = t.left :=
    IsOpenImmersion.lift_fac V.ι t.left hpointRange
  let T : S.Etale := Scheme.Etale.mk (V.ι ≫ W.hom)
  let f : T ⟶ W := MorphismProperty.Over.homMk V.ι rfl
  let tV : (Scheme.pointEtaleNeighborhoods s).fiber.obj T := Over.homMk l (by
    change l ≫ (V.ι ≫ W.hom) = s
    rw [← Category.assoc, hl]
    exact Over.w t)
  have htV : (Scheme.pointEtaleNeighborhoods s).fiber.map f tV = t := by
    apply Over.OverMorphism.ext
    exact hl
  have hunitSection : IsUnit (V.ι.appTop z) := by
    apply RingedSpace.isUnit_of_isUnit_germ V.toScheme.toRingedSpace ⊤ (V.ι.appTop z)
    intro v _
    apply (V.toScheme.mem_basicOpen_top (V.ι.appTop z) v).mp
    rw [← Scheme.preimage_basicOpen_top]
    exact v.property
  have hgerm : geometricStalkGerm s T tV (V.ι.appTop z) =
      geometricStalkGerm s W t z := by
    have h := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w f tV (etaleSections S)
    rw [htV] at h
    exact ConcreteCategory.congr_hom h z
  rw [← hgerm]
  exact hunitSection.map (geometricStalkGerm s T tV).hom

/-- Units in the étale geometric stalk are detected by their actual values. -/
theorem geometricStalk_isUnit_iff (a : geometricStalk s) :
    IsUnit a ↔ geometricStalkEvaluation s a ≠ 0 := by
  constructor
  · intro ha
    exact (ha.map (geometricStalkEvaluation s).hom).ne_zero
  · exact geometricStalk_isUnit_of_evaluation_ne_zero s a

/-- The étale geometric stalk constructed as a filtered colimit is a local ring. -/
instance geometricStalk_isLocalRing : IsLocalRing (geometricStalk s) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  by_cases ha : geometricStalkEvaluation s a = 0
  · right
    apply geometricStalk_isUnit_of_evaluation_ne_zero s
    rw [map_sub, map_one, ha, sub_zero]
    exact one_ne_zero
  · exact Or.inl (geometricStalk_isUnit_of_evaluation_ne_zero s a ha)

end EtaleFundamentalGroups.StrictHenselian
