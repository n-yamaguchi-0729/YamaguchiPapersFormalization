/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.EtaleCohomology.Sites.ZariskiSectionEquality
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.Topology.Sheaves.Stalks

/-!
# Zariski germs inside geometric étale stalks

The actual lift of a geometric point to each open neighborhood defines the
map from the Zariski stalk to the geometric étale stalk. Equality in the
latter occurs on an étale neighborhood. Descent to its open image proves
that this map is injective for a sheaf.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

namespace EtaleCohomology

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ X) (ξ : Spec (CommRingCat.of Ω))

/-- The actual geometric lift to an open neighborhood. -/
def zariskiGeometricLift (U : X.Opens) (hU : s ξ ∈ U) :
    (Scheme.pointSmallEtale s).fiber.obj ((zariskiToEtale X).obj U) := by
  have hRange : Set.range s ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨t, rfl⟩
    rw [Subsingleton.elim t ξ]
    exact hU
  let k : Spec (CommRingCat.of Ω) ⟶ U.toScheme := IsOpenImmersion.lift U.ι s hRange
  exact Over.homMk k (IsOpenImmersion.lift_fac U.ι s hRange)

private lemma zariskiGeometricLift_unique (U : X.Opens)
    (a b : (Scheme.pointSmallEtale s).fiber.obj ((zariskiToEtale X).obj U)) : a = b := by
  apply Over.OverMorphism.ext
  apply (cancel_mono U.ι).mp
  exact a.w.trans b.w.symm

private def zariskiGeometricNeighborhoods :
    OpenNhds (s ξ) ⥤ (Scheme.pointSmallEtale s).fiber.Elements where
  obj U := (Scheme.pointSmallEtale s).fiber.elementsMk ((zariskiToEtale X).obj U.1)
    (zariskiGeometricLift s ξ U.1 U.2)
  map {U V} g := Functor.Elements.homMk
    ((zariskiToEtale X).map ((OpenNhds.inclusion (s ξ)).map g))
    (zariskiGeometricLift_unique s V.1 _ _)
  map_id U := by
    apply Functor.Elements.hom_ext
    exact (zariskiToEtale X).map_id U.1
  map_comp g h := by
    apply Functor.Elements.hom_ext
    exact (zariskiToEtale X).map_comp _ _

variable (F : Sheaf X.smallEtaleTopology (Type u))

/-- The canonical map from the actual Zariski stalk to the geometric étale stalk. -/
def etaleZariskiStalkToGeometricStalk :
    TopCat.Presheaf.stalk ((etaleZariskiRestriction X (Type u)).obj F).obj (s ξ) ⟶
      (Scheme.pointSmallEtale s).presheafFiber.obj F.obj :=
  colimit.pre ((Functor.Elements.π (Scheme.pointSmallEtale s).fiber).op ⋙ F.obj)
    (zariskiGeometricNeighborhoods s ξ).op

/-- The stalk comparison sends an actual Zariski germ to its geometric germ. -/
lemma germ_etaleZariskiStalkToGeometricStalk (U : X.Opens) (hU : s ξ ∈ U) :
    TopCat.Presheaf.germ ((etaleZariskiRestriction X (Type u)).obj F).obj U (s ξ) hU ≫
        etaleZariskiStalkToGeometricStalk s ξ F =
      (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s ξ U hU) F.obj :=
  colimit.ι_pre ((Functor.Elements.π (Scheme.pointSmallEtale s).fiber).op ⋙ F.obj)
    (zariskiGeometricNeighborhoods s ξ).op (op ⟨U, hU⟩)

private lemma zariski_germ_eq_of_geometric_germ_eq
    (U : X.Opens) (hU : s ξ ∈ U)
    (a b : F.obj.obj (op ((zariskiToEtale X).obj U)))
    (hab : (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s ξ U hU) F.obj a =
      (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s ξ U hU) F.obj b) :
    TopCat.Presheaf.germ ((etaleZariskiRestriction X (Type u)).obj F).obj U (s ξ) hU a =
      TopCat.Presheaf.germ ((etaleZariskiRestriction X (Type u)).obj F).obj U (s ξ) hU b := by
  obtain ⟨V, g, y, _, hy⟩ := ((Scheme.pointSmallEtale s).toPresheafFiber_eq_iff' (P := F.obj)
    ((zariskiToEtale X).obj U) (zariskiGeometricLift s ξ U hU) a b).mp hab
  obtain ⟨W, hWU, hW, habW⟩ :=
    exists_zariski_neighborhood_sections_eq_of_etale_map_eq F U a b V g hy (y.left ξ)
  have hPoint : V.hom (y.left ξ) = s ξ :=
    (Scheme.Hom.comp_apply y.left V.hom ξ).symm.trans
      (congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ X => k ξ) y.w)
  rw [hPoint] at hW
  let H : (TopCat.of X).Presheaf (Type u) :=
    ((etaleZariskiRestriction X (Type u)).obj F).obj
  exact (H.germ_res_apply (homOfLE hWU) (s ξ) hW a).symm.trans
    ((congrArg (H.germ W (s ξ) hW) habW).trans
      (H.germ_res_apply (homOfLE hWU) (s ξ) hW b))

/-- A Zariski germ of an étale sheaf is determined by its geometric germ. -/
theorem etaleZariskiStalkToGeometricStalk_injective :
    Function.Injective (etaleZariskiStalkToGeometricStalk s ξ F) := by
  let H : (TopCat.of X).Presheaf (Type u) :=
    ((etaleZariskiRestriction X (Type u)).obj F).obj
  intro a b hab
  obtain ⟨U, hU, a, rfl⟩ := H.exists_germ_eq a
  obtain ⟨V, hVU, hV, b, rfl⟩ := H.exists_le_germ_eq b hU
  have hres := H.germ_res_apply (homOfLE hVU) (s ξ) hV a
  rw [← hres] at hab ⊢
  apply zariski_germ_eq_of_geometric_germ_eq s ξ F V hV
  have hg (c : H.obj (op V)) :
      etaleZariskiStalkToGeometricStalk s ξ F (H.germ V (s ξ) hV c) =
        (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj V)
          (zariskiGeometricLift s ξ V hV) F.obj c :=
    congrArg (fun k : H.obj (op V) ⟶ (Scheme.pointSmallEtale s).presheafFiber.obj F.obj => k c)
      (germ_etaleZariskiStalkToGeometricStalk s ξ F V hV)
  exact (hg _).symm.trans (hab.trans (hg b))

end EtaleCohomology
