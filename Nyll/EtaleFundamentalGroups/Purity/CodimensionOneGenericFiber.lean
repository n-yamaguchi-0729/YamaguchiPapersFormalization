/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.CodimensionOneBoundary
import Nyll.SchemeTheory.LocalGeometry.GenericComplementPuncture
import Nyll.SchemeTheory.LocalGeometry.PuncturedDVR
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Closure

/-!
# Canonical generic maps at a codimension-one boundary point

For a dense open and a missing point whose stalk is a DVR, the actual
stalk overlap is identified with the spectrum of its fraction field.
The induced map from that fraction field to the open preserves the map
to the ambient scheme.

When the open is enlarged without including the point, these two
constructed generic maps agree after the inclusion. This comparison
retains the same stalk, fraction field, and structural ring map; it is the
input for transporting an original cover's generic fibre to an extension
over the larger open in Stacks Project, Lemma 58.31.2 (tag 0H2W).
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The actual stalk overlap of a dense open at a DVR boundary point is
the spectrum of the original stalk's fraction field. -/
def denseOpenDVRPullbackIso
    (U : X.Opens) (hU : Dense (U : Set X)) (x : X) (hx : x ∉ U)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞)) :
    Limits.pullback (X.fromSpecStalk x) U.ι ≅
      Spec (.of (FractionRing (X.presheaf.stalk x))) :=
  genericComplementPuncturedSpectrumPullbackIso U
    ⟨⟨x, hx⟩, mem_genericPoints_complement_of_stalk_dimension_one U hU x hx hdim⟩ ≪≫
      puncturedSpectrumIsoSpecFractionField
        (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))

/-- The overlap comparison preserves the canonical morphism to the full
stalk spectrum. -/
@[reassoc]
theorem denseOpenDVRPullbackIso_hom_SpecMap
    (U : X.Opens) (hU : Dense (U : Set X)) (x : X) (hx : x ∉ U)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞)) :
    (denseOpenDVRPullbackIso U hU x hx hdim).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)))) =
      Limits.pullback.fst (X.fromSpecStalk x) U.ι := by
  change ((genericComplementPuncturedSpectrumPullbackIso U
    ⟨⟨x, hx⟩, mem_genericPoints_complement_of_stalk_dimension_one U hU x hx hdim⟩).hom ≫
      (puncturedSpectrumIsoSpecFractionField
        (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))).hom) ≫ _ = _
  rw [Category.assoc, puncturedSpectrumIsoSpecFractionField_hom_SpecMap,
    genericComplementPuncturedSpectrumPullbackIso_hom_inclusion]

/-- The canonical generic-point morphism into the original dense open,
constructed from its actual stalk overlap. -/
def denseOpenDVRFractionFieldMap
    (U : X.Opens) (hU : Dense (U : Set X)) (x : X) (hx : x ∉ U)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞)) :
    Spec (.of (FractionRing (X.presheaf.stalk x))) ⟶ U.toScheme :=
  (denseOpenDVRPullbackIso U hU x hx hdim).inv ≫
    Limits.pullback.snd (X.fromSpecStalk x) U.ι

/-- The constructed generic morphism is over the ambient scheme, with
the original fraction-field coefficient map. -/
@[reassoc]
theorem denseOpenDVRFractionFieldMap_comp_ι
    (U : X.Opens) (hU : Dense (U : Set X)) (x : X) (hx : x ∉ U)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞)) :
    denseOpenDVRFractionFieldMap U hU x hx hdim ≫ U.ι =
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)))) ≫
          X.fromSpecStalk x := by
  let e : Limits.pullback (X.fromSpecStalk x) U.ι ≅
      Spec (.of (FractionRing (X.presheaf.stalk x))) :=
    denseOpenDVRPullbackIso U hU x hx hdim
  let q : Spec (X.presheaf.stalk x) ⟶ X := X.fromSpecStalk x
  let g : Spec (.of (FractionRing (X.presheaf.stalk x))) ⟶ Spec (X.presheaf.stalk x) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))))
  have he : e.hom ≫ g = Limits.pullback.fst q U.ι :=
    denseOpenDVRPullbackIso_hom_SpecMap U hU x hx hdim
  have heInv : e.inv ≫ Limits.pullback.fst q U.ι = g := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  change (e.inv ≫ Limits.pullback.snd q U.ι) ≫ U.ι = g ≫ q
  calc
    (e.inv ≫ Limits.pullback.snd q U.ι) ≫ U.ι =
        e.inv ≫ (Limits.pullback.snd q U.ι ≫ U.ι) := Category.assoc _ _ _
    _ = e.inv ≫ (Limits.pullback.fst q U.ι ≫ q) :=
      congrArg (fun t ↦ e.inv ≫ t) Limits.pullback.condition.symm
    _ = (e.inv ≫ Limits.pullback.fst q U.ι) ≫ q := (Category.assoc _ _ _).symm
    _ = g ≫ q := congrArg (fun t ↦ t ≫ q) heInv

/-- Enlarging the dense open preserves the actual generic-point map after
composition with the inclusion. Both maps use the same stalk fraction field. -/
theorem denseOpenDVRFractionFieldMap_homOfLE
    (U N : X.Opens) (hU : Dense (U : Set X)) (hUN : U ≤ N)
    (x : X) (hxN : x ∉ N)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞)) :
    denseOpenDVRFractionFieldMap U hU x (fun hx ↦ hxN (hUN hx)) hdim ≫
        X.homOfLE hUN =
      denseOpenDVRFractionFieldMap N (Dense.mono hUN hU) x hxN hdim := by
  apply (cancel_mono N.ι).mp
  rw [Category.assoc, homOfLE_ι,
    denseOpenDVRFractionFieldMap_comp_ι, denseOpenDVRFractionFieldMap_comp_ι]

end AlgebraicGeometry.Scheme
