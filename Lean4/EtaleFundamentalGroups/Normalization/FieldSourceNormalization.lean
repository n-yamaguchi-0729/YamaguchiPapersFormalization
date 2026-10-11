/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.GenericFieldSource
import EtaleFundamentalGroups.Inertia.NormalizationSourceIso
import EtaleFundamentalGroups.FiniteEtale.Connected
import EtaleFundamentalGroups.FiniteEtale.Integral
import EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedRestriction
import SchemeTheory.Morphisms.DominantBaseChange
import SchemeTheory.Normalization.FiniteSeparable
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Topology.Connected.Basic

/-!
# Normalization at a supplied generic field source

If the actual generic fiber of a finite étale morphism is a field spectrum,
its source is connected. Over a normal integral base it is therefore the
normalization in its function field. The generic pullback identifies that
function-field spectrum with the given field spectrum, transporting the
normalization isomorphism and its étaleness to the given extension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

private local instance fieldSpecQuasiCompact
    {K : Type u} [Field K] {S : Scheme.{u}} (f : Spec (.of K) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

/-- A finite étale model with actual generic fiber `Spec L` makes the
normalization of the base in `L` étale. No connectedness or comparison of
function fields is an additional hypothesis. -/
theorem etale_fieldSourceNormalization_of_finiteEtale_genericFiber
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (F L : Type u) [Field F] [Field L] [Algebra F L]
    (j : Spec (.of F) ⟶ X) [IsDominant j] [IsPreimmersion j]
    {Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f]
    (p : Spec (.of L) ⟶ Y)
    (H : IsPullback p (Spec.map (CommRingCat.ofHom (algebraMap F L)))
      f j) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ j).fromNormalization := by
  let : IsFiniteEtale f := {}
  let W : FiniteEtale X := FiniteEtale.mk f
  let pW : Spec (.of L) ⟶ W.left := p
  let η := j
  let : IsDominant (pullback.fst f η) :=
    isDominant_pullback_fst_of_isOpenMap f η f.isOpenMap
  let : IsDominant pW := by
    change IsDominant p
    rw [← H.isoPullback_hom_fst]
    infer_instance
  let : IsPreimmersion pW := by
    change IsPreimmersion p
    rw [← H.isoPullback_hom_fst]
    infer_instance
  let : ConnectedSpace W.left := by
    exact
      { toPreconnectedSpace := pW.denseRange.preconnectedSpace pW.continuous
        toNonempty := ⟨pW (IsLocalRing.closedPoint (CommRingCat.of L))⟩ }
  let : IsConnected W := FiniteEtale.isConnected_of_connectedSpace_left W
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let e := genericFieldSourceIso pW
  let g := FiniteEtale.connectedCoverGenericComposite W
  have he : e.hom ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ j := by
    change e.hom ≫
      ((W.left.genericExtensionMorphism W.left.functionField) ≫ f) =
        Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ j
    unfold Scheme.genericExtensionMorphism
    rw [show CommRingCat.ofHom (algebraMap W.left.functionField W.left.functionField) = 𝟙 _ by rfl]
    rw [Spec.map_id, Category.id_comp]
    exact (Category.assoc e.hom (W.left.fromSpecStalk (genericPoint W.left)) f).symm.trans
      ((congrArg (fun k : Spec (.of L) ⟶ W.left => k ≫ f)
        (genericFieldSourceIso_hom_fromSpecStalk pW)).trans H.w)
  let E := Inertia.normalizationSourceIso (Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ j) g e he
  let c := FiniteEtale.connectedCoverGenericNormalizationIso W
  have hF : c.hom ≫ f = g.fromNormalization := by
    have h : c.inv ≫ g.fromNormalization = f :=
      FiniteEtale.connectedCoverGenericNormalizationIso_inv_fromNormalization W
    exact (congrArg (fun k : W.left ⟶ X => c.hom ≫ k) h.symm).trans
      (c.hom_inv_id_assoc g.fromNormalization)
  let i : (Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ j).normalization ≅ Y := E ≪≫ c
  have hbase : i.hom ≫ f =
      (Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ j).fromNormalization := by
    exact (Category.assoc E.hom c.hom f).trans
      ((congrArg (fun k : g.normalization ⟶ X => E.hom ≫ k) hF).trans
        (Inertia.normalizationSourceIso_hom_fromNormalization
          (Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ j) g e he))
  rw [← hbase]
  infer_instance

end EtaleFundamentalGroups
