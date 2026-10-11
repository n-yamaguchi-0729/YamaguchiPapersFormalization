/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.GenericFieldSource
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationSourceIso
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedRestriction
import Nyll.SchemeTheory.Morphisms.DominantBaseChange
import Nyll.SchemeTheory.Normalization.FiniteSeparable
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Topology.Connected.Basic

/-!
# Normalization from a finite étale model of the generic fiber

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
theorem etale_genericExtensionNormalization_of_finiteEtale_genericFiber
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    {Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f]
    (p : Spec (.of L) ⟶ Y)
    (H : IsPullback p (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)))
      f (X.fromSpecStalk (genericPoint X))) :
    Etale (X.genericExtensionMorphism L).fromNormalization := by
  let : IsFiniteEtale f := {}
  let W : FiniteEtale X := FiniteEtale.mk f
  let pW : Spec (.of L) ⟶ W.left := p
  let η := X.fromSpecStalk (genericPoint X)
  let : IsDominant η := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro x
    apply (genericPoint_specializes x).mem_closed isClosed_closure
    exact subset_closure ⟨IsLocalRing.closedPoint (CommRingCat.of X.functionField),
      Scheme.fromSpecStalk_closedPoint (X := X) (x := genericPoint X)⟩
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
  have he : e.hom ≫ g = X.genericExtensionMorphism L := by
    change e.hom ≫
      ((W.left.genericExtensionMorphism W.left.functionField) ≫ f) = X.genericExtensionMorphism L
    unfold Scheme.genericExtensionMorphism
    rw [show CommRingCat.ofHom (algebraMap W.left.functionField W.left.functionField) = 𝟙 _ by rfl]
    rw [Spec.map_id, Category.id_comp]
    exact (Category.assoc e.hom (W.left.fromSpecStalk (genericPoint W.left)) f).symm.trans
      ((congrArg (fun k : Spec (.of L) ⟶ W.left => k ≫ f)
        (genericFieldSourceIso_hom_fromSpecStalk pW)).trans H.w)
  let E := Inertia.normalizationSourceIso (X.genericExtensionMorphism L) g e he
  let F := FiniteEtale.connectedCoverGenericNormalizationIso W
  have hF : F.hom ≫ f = g.fromNormalization := by
    have h : F.inv ≫ g.fromNormalization = f :=
      FiniteEtale.connectedCoverGenericNormalizationIso_inv_fromNormalization W
    exact (congrArg (fun k : W.left ⟶ X => F.hom ≫ k) h.symm).trans
      (F.hom_inv_id_assoc g.fromNormalization)
  let i : (X.genericExtensionMorphism L).normalization ≅ Y := E ≪≫ F
  have hbase : i.hom ≫ f = (X.genericExtensionMorphism L).fromNormalization := by
    exact (Category.assoc E.hom F.hom f).trans
      ((congrArg (fun k : g.normalization ⟶ X => E.hom ≫ k) hF).trans
        (Inertia.normalizationSourceIso_hom_fromNormalization
          (X.genericExtensionMorphism L) g e he))
  rw [← hbase]
  infer_instance

end EtaleFundamentalGroups
