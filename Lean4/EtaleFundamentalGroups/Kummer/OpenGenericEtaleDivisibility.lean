/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Models.EtaleLocalRootDivisibility
import EtaleFundamentalGroups.Normalization.GenericFieldSourceNaturality
import EtaleFundamentalGroups.GeometricFiber.RationalPointLift
import EtaleFundamentalGroups.FiniteEtale.Connected
import EtaleFundamentalGroups.FiniteEtale.Integral
import SchemeTheory.Morphisms.DominantBaseChange
import SchemeTheory.LocalGeometry.SmoothStalkNormality
import SchemeTheory.Normalization.Normal

/-!
# Orders of actual generic Kummer roots on open smooth curves

The finite étale cover is the original geometric cover. Its given generic
fiber identifies its function field, and the actual étale stalk map supplies
the unramified local calculation. Properness is nowhere required.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

/-- A root in the actual generic fiber of a finite étale cover of a smooth
curve has divisible order at every actual closed point of that curve. -/
theorem ord_dvd_of_finiteEtale_generic_root_on_smoothCurve
    (K : Type) [Field K] [IsAlgClosed K]
    {X : Scheme} [IsIntegral X]
    (c : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 c]
    (L : Type) [Field L] [Algebra X.functionField L]
    {Y : Scheme} (f : Y ⟶ X) [IsFinite f] [Etale f]
    (e : pullback f (X.fromSpecStalk (genericPoint X)) ≅ Spec (.of L))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) =
      pullback.snd f (X.fromSpecStalk (genericPoint X)))
    (a : X.functionField) (b : L) (n : ℕ)
    (hb : b ^ n = algebraMap X.functionField L a) :
    let : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
    ∀ (x : closedPoints X) (v : Place K X.functionField),
      (algebraMap (X.presheaf.stalk x.val) X.functionField).range =
        v.toValuationSubring.toSubring → (n : ℤ) ∣ v.ord a := by
  intro algX x v hv
  let η := X.fromSpecStalk (genericPoint X)
  have : IsDominant η := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro z
    apply (genericPoint_specializes z).mem_closed isClosed_closure
    exact subset_closure ⟨IsLocalRing.closedPoint (CommRingCat.of X.functionField),
      Scheme.fromSpecStalk_closedPoint (X := X) (x := genericPoint X)⟩
  have : IsDominant (pullback.fst f η) :=
    isDominant_pullback_fst_of_isOpenMap f η f.isOpenMap
  let p : Spec (.of L) ⟶ Y := e.inv ≫ pullback.fst f η
  have : IsDominant p := by dsimp only [p]; infer_instance
  have : IsPreimmersion p := by dsimp only [p]; infer_instance
  have hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫ η := by
    dsimp only [p]
    rw [Category.assoc, pullback.condition, ← he, Category.assoc, e.inv_hom_id_assoc]
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral X := IsNormalIntegral.of_stalks X
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk c z).2)
  have : IsFiniteEtale f := {}
  let W : FiniteEtale X := FiniteEtale.mk f
  have : ConnectedSpace W.left :=
    { toPreconnectedSpace := p.denseRange.preconnectedSpace p.continuous
      toNonempty := ⟨p (IsLocalRing.closedPoint (CommRingCat.of L))⟩ }
  have : IsConnected W := FiniteEtale.isConnected_of_connectedSpace_left W
  have : IsIntegral Y := isIntegral_left_of_isConnected_finiteEtale W
  have : Surjective f := IsFiniteEtale.surjective f
  let hf : DenseRange f := f.surjective.denseRange
  let b' := (genericFieldSourceRingEquiv p).symm b
  have hb' : b' ^ n = f.functionFieldMap hf a :=
    genericFieldSourceRingEquiv_symm_pow f hf p hp a b n hb
  obtain ⟨y, hy⟩ := FiniteEtale.exists_closedPoint_above c W x
  have hv' : (algebraMap (X.presheaf.stalk (f y.val)) X.functionField).range =
      v.toValuationSubring.toSubring := by
    change (algebraMap (X.presheaf.stalk (W.hom y.val)) X.functionField).range = _
    rw [hy]
    exact hv
  exact ord_dvd_of_etale_functionField_root_at_closedPoint
    c f hf y.val y.property a b' n hb' v hv'

end EtaleFundamentalGroups
