/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite
import Nyll.AlgebraicCurves.Models.CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed
import Nyll.EtaleFundamentalGroups.Normalization.GenericFieldSource
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.SchemeTheory.Morphisms.DominantBaseChange
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality
import Nyll.SchemeTheory.Normalization.Normal
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Divisibility of orders from an actual finite étale generic root cover

A root in the field forming the generic fiber of a finite étale cover has
integral order at every point of the covering curve. The actual ramification
index is one, so the original orders are divisible by the root exponent.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
open CategoryTheory.PreGaloisCategory
open AlgebraicCurves.Models.Proofs
open
  CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite.AlgebraicCurve

namespace EtaleFundamentalGroups

private theorem ord_dvd_of_model_root
    (K : Type) [Field K] [IsAlgClosed K]
    {F E L : Type} [Field F] [Field E] [Field L] [Algebra K F] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E) [Algebra M.C.functionField L]
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase) [IsFinite d] [Etale d]
    (p : Spec (.of L) ⟶ N.C) [IsDominant p] [IsPreimmersion p]
    (hp : p ≫ d = Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField L)) ≫
      M.C.fromSpecStalk (genericPoint M.C))
    (a : M.C.functionField) (b : L) (n : ℕ)
    (hb : b ^ n = algebraMap M.C.functionField L a) :
    ∀ v : Place K F, (n : ℤ) ∣ v.ord (M.ffEquiv.symm a) := by
  have : IsFiniteEtale d := {}
  have : Surjective d := IsFiniteEtale.surjective d
  let φ : F →ₐ[K] E := FFLeg.phi K M N d hd d.surjective
  have hφ : φ.toRingHom.IsIntegral := FFLeg.isIntegral_phi K M N d hd d.surjective
  let ξ := FFLeg.specializes_genericPoint K M N d d.surjective
  let g : M.C.functionField →+* N.C.functionField :=
    (FFLeg.FunctionFieldPull.pull d ξ).hom
  have hg : Spec.map (CommRingCat.ofHom g) ≫ M.C.fromSpecStalk (genericPoint M.C) =
      N.C.fromSpecStalk (genericPoint N.C) ≫ d := by
    change Spec.map (M.C.presheaf.stalkSpecializes ξ ≫ d.stalkMap (genericPoint N.C)) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  let r : N.C.functionField ≃+* L := genericFieldSourceRingEquiv p
  have hr : Spec.map (CommRingCat.ofHom r.toRingHom) ≫
      N.C.fromSpecStalk (genericPoint N.C) = p :=
    genericFieldSourceIso_hom_fromSpecStalk p
  have hrg : r.toRingHom.comp g = algebraMap M.C.functionField L := by
    have hh : CommRingCat.ofHom (r.toRingHom.comp g) =
        CommRingCat.ofHom (algebraMap M.C.functionField L) := by
      apply Spec.map_injective
      apply (cancel_mono (M.C.fromSpecStalk (genericPoint M.C))).mp
      rw [show CommRingCat.ofHom (r.toRingHom.comp g) =
        CommRingCat.ofHom g ≫ CommRingCat.ofHom r.toRingHom by rfl,
        Spec.map_comp, Category.assoc, hg, ← Category.assoc, hr, hp]
    exact congrArg CommRingCat.Hom.hom hh
  let b' : E := N.ffEquiv.symm (r.symm b)
  have hb' : b' ^ n = φ (M.ffEquiv.symm a) := by
    apply N.ffEquiv.injective
    apply r.injective
    have hh := congrArg (fun q : M.C.functionField →+* L => q a) hrg
    change r (N.ffEquiv (b' ^ n)) = r (N.ffEquiv (φ (M.ffEquiv.symm a)))
    rw [map_pow]
    rw [show N.ffEquiv b' = r.symm b from N.ffEquiv.apply_symm_apply _,
      show N.ffEquiv (φ (M.ffEquiv.symm a)) = g a by
        change N.ffEquiv (N.ffEquiv.symm (g (M.ffEquiv (M.ffEquiv.symm a)))) = g a
        rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]]
    rw [map_pow, RingEquiv.apply_symm_apply, hb]
    exact hh.symm
  have hgen : N.C.fromSpecStalk (genericPoint N.C) ≫ d =
      Spec.map (CommRingCat.ofHom (N.ffEquiv.toRingHom.comp
        (φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) := by
    have heq : N.ffEquiv.toRingHom.comp
        (φ.toRingHom.comp M.ffEquiv.symm.toRingHom) = g := by
      ext z
      change N.ffEquiv (N.ffEquiv.symm (g (M.ffEquiv (M.ffEquiv.symm z)))) = g z
      rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    rw [heq]
    exact hg.symm
  intro v
  let x := M.pointEquivPlace.symm v
  let W : FiniteEtale M.C := FiniteEtale.mk d
  obtain ⟨y₀, hy₀⟩ := d.surjective (x.1 (IsLocalRing.closedPoint K))
  obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := d) (g := x.1) y₀
    (IsLocalRing.closedPoint K) hy₀
  let yHom : Over.mk x.1 ⟶ W.toComma :=
    FiniteEtale.fiberObjEquivHom x.1 W z
  let yArrow : Spec (.of K) ⟶ N.C := yHom.left
  have hyArrow : yArrow ≫ d = x.1 := yHom.w
  let y : {q : Spec (.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _} :=
    ⟨yArrow, by rw [← hd, ← Category.assoc, hyArrow]; exact x.2⟩
  let w : Place K E := N.pointEquivPlace y
  have hw : w.restrictAlong φ hφ = v := by
    apply M.pointEquivPlace.symm.injective
    apply Subtype.ext
    have hh := FFLeg.point_compat K M N d hd d.surjective w
    rw [show N.pointEquivPlace.symm w = y from N.pointEquivPlace.symm_apply_apply y] at hh
    exact hh.trans hyArrow
  have he : Place.ramificationIndexAlong φ w = 1 :=
    CurveModel.ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
      N M φ hφ d hd hgen y ⊤ trivial (by infer_instance)
  refine ⟨w.ord b', ?_⟩
  have ho := Place.ord_restrictAlong φ hφ w (M.ffEquiv.symm a)
  rw [he, hw, Nat.cast_one, one_mul, ← hb'] at ho
  rw [← zpow_natCast, Place.ord_zpow] at ho
  exact ho.symm

/-- If the actual generic fiber of a finite étale cover contains an `n`th
root of a rational function, its order at every place is divisible by `n`. -/
theorem ord_dvd_of_finiteEtale_generic_root
    (K : Type) [Field K] [IsAlgClosed K]
    {F : Type} [Field F] [Algebra K F] (M : CurveModel K F)
    (L : Type) [Field L] [Algebra M.C.functionField L]
    {Y : Scheme} (f : Y ⟶ M.C) [IsFinite f] [Etale f]
    (e : pullback f (M.C.fromSpecStalk (genericPoint M.C)) ≅ Spec (.of L))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField L)) =
      pullback.snd f (M.C.fromSpecStalk (genericPoint M.C)))
    (a : M.C.functionField) (b : L) (n : ℕ)
    (hb : b ^ n = algebraMap M.C.functionField L a) :
    ∀ v : Place K F, (n : ℤ) ∣ v.ord (M.ffEquiv.symm a) := by
  let η := M.C.fromSpecStalk (genericPoint M.C)
  have : IsDominant η := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro x
    apply (genericPoint_specializes x).mem_closed isClosed_closure
    exact subset_closure ⟨IsLocalRing.closedPoint (CommRingCat.of M.C.functionField),
      Scheme.fromSpecStalk_closedPoint (X := M.C) (x := genericPoint M.C)⟩
  have : IsDominant (pullback.fst f η) :=
    isDominant_pullback_fst_of_isOpenMap f η f.isOpenMap
  let p : Spec (.of L) ⟶ Y := e.inv ≫ pullback.fst f η
  have : IsDominant p := by dsimp only [p]; infer_instance
  have : IsPreimmersion p := by dsimp only [p]; infer_instance
  have hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField L)) ≫ η := by
    dsimp only [p]
    rw [Category.assoc, pullback.condition, ← he, Category.assoc, e.inv_hom_id_assoc]
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
  have : IsFiniteEtale f := {}
  let W : FiniteEtale M.C := FiniteEtale.mk f
  have : ConnectedSpace W.left :=
    { toPreconnectedSpace := p.denseRange.preconnectedSpace p.continuous
      toNonempty := ⟨p (IsLocalRing.closedPoint (CommRingCat.of L))⟩ }
  have : IsConnected W := FiniteEtale.isConnected_of_connectedSpace_left W
  have : IsIntegral Y := isIntegral_left_of_isConnected_finiteEtale W
  let cY : Y ⟶ Spec (.of K) := f ≫ M.toBase
  have : IsProper cY := by dsimp only [cY]; infer_instance
  have : SmoothOfRelativeDimension 1 cY :=
    smoothOfRelativeDimension_comp 0 1 f M.toBase
  let algY : Algebra K Y.functionField := (baseToFunctionField cY).toAlgebra
  obtain ⟨hcurve, hfinite, N, i, hi, _⟩ :=
    SmoothProperCurve.exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed K Y cY
  let d : N.C ⟶ M.C := i.hom ≫ f
  have hd : d ≫ M.toBase = N.toBase := by
    change (i.hom ≫ f) ≫ M.toBase = N.toBase
    exact (Category.assoc _ _ _).trans hi
  have : IsFinite d := by dsimp only [d]; infer_instance
  have : Etale d := by dsimp only [d]; infer_instance
  let p' : Spec (.of L) ⟶ N.C := p ≫ i.inv
  have : IsDominant p' := by dsimp only [p']; infer_instance
  have : IsPreimmersion p' := by dsimp only [p']; infer_instance
  have hp' : p' ≫ d =
      Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField L)) ≫ η := by
    dsimp only [p', d]
    rw [Category.assoc, i.inv_hom_id_assoc]
    exact hp
  exact ord_dvd_of_model_root K M N d hd p' hp' a b n hb

end EtaleFundamentalGroups
