/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Models.CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Mathlib.AlgebraicGeometry.Stalk
import AlgebraicCurves.Places.Place_ord_eq_zero_of_evalAt_ne_zero
import AlgebraicCurves.Models.CurveModel_isRational_pointEquivPlace

/-!
# Evaluation at the actual geometric generic point

The value of a pulled-back rational function at the geometric generic
point is its image in the geometric-point field. The proof compares
actual scheme stalk maps and the existing place-evaluation map.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicCurve.CurveModel

/-- Actual place evaluation at a lifted generic point agrees with the
specified embedding of the original function field. -/
theorem evalAt_geometricGenericPoint
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme} [IsIntegral X]
    (p : M.C ⟶ X) (φ : X.functionField →+* F)
    (hφ : ∀ (U : X.Opens) [Nonempty U] [Nonempty (p ⁻¹ᵁ U)] (s : Γ(X, U)),
      φ (X.germToFunctionField U s) =
        M.ffEquiv.symm (M.C.germToFunctionField (p ⁻¹ᵁ U) ((p.app U).hom s)))
    (ι : X.functionField →+* K)
    (x : {q : Spec (.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (hx : x.1 ≫ p =
      Spec.map (CommRingCat.ofHom ι) ≫ X.fromSpecStalk (genericPoint X))
    (r : X.functionField) :
    (M.pointEquivPlace x).evalAt (φ r) = ι r := by
  obtain ⟨U, hU, s, hs⟩ := X.presheaf.exists_germ_eq r
  have hne : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  have hxgen : (x.1 ≫ p).base (IsLocalRing.closedPoint K) = genericPoint X := by
    rw [hx]
    change (X.fromSpecStalk (genericPoint X)).base
      ((Spec.map (CommRingCat.ofHom ι)).base (IsLocalRing.closedPoint K)) = _
    rw [AlgebraicGeometry.Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hxU : x.1.base (IsLocalRing.closedPoint K) ∈ p ⁻¹ᵁ U := by
    change (x.1 ≫ p).base (IsLocalRing.closedPoint K) ∈ U
    rw [hxgen]
    exact hU
  have hpre : Nonempty (p ⁻¹ᵁ U) :=
    ⟨⟨x.1.base (IsLocalRing.closedPoint K), hxU⟩⟩
  let w := (M.C.presheaf.germ (p ⁻¹ᵁ U)
    (x.1.base (IsLocalRing.closedPoint K)) hxU).hom ((p.app U).hom s)
  obtain ⟨_, _, heval⟩ :=
    M.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo x w
  have hw : algebraMap _ M.C.functionField w =
      M.C.germToFunctionField (p ⁻¹ᵁ U) ((p.app U).hom s) :=
    M.C.algebraMap_germ_eq_germToFunctionField hxU _
  have hs' : X.germToFunctionField U s = r := hs
  rw [hw] at heval
  rw [← hs', hφ, heval]
  have hcomp :
      (Scheme.stalkClosedPointTo x.1).hom w =
        (X.presheaf.germ U ((x.1 ≫ p).base (IsLocalRing.closedPoint K)) hxU ≫
          Scheme.stalkClosedPointTo (x.1 ≫ p)).hom s := by
    rw [Scheme.stalkClosedPointTo_comp]
    change (Scheme.stalkClosedPointTo x.1).hom w =
      (Scheme.stalkClosedPointTo x.1).hom
        ((p.stalkMap (x.1.base (IsLocalRing.closedPoint K))).hom
          ((X.presheaf.germ U (p.base (x.1.base (IsLocalRing.closedPoint K))) hxU).hom s))
    apply congrArg (Scheme.stalkClosedPointTo x.1).hom
    exact (p.germ_stalkMap_apply U (x.1.base (IsLocalRing.closedPoint K)) hxU s).symm
  rw [hcomp]
  have hsection (q : Spec (.of K) ⟶ X)
      (hq : q = Spec.map (CommRingCat.ofHom ι) ≫ X.fromSpecStalk (genericPoint X))
      (hmem : q.base (IsLocalRing.closedPoint K) ∈ U) :
      (X.presheaf.germ U (q.base (IsLocalRing.closedPoint K)) hmem ≫
        Scheme.stalkClosedPointTo q).hom s = ι (X.germToFunctionField U s) := by
    subst q
    rw [Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk]
    rfl
  exact hsection (x.1 ≫ p) hx hxU

/-- The lifted generic point avoids zeros and poles of every nonzero
original rational function. This supplies support avoidance for the
actual base-changed Kummer divisor. -/
theorem ord_geometricGenericPoint
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme} [IsIntegral X]
    (p : M.C ⟶ X) (φ : X.functionField →+* F)
    (hφ : ∀ (U : X.Opens) [Nonempty U] [Nonempty (p ⁻¹ᵁ U)] (s : Γ(X, U)),
      φ (X.germToFunctionField U s) =
        M.ffEquiv.symm (M.C.germToFunctionField (p ⁻¹ᵁ U) ((p.app U).hom s)))
    (ι : X.functionField →+* K)
    (x : {q : Spec (.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (hx : x.1 ≫ p =
      Spec.map (CommRingCat.ofHom ι) ≫ X.fromSpecStalk (genericPoint X))
    (r : X.functionField) (hr : r ≠ 0) :
    (M.pointEquivPlace x).ord (φ r) = 0 := by
  apply (M.pointEquivPlace x).ord_eq_zero_of_evalAt_ne_zero
    (M.isRational_pointEquivPlace x)
  rw [M.evalAt_geometricGenericPoint p φ hφ ι x hx r]
  exact fun h => hr (ι.injective (h.trans (map_zero ι).symm))

end AlgebraicCurve.CurveModel
