/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.EndDegree
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Mathlib.AlgebraicGeometry.Pullbacks
import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# The full Tate module of algebraic points

The actual torsion levels of the additive group of algebraic points identify
with points of the multiplication kernel. For a proper smooth commutative
group scheme over an algebraically closed field of characteristic zero,
these kernels are finite étale. Thus the full Tate module has finite levels
and is compact in its canonical topology. Its Hausdorff, totally disconnected,
and torsion-free structures are supplied by the general full Tate construction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.P2mSepKer

variable {K : Type} [Field K] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of K)}
variable (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

private theorem comp_nsmul_idPoint {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K))
    (n : ℕ) (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp x (G.nsmul f n idPoint) = G.nsmul t n x := by
  have hid : GoodReductionJacobian.schemeHomOverComp x.1 x.2
      (idPoint : SchemeHomOver f f) = x := by
    apply Subtype.ext
    exact Category.comp_id x.1
  have h := G.nsmul_natural f t x.1 x.2 n idPoint
  rw [hid] at h
  exact h

private def torsionSubsetChangeBase (n : ℕ)
    (t t' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)) (h : t = t') :
    G.torsionSubset t n ≃ G.torsionSubset t' n where
  toFun x := ⟨⟨x.1.1, x.1.2.trans h⟩, by
    subst t'
    exact x.2⟩
  invFun x := ⟨⟨x.1.1, x.1.2.trans h.symm⟩, by
    subst t'
    exact x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The actual torsion subgroup of algebraic points is the point set of the
scheme theoretic multiplication kernel. -/
def torsionLevelEquivSchemeKerPoints (n : ℕ+) :
    ProCGroups.torsionLevel (G.AlgPoints hc K) n ≃
      SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (G.schemeKerStr (n : ℕ)) := by
  let t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K K))
  let e₁ : ProCGroups.torsionLevel (G.AlgPoints hc K) n ≃ G.torsionSubset t (n : ℕ) :=
    (AlgPoints.equivPoint (L := G) (hc := hc) (T := K)).subtypeEquiv
      (fun x => AlgPoints.nsmul_eq_zero_iff (n : ℕ) x)
  have ht : t = 𝟙 (Spec (CommRingCat.of K)) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id K)) = _
    rw [CommRingCat.ofHom_id]
    exact Spec.map_id (CommRingCat.of K)
  let e₂ : G.torsionSubset t (n : ℕ) ≃
      G.torsionSubset (𝟙 (Spec (CommRingCat.of K))) (n : ℕ) :=
    torsionSubsetChangeBase G (n : ℕ) t (𝟙 (Spec (CommRingCat.of K))) ht
  let e₃ : G.torsionSubset (𝟙 (Spec (CommRingCat.of K))) (n : ℕ) ≃
      KerPts G (G.nsmul f (n : ℕ) idPoint) :=
    Equiv.subtypeEquivRight fun x => by
      change G.nsmul _ (n : ℕ) x = G.one _ ↔
        NeronModelInfra.schemeHomOverComp x (G.nsmul f (n : ℕ) idPoint) = G.one _
      rw [comp_nsmul_idPoint]
  exact ((e₁.trans e₂).trans e₃).trans
    (kerPtsEquiv G (G.nsmul f (n : ℕ) idPoint)).symm

/-- The scheme-kernel comparison preserves the underlying point of the group scheme. -/
theorem torsionLevelEquivSchemeKerPoints_comp_fst (n : ℕ+)
    (x : ProCGroups.torsionLevel (G.AlgPoints hc K) n) :
    (G.torsionLevelEquivSchemeKerPoints hc n x).1 ≫
        pullback.fst (G.schemeNsmul (n : ℕ)) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 =
      (AlgPoints.toPoint x.1).1 := by
  change pullback.lift _ (𝟙 _) _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

/-- Properness and smoothness make every positive torsion level finite in
characteristic zero, without any separate finiteness hypothesis on points. -/
theorem finite_torsionLevel [IsAlgClosed K] [CharZero K] [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ+) :
    Finite (ProCGroups.torsionLevel (G.AlgPoints hc K) n) := by
  have hn : IsUnit ((n : ℕ) : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt n.property))
  have : Etale (G.schemeNsmul (n : ℕ)) :=
    G.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension hc d (n : ℕ) hn
  have : Etale (G.endKerStr (G.nsmul f (n : ℕ) idPoint)) :=
    inferInstanceAs (Etale (G.schemeKerStr (n : ℕ)))
  have hfinite : Finite (KerPts G (G.nsmul f (n : ℕ) idPoint)) :=
    (G.isFinite_endKerStr_and_natCard_eq_endDegree_of_etale K f
      (G.nsmul f (n : ℕ) idPoint)).2.1
  have : Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (G.schemeKerStr (n : ℕ))) :=
    Finite.of_equiv _ (kerPtsEquiv G (G.nsmul f (n : ℕ) idPoint)).symm
  exact Finite.of_equiv _ (G.torsionLevelEquivSchemeKerPoints hc n).symm

/-- The full Tate module of actual algebraic points is compact. -/
theorem compactSpace_fullTateModule [IsAlgClosed K] [CharZero K] [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    CompactSpace (ProCGroups.FullTateModule (G.AlgPoints hc K)) := by
  have : ∀ n : ℕ+, Finite (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
    fun n => G.finite_torsionLevel hc d n
  infer_instance

end GoodReductionJacobian.RelativeGroupLaw
