/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.AlbaneseChartGlue
import Nyll.JacobianVarieties.Albanese.FiniteSums
import Nyll.JacobianVarieties.Picard.Exists_abelJacobi_of_representsRelSubPic
import Nyll.JacobianVarieties.Picard.AbelJacobiFamily
import Nyll.JacobianVarieties.Picard.Nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_prodKerGraph
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_IsUniversal_exists_sumMap
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivTwist2
import Nyll.AlgebraicCurves.Geometry.Schemes.prodKerGraph_comap_mapOnProdOver
import Nyll.AlgebraicCurves.Geometry.Schemes.ext_of_forall_comp_eq_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.Data.List.OfFn

/-! # The glued divisor sum factors the actual Abel--Jacobi morphism

Adding copies of the fixed base point makes a single moving point into a divisor
of the degree used in the chart construction. Its normalized line bundle is the
point-minus-basepoint bundle and its sum is the original pointed morphism.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open AlgebraicCurves.RelativeDivisors.Proofs
open RelEffCartierDiv_IsUniversal_exists_sumMap.AlgebraicGeometry
open AlgebraicGeometry.RelPicard.Scheme.IdealSheafData.IsInvertible

namespace JacobianVarieties.Albanese

private def paddedPoints
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K))
    (ε x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) (n : ℕ) :
    Fin (n + 1) → SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c :=
  Fin.cons x (fun _ => ε)

private theorem nonempty_pointsSubBasepointModule_replicate
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsSeparated c]
    [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) (n : ℕ) :
    Nonempty (pointsSubBasepointModule ε (List.replicate n ε) ≅
      𝟙_ (pullback c (𝟙 (Spec (CommRingCat.of K)))).Modules) := by
  induction n with
  | zero => exact ⟨Iso.refl _⟩
  | succ n ih =>
    rw [List.replicate_succ, pointsSubBasepointModule_cons]
    obtain ⟨e⟩ := nonempty_invModule_tensor_module_iso
      (RelEffCartierDiv.ofPoint c ε.1 ε.2).isInvertible_I
    exact ⟨(e ⊗ᵢ ih.some) ≪≫ λ_ _⟩

private theorem sumList_replicate_one
    {K : Type u} [Field K] {B T : Scheme.{u}}
    {b : B ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K b)
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) :
    G.sumList t (List.replicate n (G.one t)) = G.one t := by
  induction n with
  | zero => exact G.sumList_nil t
  | succ n ih => rw [List.replicate_succ, G.sumList_cons, ih, G.one_mul]

private theorem nonempty_padded_twist_iso
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsSeparated c]
    [SmoothOfRelativeDimension 1 c]
    (ε x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) (n : ℕ)
    (D : RelEffCartierDiv c (n + 1) (𝟙 (Spec (CommRingCat.of K))))
    (hD : D.I = prodKerGraph c (fun i => (paddedPoints c ε x n i).1)
      (fun i => (paddedPoints c ε x n i).2)) :
    Nonempty (D.twistModule c ε ≅ pointSubBasepointModule x ε) := by
  have hε : sectionIdeal c ε (𝟙 (Spec (CommRingCat.of K))) =
      (RelEffCartierDiv.ofPoint c ε.1 ε.2).I := by
    change (RelEffCartierDiv.ofPoint c (𝟙 _ ≫ ε.1)
      (by rw [Category.id_comp]; exact ε.2)).I = _
    apply congrArg RelEffCartierDiv.I
    exact AlgebraicGeometry.RelPicard.RelEffCartierDiv.ofPoint_congr
      c (Category.id_comp ε.1) _ _
  have hεI : (sectionIdeal c ε (𝟙 (Spec (CommRingCat.of K)))).IsInvertible := by
    rw [hε]
    exact (RelEffCartierDiv.ofPoint c ε.1 ε.2).isInvertible_I
  let M := D.lineBundle ⊗ ((sectionIdeal c ε (𝟙 (Spec (CommRingCat.of K)))) ^ (n + 1)).module
  have hM : Scheme.Modules.IsInvertible M :=
    D.isInvertible_I.isInvertible_invModule.tensor
      (hεI.pow (n + 1)).isInvertible_module
  obtain ⟨e₀⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_isLocalRing
    (hM.pullback (rigSection c (𝟙 _) ε)).dual.1
  let e₁ : D.twistModule c ε ≅ M :=
    (Iso.refl M ⊗ᵢ ((Scheme.Modules.pullback (pullback.snd c (𝟙 _))).mapIso e₀ ≪≫
      Scheme.Modules.pullbackUnitIso _)) ≪≫ ρ_ M
  obtain ⟨e₂⟩ := nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
    ε (fun i => (paddedPoints c ε x n i).1)
    (fun i => (paddedPoints c ε x n i).2)
  have heM : M = (prodKerGraph c
      (fun i => (paddedPoints c ε x n i).1)
      (fun i => (paddedPoints c ε x n i).2)).invModule ⊗
        ((RelEffCartierDiv.ofPoint c ε.1 ε.2).I ^ (n + 1)).module := by
    change D.I.invModule ⊗ _ = _
    rw [hD, hε]
  have hlist : (List.ofFn fun i : Fin (n + 1) =>
      (⟨(paddedPoints c ε x n i).1,
        (paddedPoints c ε x n i).2⟩ :
          SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)) = x :: List.replicate n ε := by
    rw [List.ofFn_succ]
    simp only [paddedPoints, Fin.cons_zero, Fin.cons_succ, Subtype.coe_eta, List.ofFn_const]
  rw [hlist, pointsSubBasepointModule_cons] at e₂
  exact ⟨e₁ ≪≫ eqToIso heM ≪≫ e₂ ≪≫
    (Iso.refl _ ⊗ᵢ (nonempty_pointsSubBasepointModule_replicate c ε n).some) ≪≫ ρ_ _⟩

private theorem padded_divisor_sum
    {K : Type u} [Field K] {C B Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsSeparated c]
    (ε x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) (n : ℕ)
    {y : Y ⟶ Spec (CommRingCat.of K)} {U : RelEffCartierDiv c (n + 1) y}
    (hU : U.IsUniversal) (σ : finFibrePow c (n + 1) ⟶ Y)
    (hσ : σ ≫ y = finFibrePow.toBase c (n + 1))
    (hI : U.I.comap (mapOnProdOver c σ hσ) = fibrePowOver.tautIdeal c (n + 1))
    {b : B ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K b)
    (q : SchemeHomOver c b) (hq : NeronModelInfra.schemeHomOverComp ε q = G.one (𝟙 _))
    (sum : SchemeHomOver y b) (hsum : σ ≫ sum.1 = (G.finiteSumMap c q (n + 1)).1)
    (D : RelEffCartierDiv c (n + 1) (𝟙 (Spec (CommRingCat.of K))))
    (hD : D.I = prodKerGraph c (fun i => (paddedPoints c ε x n i).1)
      (fun i => (paddedPoints c ε x n i).2)) :
    hU.lift D ≫ sum.1 = x.1 ≫ q.1 := by
  let xs : Fin (n + 1) → SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c :=
    paddedPoints c ε x n
  let v : Spec (CommRingCat.of K) ⟶ finFibrePow c (n + 1) :=
    WidePullback.lift (𝟙 _) (fun i => (xs i).1) (fun i => (xs i).2)
  have hv : v ≫ finFibrePow.toBase c (n + 1) = 𝟙 _ := WidePullback.lift_base _ _ _ _
  have hvs : (v ≫ σ) ≫ y = 𝟙 _ := by rw [Category.assoc, hσ, hv]
  have hlift : hU.lift D = v ≫ σ := by
    symm
    apply hU.eq_lift hvs
    have hcomp := congrArg RelEffCartierDiv.I (U.pullbackAlong_comp σ hσ v hv)
    change (U.pullbackAlong (v ≫ σ) hvs).I = D.I
    rw [← hcomp]
    change (U.I.comap (mapOnProdOver c σ hσ)).comap (mapOnProdOver c v hv) = D.I
    rw [hI, fibrePowOver.tautIdeal, prodKerGraph_comap_mapOnProdOver, hD]
    exact prodKerGraph_congr c (funext fun i => WidePullback.lift_π _ _ _ _ _) _ _
  have heval := congrArg Subtype.val (G.finiteSumMap_evaluate c q (𝟙 _) xs)
  change v ≫ (G.finiteSumMap c q (n + 1)).1 =
    (G.sumList (𝟙 _) (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (xs i) q)).1 at heval
  have hxq : (fun i => NeronModelInfra.schemeHomOverComp (xs i) q) =
      Fin.cons (NeronModelInfra.schemeHomOverComp x q)
        (fun _ : Fin n => G.one (𝟙 (Spec (CommRingCat.of K)))) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact hq
  rw [hlift, Category.assoc, hsum, heval, hxq, List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, List.ofFn_const]
  rw [G.sumList_cons, sumList_replicate_one, G.mul_one]
  rfl

/-- Over an algebraically closed field the actual point-minus-basepoint
Abel--Jacobi morphism factors every pointed morphism to a smooth proper
geometrically integral group scheme. The factor is built from actual divisor
sums, without a factorization or comparison assumption. -/
theorem exists_abelJacobi_factorization_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (P : RelativePic0Designation K c) [LocallyOfFiniteType P.toBase] [IsReduced P.P]
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) P) :
    ∃ aj : SchemeHomOver c P.toBase,
      ε.1 ≫ aj.1 = P.zeroSection ∧
      (∀ (L : Type u) [Field L] (t : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
        (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
          ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans
                ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule)) ∧
      ∀ (B : Scheme.{u}) (b : B ⟶ Spec (CommRingCat.of K)) [Smooth b] [IsProper b]
        [GeometricallyIntegral b] (G : RelativeGroupLaw K b) (q : SchemeHomOver c b),
        NeronModelInfra.schemeHomOverComp ε q = G.one (𝟙 _) →
          ∃ ψ : SchemeHomOver P.toBase b, aj.1 ≫ ψ.1 = q.1 := by
  obtain ⟨aj, haj, hclass⟩ := exists_abelJacobi_of_representsRelSubPic K c ε P h
  refine ⟨aj, haj, hclass, ?_⟩
  intro B b _ _ _ G q hq
  obtain ⟨r, hr, Y, y, U, hU, σ, hσ, sum, ψ, hI, hsum, hψ⟩ :=
    exists_divisorSum_glue c ε h G q
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  refine ⟨ψ, ?_⟩
  apply ext_of_forall_comp_eq_of_isAlgClosed c b
    (by rw [Category.assoc, ψ.2, aj.2]) q.2
  intro x hx
  let z : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c := ⟨x, hx⟩
  obtain ⟨D, hD⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph
    (fun i => (paddedPoints c ε z n i).1)
    (fun i => (paddedPoints c ε z n i).2)
  obtain ⟨eD⟩ := nonempty_padded_twist_iso c ε z n D hD
  obtain ⟨eaj⟩ := hclass K (𝟙 (Spec (CommRingCat.of K))) z
  have heaj : (h.poincare.pullbackAlong
      (⟨x ≫ aj.1, by rw [Category.assoc, aj.2, hx]⟩ :
        SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) P.toBase)).L ≅
        pointSubBasepointModule z ε := by
    simpa only [Category.id_comp] using eaj
  have hp := hψ _ (𝟙 (Spec (CommRingCat.of K))) D
    ⟨x ≫ aj.1, by rw [Category.assoc, aj.2, hx]⟩ ⟨eD ≪≫ heaj.symm⟩
  rw [Category.assoc] at hp
  exact hp.trans (padded_divisor_sum c ε z n hU σ hσ hI G q hq sum hsum D hD)

end JacobianVarieties.Albanese
