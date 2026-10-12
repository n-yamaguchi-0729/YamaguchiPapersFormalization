/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.FiniteSums
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.JacobianVarieties.Picard.AbelJacobiFamily
import Nyll.JacobianVarieties.Picard.Nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_prodKerGraph
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_IsUniversal_exists_sumMap
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivTwist2
import Nyll.AlgebraicCurves.Geometry.Schemes.prodKerGraph_comap_mapOnProdOver
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Mathlib.Data.List.OfFn

/-! # Padding a geometric point by the basepoint

The actual effective divisor `x + n ε` over any field-valued test scheme has
normalized line bundle `O(x - ε)`. Its actual divisor sum evaluates to `q(x)`
when `q` sends the basepoint to the identity.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
open GoodReductionJacobian
open AlgebraicCurves.RelativeDivisors.Proofs
open RelEffCartierDiv_IsUniversal_exists_sumMap.AlgebraicGeometry
open AlgebraicGeometry.RelPicard.Scheme.IdealSheafData.IsInvertible
open JacobianVarieties.Picard.Proofs
open Nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
open AlgebraicGeometry.RelPicard.TensorList

namespace JacobianVarieties.Albanese

/-- A field-valued point padded with copies of the basepoint is an actual
effective divisor with the expected point-minus-basepoint normalized bundle. -/
theorem exists_padded_divisor_twist_iso_of_fieldMap
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsSeparated c]
    [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (L : Type u) [Field L] (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver s c) (n : ℕ) :
    let ζ : SchemeHomOver s c :=
      ⟨s ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
    let points : Fin (n + 1) → SchemeHomOver s c := Fin.cons x (fun _ => ζ)
    ∃ D : RelEffCartierDiv c (n + 1) s,
      D.I = prodKerGraph c (fun i => (points i).1) (fun i => (points i).2) ∧
      Nonempty (D.twistModule c ε ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c ζ.1 ζ.2).idealModule) := by
  intro ζ points
  obtain ⟨D, hD⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph
    (fun i => (points i).1) (fun i => (points i).2)
  refine ⟨D, hD, ?_⟩
  let Ix := (RelEffCartierDiv.ofPoint c x.1 x.2).I
  let Iε := (RelEffCartierDiv.ofPoint c ζ.1 ζ.2).I
  have hxI : Ix.IsInvertible := (RelEffCartierDiv.ofPoint c x.1 x.2).isInvertible_I
  have hεI : Iε.IsInvertible := (RelEffCartierDiv.ofPoint c ζ.1 ζ.2).isInvertible_I
  have hpI : (Iε ^ n).IsInvertible := hεI.pow n
  have hsection : sectionIdeal c ε s = Iε := rfl
  have hsI : (sectionIdeal c ε s).IsInvertible := by
    rw [hsection]
    exact hεI
  have hprod : D.I = Ix * Iε ^ n := by
    rw [hD, prodKerGraph_eq_prod, Fin.prod_univ_succ]
    simp only [points, Fin.cons_zero, Fin.cons_succ]
    change Ix * (∏ _ : Fin n, Iε) = Ix * Iε ^ n
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  let M := D.lineBundle ⊗ (sectionIdeal c ε s ^ (n + 1)).module
  have hM : Scheme.Modules.IsInvertible M :=
    D.isInvertible_I.isInvertible_invModule.tensor
      (hsI.pow (n + 1)).isInvertible_module
  obtain ⟨e₀⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_isLocalRing
    (hM.pullback (rigSection c s ε)).dual.1
  let e₁ : D.twistModule c ε ≅ M :=
    (Iso.refl M ⊗ᵢ ((Scheme.Modules.pullback (pullback.snd c s)).mapIso e₀ ≪≫
      Scheme.Modules.pullbackUnitIso _)) ≪≫ ρ_ M
  obtain ⟨e₂⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor
      hxI hpI
  obtain ⟨e₃⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor
      hεI hpI
  obtain ⟨e₄⟩ := nonempty_invModule_tensor_module_iso hpI
  have hM' : M = (Ix * Iε ^ n).invModule ⊗ (Iε * Iε ^ n).module := by
    change D.I.invModule ⊗ _ = _
    rw [hprod, hsection, pow_succ']
  exact ⟨e₁ ≪≫ eqToIso hM' ≪≫ (e₂ ⊗ᵢ e₃) ≪≫ shuffle _ _ _ _ ≪≫
    (Iso.refl _ ⊗ᵢ e₄) ≪≫ ρ_ _⟩

private theorem sumList_replicate_one
    {K : Type u} [Field K] {B T : Scheme.{u}}
    {b : B ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K b)
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) :
    G.sumList t (List.replicate n (G.one t)) = G.one t := by
  induction n with
  | zero => exact G.sumList_nil t
  | succ n ih => rw [List.replicate_succ, G.sumList_cons, ih, G.one_mul]

/-- The actual universal-divisor sum on the padded geometric-point divisor is
the value of the pointed curve morphism at that point. -/
theorem padded_divisor_sum_of_fieldMap
    {K : Type u} [Field K] {C B Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (L : Type u) [Field L] (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver s c) (n : ℕ)
    {y : Y ⟶ Spec (CommRingCat.of K)} {U : RelEffCartierDiv c (n + 1) y}
    (hU : U.IsUniversal) (σ : finFibrePow c (n + 1) ⟶ Y)
    (hσ : σ ≫ y = finFibrePow.toBase c (n + 1))
    (hI : U.I.comap (mapOnProdOver c σ hσ) = fibrePowOver.tautIdeal c (n + 1))
    {b : B ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K b)
    (q : SchemeHomOver c b) (hq : NeronModelInfra.schemeHomOverComp ε q = G.one (𝟙 _))
    (sum : SchemeHomOver y b) (hsum : σ ≫ sum.1 = (G.finiteSumMap c q (n + 1)).1) :
    let ζ : SchemeHomOver s c :=
      ⟨s ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
    let points : Fin (n + 1) → SchemeHomOver s c := Fin.cons x (fun _ => ζ)
    ∀ D : RelEffCartierDiv c (n + 1) s,
      D.I = prodKerGraph c (fun i => (points i).1) (fun i => (points i).2) →
      hU.lift D ≫ sum.1 = x.1 ≫ q.1 := by
  intro ζ points D hD
  let v : Spec (CommRingCat.of L) ⟶ finFibrePow c (n + 1) :=
    WidePullback.lift s (fun i => (points i).1) (fun i => (points i).2)
  have hv : v ≫ finFibrePow.toBase c (n + 1) = s := WidePullback.lift_base _ _ _ _
  have hvs : (v ≫ σ) ≫ y = s := by rw [Category.assoc, hσ, hv]
  have hlift : hU.lift D = v ≫ σ := by
    symm
    apply hU.eq_lift hvs
    have hcomp := congrArg RelEffCartierDiv.I (U.pullbackAlong_comp σ hσ v hv)
    change (U.pullbackAlong (v ≫ σ) hvs).I = D.I
    rw [← hcomp]
    change (U.I.comap (mapOnProdOver c σ hσ)).comap (mapOnProdOver c v hv) = D.I
    rw [hI, fibrePowOver.tautIdeal, prodKerGraph_comap_mapOnProdOver, hD]
    exact prodKerGraph_congr c (funext fun i => WidePullback.lift_π _ _ _ _ _) _ _
  have hζq : NeronModelInfra.schemeHomOverComp ζ q = G.one s := by
    apply Subtype.ext
    change (s ≫ ε.1) ≫ q.1 = (G.one s).1
    have hbase : ε.1 ≫ q.1 = (G.one (𝟙 _)).1 := congrArg Subtype.val hq
    rw [Category.assoc, hbase]
    exact congrArg Subtype.val (G.one_natural (𝟙 _) s s (Category.comp_id s))
  have heval := congrArg Subtype.val (G.finiteSumMap_evaluate c q s points)
  change v ≫ (G.finiteSumMap c q (n + 1)).1 =
    (G.sumList s (List.ofFn fun i =>
      NeronModelInfra.schemeHomOverComp (points i) q)).1 at heval
  have hxq : (fun i => NeronModelInfra.schemeHomOverComp (points i) q) =
      Fin.cons (NeronModelInfra.schemeHomOverComp x q)
        (fun _ : Fin n => G.one s) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact hζq
  rw [hlift, Category.assoc, hsum, heval, hxq, List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, List.ofFn_const]
  rw [G.sumList_cons, sumList_replicate_one, G.mul_one]
  rfl

end JacobianVarieties.Albanese
