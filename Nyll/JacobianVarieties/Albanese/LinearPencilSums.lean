/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.SameDivisorDescent
import Nyll.JacobianVarieties.Albanese.FiniteSums
import Nyll.AlgebraicCurves.RelativeDivisors.LinearPencilDivisor
import Nyll.AlgebraicCurves.RelativeDivisors.LinearPencilSections
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_isUniversal
import Nyll.AlgebraicCurves.Models.Exists_isAffineOpen_forall_mem_of_finset_of_field
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AffineLineConstancy
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_unique_section_of_pullbackSection_closedCover
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIrreducible_geometricallyConnected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!+# Finite sums are constant along an actual linear pencil

The independent pencil supplies a relative divisor over the affine line. Its
actual classifying morphism into the universal divisor scheme, followed by the
descended finite sum, is constant. The parameter fibres retain the same degree
and their ideals are identified with the original linear combinations.
For nonzero dependent sections, the ground-field scalar is a unit and the
two actual zero-scheme ideals coincide.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.LinearPencil
open NeronModelInfra GoodReductionJacobian
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_exists_unique_section_of_pullbackSection_closedCover
open AlgebraicGeometry.Scheme.Modules.GlueSect

namespace JacobianVarieties.Albanese

private theorem exists_universal_over_field
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] (r : ℕ) :
    ∃ (Y : Scheme.{u}) (y : Y ⟶ Spec (CommRingCat.of K))
      (U : RelEffCartierDiv c r y), U.IsUniversal := by
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  apply RelEffCartierDiv.exists_isUniversal c ?_ r
  intro V F hF
  by_cases hV : (V : (Spec (CommRingCat.of K)).Opens) = ⊥
  · refine ⟨⊥, isAffineOpen_bot C, bot_le, ?_⟩
    intro x hx
    have h := hF x hx
    rw [hV] at h
    exact h
  · have hne : ((V : (Spec (CommRingCat.of K)).Opens) :
        Set (Spec (CommRingCat.of K))).Nonempty := by
      apply Set.nonempty_iff_ne_empty.mpr
      intro h
      exact hV (SetLike.ext' h)
    obtain ⟨t, ht⟩ := hne
    have hVtop : (V : (Spec (CommRingCat.of K)).Opens) = ⊤ := by
      apply top_unique
      intro t' _
      exact (Subsingleton.elim t t') ▸ ht
    obtain ⟨W, hW, hFW⟩ := AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset_of_field c F
    refine ⟨W, hW, ?_, hFW⟩
    rw [hVtop]
    exact le_top

private theorem lift_pullbackAlong
    {C S Y T T' : Scheme.{u}} {c : C ⟶ S} {r : ℕ}
    {y : Y ⟶ S} {U : RelEffCartierDiv c r y} (hU : U.IsUniversal)
    {g : T ⟶ S} (D : RelEffCartierDiv c r g)
    {g' : T' ⟶ S} (φ : T' ⟶ T) (hφ : φ ≫ g = g') :
    hU.lift (D.pullbackAlong φ hφ) = φ ≫ hU.lift D := by
  symm
  apply hU.eq_lift (by rw [Category.assoc, hU.lift_comp, hφ])
  have h : U.pullbackAlong (φ ≫ hU.lift D)
      (by rw [Category.assoc, hU.lift_comp, hφ]) = D.pullbackAlong φ hφ := by
    rw [← U.pullbackAlong_comp (hU.lift D) (hU.lift_comp D) φ hφ,
      hU.pullbackAlong_lift]
  exact congrArg RelEffCartierDiv.I h

/-- The ideal of a parameter fibre, transported from `C × Spec K` back to `C`.
The fibre divisor has exactly the degree of the pencil. -/
theorem pencilDivisor_fibre_ideal
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (M : C.Modules)
    (hM : Scheme.Modules.IsInvertible M) (v : Fin 2 → Γ(M, ⊤))
    {r : ℕ} (P : RelEffCartierDiv c r lineMap)
    (hP : P.I = Scheme.Modules.zeroSchemeIdeal (pencilMorphism c M v)) (a : K) :
    (P.pullbackAlong (evaluate a) (evaluate_comp_lineMap a)).I.comap
        (inv (pullback.fst c (𝟙 (Spec (CommRingCat.of K))))) =
      Scheme.Modules.zeroSchemeIdeal (homOfGsec
        ((1 - c.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) • v 0 +
          c.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a) • v 1)) := by
  have hmap : inv (pullback.fst c (𝟙 (Spec (CommRingCat.of K)))) ≫
      mapOnProdOver c (evaluate a) (evaluate_comp_lineMap a) = fibre c a := by
    apply pullback.hom_ext
    · rw [Category.assoc, mapOnProdOver_fst, IsIso.inv_hom_id, fibre_fst]
    · rw [Category.assoc, mapOnProdOver_snd, fibre_snd]
      have hsnd : pullback.snd c (𝟙 (Spec (CommRingCat.of K))) =
          pullback.fst c (𝟙 _) ≫ c := by
        simpa only [Category.comp_id] using (pullback.condition (f := c) (g := 𝟙 _)).symm
      rw [hsnd, ← Category.assoc, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  change (P.I.comap _).comap _ = _
  rw [← Scheme.IdealSheafData.comap_comp, hmap, hP]
  exact zeroSchemeIdeal_pencilMorphism_fibre c M hM v a

/-- The two endpoint divisors have the original zero ideals, and both have
the degree `r` of the actual pencil divisor. -/
theorem pencilDivisor_endpoint_ideals
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (M : C.Modules)
    (hM : Scheme.Modules.IsInvertible M) (v : Fin 2 → Γ(M, ⊤))
    {r : ℕ} (P : RelEffCartierDiv c r lineMap)
    (hP : P.I = Scheme.Modules.zeroSchemeIdeal (pencilMorphism c M v)) :
    (P.pullbackAlong (evaluate (0 : K)) (evaluate_comp_lineMap 0)).I.comap
        (inv (pullback.fst c (𝟙 (Spec (CommRingCat.of K))))) =
      Scheme.Modules.zeroSchemeIdeal (homOfGsec (v 0)) ∧
    (P.pullbackAlong (evaluate (1 : K)) (evaluate_comp_lineMap 1)).I.comap
        (inv (pullback.fst c (𝟙 (Spec (CommRingCat.of K))))) =
      Scheme.Modules.zeroSchemeIdeal (homOfGsec (v 1)) := by
  constructor
  · rw [pencilDivisor_fibre_ideal c M hM v P hP, map_zero, map_zero, sub_zero,
      one_smul, zero_smul, add_zero]
  · rw [pencilDivisor_fibre_ideal c M hM v P hP, map_one, map_one, sub_self,
      zero_smul, one_smul, zero_add]

/-- Two nonzero dependent sections of the same invertible module differ by a
unit from the ground field, so their actual zero-scheme ideals coincide. -/
theorem zeroSchemeIdeal_eq_of_dependent_sections
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (M : C.Modules)
    (hM : Scheme.Modules.IsInvertible M) :
    let : Algebra K Γ(C, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop).hom.toAlgebra
    let : Module K Γ(M, ⊤) := Module.compHom _ (algebraMap K Γ(C, ⊤))
    ∀ (v : Fin 2 → Γ(M, ⊤)), v 0 ≠ 0 → v 1 ≠ 0 →
      ¬ LinearIndependent K v →
      Scheme.Modules.zeroSchemeIdeal (homOfGsec (v 0)) =
        Scheme.Modules.zeroSchemeIdeal (homOfGsec (v 1)) := by
  intro algK modK v h0 h1 hv
  classical
  have hn : ¬ ∀ a : K, a • v 1 ≠ v 0 := by
    intro h
    exact hv (linearIndependent_fin2.mpr ⟨h1, h⟩)
  obtain ⟨a, ha⟩ := not_forall.mp hn
  have heq : a • v 1 = v 0 := not_not.mp ha
  have ha0 : a ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at heq
    exact h0 heq.symm
  have hu : IsUnit (algebraMap K Γ(C, ⊤) a) :=
    (isUnit_iff_ne_zero.mpr ha0).map (algebraMap K Γ(C, ⊤))
  symm
  apply hM.zeroSchemeIdeal_eq_of_app_eq_smul (homOfGsec (v 1)) (homOfGsec (v 0))
    (algebraMap K Γ(C, ⊤) a) hu
  change gsec (homOfGsec (v 0)) = algebraMap K Γ(C, ⊤) a • gsec (homOfGsec (v 1))
  rw [gsec_homOfGsec, gsec_homOfGsec]
  exact heq.symm

/-- An independent pencil has an actual universal classifying map and a descended
finite sum whose values on all parameter fibres are equal. No divisor
representability or linear-equivalence invariance is assumed. -/
theorem exists_pencilSum
    {K : Type u} [Field K] {C B : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (s : Spec (CommRingCat.of K) ⟶ C) (hs : s ≫ c = 𝟙 _)
    {b : B ⟶ Spec (CommRingCat.of K)} [Smooth b] [IsProper b]
    [GeometricallyIntegral b] (G : RelativeGroupLaw K b) (q : SchemeHomOver c b)
    (M : C.Modules) (hM : Scheme.Modules.IsInvertible M) :
    let : Algebra K Γ(C, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop).hom.toAlgebra
    let : Module K Γ(M, ⊤) := Module.compHom _ (algebraMap K Γ(C, ⊤))
    ∀ (v : Fin 2 → Γ(M, ⊤)), LinearIndependent K v →
      ∃ (r : ℕ) (P : RelEffCartierDiv c r lineMap)
        (Y : Scheme.{u}) (y : Y ⟶ Spec (CommRingCat.of K))
        (U : RelEffCartierDiv c r y) (hU : U.IsUniversal)
        (σ : finFibrePow c r ⟶ Y) (hσ : σ ≫ y = finFibrePow.toBase c r)
        (sum : SchemeHomOver y b),
        P.I = Scheme.Modules.zeroSchemeIdeal (pencilMorphism c M v) ∧
        U.I.comap (mapOnProdOver c σ hσ) = fibrePowOver.tautIdeal c r ∧
        σ ≫ sum.1 = (G.finiteSumMap c q r).1 ∧
        (∀ (a a' : K),
          hU.lift (P.pullbackAlong (evaluate a) (evaluate_comp_lineMap a)) ≫ sum.1 =
          hU.lift (P.pullbackAlong (evaluate a') (evaluate_comp_lineMap a')) ≫ sum.1) := by
  intro algK modK v hv
  have : GeometricallyConnected c := GeometricallyIrreducible.geometricallyConnected c
  have : GeometricallyConnected b := GeometricallyIrreducible.geometricallyConnected b
  obtain ⟨r, P, hP, -⟩ := exists_pencilDivisor c M hM v hv
  obtain ⟨Y, y, U, hU⟩ := exists_universal_over_field c r
  obtain ⟨σ, hσ, sum, hI, -, -, -, hsum, -⟩ :=
    exists_finiteSumMap_desc c s hs G q hU
  let hB : GoodReductionJacobian.AbelianSchemePropertyBundle K b :=
    ⟨inferInstance, inferInstance, b.isConnected_preimage_singleton, ⟨G⟩⟩
  have hbase : (hU.lift P ≫ sum.1) ≫ b =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))) := by
    rw [Category.assoc, sum.2, hU.lift_comp]
    rfl
  obtain ⟨a₀, -, hconst⟩ := GoodReductionJacobian.exists_eq_const_of_affineLine K hB
    (hU.lift P ≫ sum.1) hbase
  change hU.lift P ≫ sum.1 = lineMap ≫ a₀ at hconst
  refine ⟨r, P, Y, y, U, hU, σ, hσ, sum, hP, hI, hsum, ?_⟩
  intro a a'
  rw [lift_pullbackAlong, lift_pullbackAlong, Category.assoc, Category.assoc,
    hconst, ← Category.assoc, ← Category.assoc, evaluate_comp_lineMap,
    evaluate_comp_lineMap]

end JacobianVarieties.Albanese
