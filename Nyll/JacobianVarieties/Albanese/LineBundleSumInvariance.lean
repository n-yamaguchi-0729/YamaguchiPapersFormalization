/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.LinearPencilSums
import Nyll.JacobianVarieties.Albanese.SameDivisorDescent
import Nyll.JacobianVarieties.Albanese.FiniteSums
import Nyll.AlgebraicCurves.RelativeDivisors.LinearPencilDivisor
import Nyll.AlgebraicCurves.RelativeDivisors.LinearPencilSections
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_unique_section_of_pullbackSection_closedCover
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AffineLineConstancy
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIrreducible_geometricallyConnected
import Nyll.SchemeTheory.Modules.Invertible
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!+# Finite sums depend only on the line bundle of an effective divisor

The universal divisor scheme is fixed throughout. Canonical divisor sections,
transported to a common invertible module, either define an independent pencil
or differ by a ground-field unit. In the pencil case the actual endpoint ideal
identifies its finite-flat rank with the prescribed degree.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.LinearPencil
open NeronModelInfra GoodReductionJacobian
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_exists_unique_section_of_pullbackSection_closedCover
open AlgebraicGeometry.Scheme.Modules.GlueSect
open AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal

namespace JacobianVarieties.Albanese

private theorem comap_injective_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Function.Injective (fun I : Y.IdealSheafData => I.comap f) := by
  intro I J h
  have h' := congrArg (fun L : X.IdealSheafData => L.comap (inv f)) h
  simpa only [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
    Scheme.IdealSheafData.comap_id] using h'

private theorem invertible_ideal_ne_bot {X : Scheme.{u}} [Nonempty X]
    {I : X.IdealSheafData} (hI : I.IsInvertible) : I ≠ ⊥ := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, f, hx, a, ha, hgen⟩ := hI x
  have hn : Nonempty (X.basicOpen f) := ⟨⟨x, hx⟩⟩
  have : Nontrivial Γ(X, X.affineBasicOpen f) :=
    Scheme.component_nontrivial X (X.basicOpen f)
  have hm : a ∈ I.ideal (X.affineBasicOpen f) := by
    rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton a)
  rw [h] at hm
  exact nonZeroDivisors.ne_zero ha (Ideal.mem_bot.mp hm)

private theorem gsec_ne_zero_of_zeroSchemeIdeal
    {X : Scheme.{u}} [Nonempty X] {M : X.Modules}
    (t : 𝟙_ X.Modules ⟶ M) {I : X.IdealSheafData}
    (hI : I.IsInvertible) (ht : Scheme.Modules.zeroSchemeIdeal t = I) :
    gsec t ≠ 0 := by
  intro hz
  have ht0 : t = 0 := by
    apply hom_ext_of_gsec_eq
    change gsec t = (0 : 𝟙_ X.Modules ⟶ M).app ⊤
      (Scheme.Modules.toUnitSection ⊤ 1)
    rw [hz]
    rfl
  have hbot : I = ⊥ := by
    rw [← ht, ht0]
    exact EmptyIdealSupportIntersection.P2mAvoid.zeroSchemeIdeal_zero
  exact invertible_ideal_ne_bot hI hbot

private theorem homOfGsec_gsec {X : Scheme.{u}} {M : X.Modules}
    (t : 𝟙_ X.Modules ⟶ M) : homOfGsec (gsec t) = t := by
  apply hom_ext_of_gsec_eq
  exact gsec_homOfGsec (gsec t)

private theorem degree_eq_of_ideal_eq
    {K : Type u} [Field K] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of K)} {r d : ℕ}
    (D : RelEffCartierDiv c r (𝟙 (Spec (CommRingCat.of K))))
    (E : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
    (h : D.I = E.I) : r = d := by
  let x : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  calc
    r = (D.I.subschemeι ≫ pullback.snd c (𝟙 _)).finrank x := (D.finrank_eq x).symm
    _ = (E.I.subschemeι ≫ pullback.snd c (𝟙 _)).finrank x := by rw [h]
    _ = d := E.finrank_eq x

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

private theorem pencil_fibres_comp_eq
    {K : Type u} [Field K] {C B Y : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of K)} {r : ℕ}
    {y : Y ⟶ Spec (CommRingCat.of K)} {U : RelEffCartierDiv c r y}
    (hU : U.IsUniversal)
    {b : B ⟶ Spec (CommRingCat.of K)} [Smooth b] [IsProper b]
    [GeometricallyIntegral b] (G : RelativeGroupLaw K b) (sum : SchemeHomOver y b)
    (P : RelEffCartierDiv c r lineMap) (a a' : K) :
    hU.lift (P.pullbackAlong (evaluate a) (evaluate_comp_lineMap a)) ≫ sum.1 =
      hU.lift (P.pullbackAlong (evaluate a') (evaluate_comp_lineMap a')) ≫ sum.1 := by
  have : GeometricallyConnected b := GeometricallyIrreducible.geometricallyConnected b
  let hB : AbelianSchemePropertyBundle K b :=
    ⟨inferInstance, inferInstance, b.isConnected_preimage_singleton, ⟨G⟩⟩
  have hbase : (hU.lift P ≫ sum.1) ≫ b =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))) := by
    rw [Category.assoc, sum.2, hU.lift_comp]
    rfl
  obtain ⟨a₀, -, hconst⟩ := exists_eq_const_of_affineLine K hB
    (hU.lift P ≫ sum.1) hbase
  change hU.lift P ≫ sum.1 = lineMap ≫ a₀ at hconst
  rw [lift_pullbackAlong, lift_pullbackAlong, Category.assoc, Category.assoc,
    hconst, ← Category.assoc, ← Category.assoc, evaluate_comp_lineMap,
    evaluate_comp_lineMap]

/-- A morphism from the universal degree-`r` divisor scheme to an abelian scheme
has equal values on two effective divisors with isomorphic actual line bundles.
The assertion holds over every field, without a rational-point hypothesis. -/
theorem lift_comp_eq_of_lineBundle_iso
    {K : Type u} [Field K] {C B Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {r : ℕ} {y : Y ⟶ Spec (CommRingCat.of K)}
    {U : RelEffCartierDiv c r y} (hU : U.IsUniversal)
    {b : B ⟶ Spec (CommRingCat.of K)} [Smooth b] [IsProper b]
    [GeometricallyIntegral b] (G : RelativeGroupLaw K b) (sum : SchemeHomOver y b)
    (D₀ D₁ : RelEffCartierDiv c r (𝟙 (Spec (CommRingCat.of K))))
    (e : D₀.lineBundle ≅ D₁.lineBundle) :
    hU.lift D₀ ≫ sum.1 = hU.lift D₁ ≫ sum.1 := by
  classical
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  let j : C ⟶ pullback c (𝟙 (Spec (CommRingCat.of K))) := inv (pullback.fst c (𝟙 _))
  let M : C.Modules := (Scheme.Modules.pullback j).obj D₀.lineBundle
  have hM : Scheme.Modules.IsInvertible M :=
    D₀.isInvertible_I.isInvertible_invModule.pullback j
  let t₀ : 𝟙_ C.Modules ⟶ M := Scheme.Modules.pullbackSection j D₀.I.invModuleSection
  let t₁ : 𝟙_ C.Modules ⟶ M :=
    Scheme.Modules.pullbackSection j (D₁.I.invModuleSection ≫ e.inv)
  have hz₀ : Scheme.Modules.zeroSchemeIdeal t₀ = D₀.I.comap j := by
    change Scheme.Modules.zeroSchemeIdeal
      (Scheme.Modules.pullbackSection j D₀.I.invModuleSection) = _
    rw [← D₀.isInvertible_I.isInvertible_invModule.comap_zeroSchemeIdeal,
      D₀.isInvertible_I.zeroSchemeIdeal_invModuleSection]
  have hz₁ : Scheme.Modules.zeroSchemeIdeal t₁ = D₁.I.comap j := by
    change Scheme.Modules.zeroSchemeIdeal
      (Scheme.Modules.pullbackSection j (D₁.I.invModuleSection ≫ e.inv)) = _
    rw [← D₀.isInvertible_I.isInvertible_invModule.comap_zeroSchemeIdeal,
      Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
      D₁.isInvertible_I.zeroSchemeIdeal_invModuleSection]
  have hinv₀ : (D₀.I.comap j).IsInvertible :=
    ZDHeadG.isInvertible_comap_of_isIso D₀.isInvertible_I j
  have hinv₁ : (D₁.I.comap j).IsInvertible :=
    ZDHeadG.isInvertible_comap_of_isIso D₁.isInvertible_I j
  let v : Fin 2 → Γ(M, ⊤) := ![gsec t₀, gsec t₁]
  let algK : Algebra K Γ(C, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop).hom.toAlgebra
  let modK : Module K Γ(M, ⊤) := Module.compHom _ (algebraMap K Γ(C, ⊤))
  have hv₀ : v 0 ≠ 0 := gsec_ne_zero_of_zeroSchemeIdeal t₀ hinv₀ hz₀
  have hv₁ : v 1 ≠ 0 := gsec_ne_zero_of_zeroSchemeIdeal t₁ hinv₁ hz₁
  have hideal₀ : Scheme.Modules.zeroSchemeIdeal (homOfGsec (v 0)) = D₀.I.comap j := by
    change Scheme.Modules.zeroSchemeIdeal (homOfGsec (gsec t₀)) = _
    rw [homOfGsec_gsec, hz₀]
  have hideal₁ : Scheme.Modules.zeroSchemeIdeal (homOfGsec (v 1)) = D₁.I.comap j := by
    change Scheme.Modules.zeroSchemeIdeal (homOfGsec (gsec t₁)) = _
    rw [homOfGsec_gsec, hz₁]
  by_cases hv : LinearIndependent K v
  · obtain ⟨d, P, hP, -⟩ := exists_pencilDivisor c M hM v hv
    obtain ⟨h₀, h₁⟩ := pencilDivisor_endpoint_ideals c M hM v P hP
    have he₀ : (P.pullbackAlong (evaluate (0 : K)) (evaluate_comp_lineMap 0)).I = D₀.I :=
      comap_injective_of_isIso j (h₀.trans hideal₀)
    have he₁ : (P.pullbackAlong (evaluate (1 : K)) (evaluate_comp_lineMap 1)).I = D₁.I :=
      comap_injective_of_isIso j (h₁.trans hideal₁)
    have hd : d = r := degree_eq_of_ideal_eq _ D₀ he₀
    subst d
    have hD₀ : P.pullbackAlong (evaluate (0 : K)) (evaluate_comp_lineMap 0) = D₀ :=
      RelEffCartierDiv.ext he₀
    have hD₁ : P.pullbackAlong (evaluate (1 : K)) (evaluate_comp_lineMap 1) = D₁ :=
      RelEffCartierDiv.ext he₁
    rw [← hD₀, ← hD₁]
    exact pencil_fibres_comp_eq hU G sum P 0 1
  · have he : D₀.I = D₁.I := comap_injective_of_isIso j
      (hideal₀.symm.trans ((zeroSchemeIdeal_eq_of_dependent_sections c M hM v hv₀ hv₁ hv).trans
        hideal₁))
    rw [RelEffCartierDiv.ext he]

/-- The actual finite sum descends uniquely to the fixed universal divisor
scheme and takes the same value on effective divisors with isomorphic line
bundles. The field and the degree are arbitrary. -/
theorem exists_unique_finiteSumMap_desc_lineBundle_invariant
    {K : Type u} [Field K] {C B Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (s : Spec (CommRingCat.of K) ⟶ C) (hs : s ≫ c = 𝟙 _)
    {b : B ⟶ Spec (CommRingCat.of K)} [Smooth b] [IsProper b]
    [GeometricallyIntegral b] (G : RelativeGroupLaw K b) (q : SchemeHomOver c b)
    {r : ℕ} {y : Y ⟶ Spec (CommRingCat.of K)}
    {U : RelEffCartierDiv c r y} (hU : U.IsUniversal) :
    ∃ (σ : finFibrePow c r ⟶ Y) (hσ : σ ≫ y = finFibrePow.toBase c r),
      U.I.comap (mapOnProdOver c σ hσ) = fibrePowOver.tautIdeal c r ∧
      IsFinite σ ∧ Flat σ ∧ Surjective σ ∧
      ∃! sum : SchemeHomOver y b,
        σ ≫ sum.1 = (G.finiteSumMap c q r).1 ∧
        ∀ (D₀ D₁ : RelEffCartierDiv c r (𝟙 (Spec (CommRingCat.of K)))),
          Nonempty (D₀.lineBundle ≅ D₁.lineBundle) →
          hU.lift D₀ ≫ sum.1 = hU.lift D₁ ≫ sum.1 := by
  have : GeometricallyConnected c := GeometricallyIrreducible.geometricallyConnected c
  obtain ⟨σ, hσ, sum, hI, hfin, hflat, hsurj, hfac, -⟩ :=
    exists_finiteSumMap_desc c s hs G q hU
  refine ⟨σ, hσ, hI, hfin, hflat, hsurj, sum, ⟨hfac, ?_⟩, ?_⟩
  · rintro D₀ D₁ ⟨e⟩
    exact lift_comp_eq_of_lineBundle_iso c hU G sum D₀ D₁ e
  · intro sum' hsum'
    apply Subtype.ext
    apply (cancel_epi σ).mp
    exact hsum'.1.trans hfac.symm

end JacobianVarieties.Albanese
