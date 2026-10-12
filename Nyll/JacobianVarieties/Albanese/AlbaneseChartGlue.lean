/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The finite chart cover uses the construction in
`Exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced.lean`.
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Upstream source (Apache 2.0):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced.lean
Upstream NOTICE:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Nyll.JacobianVarieties.Albanese.DivisorPicardSums
import Nyll.JacobianVarieties.Albanese.SameDivisorDescent
import Nyll.JacobianVarieties.Albanese.FiniteSums
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.JacobianVarieties.Picard.Exists_representsRelSubPic_algEquivZeroCut_of_isAlgClosed
import Nyll.JacobianVarieties.Picard.Exists_chart_subsingleton_H1_fibre
import Nyll.JacobianVarieties.Picard.HasChartSections_forall_geometricFibre_riemannRoch_imp_eq
import Nyll.JacobianVarieties.Picard.EulerChar_fibre_sectionTwist_tensor_idealModule_eq_one
import Nyll.JacobianVarieties.Picard.Exists_opens_range_subset_iff_forall_subsingleton_H1_fibre
import Nyll.JacobianVarieties.Picard.Exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1
import Nyll.JacobianVarieties.Picard.Exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_prodKerGraph
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_isUniversal
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivTwist2
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback
import Nyll.AlgebraicCurves.Models.Exists_isAffineOpen_forall_mem_of_finset_of_field
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.AlgebraicCurves.Geometry.Schemes.ext_of_forall_comp_eq_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIrreducible_geometricallyConnected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Gluing the actual divisor sums on Picard charts

Riemann--Roch supplies a finite open cover of the Picard scheme by families of
effective divisors of a common degree. Their sum morphisms agree on the actual
overlaps, since their twists are restrictions of the same Poincare bundle.
The resulting morphism has a calculation rule on every reduced family.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.OpenChart.AlgebraicGeometry.RelPicard.ChartOne
open JacobianVarieties.Picard.Proofs.ClosedFieldRepresentation

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

private def pullback_twist_iso
    {K : Type u} [Field K] {C P T T' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsSeparated c]
    [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    {p : P ⟶ Spec (CommRingCat.of K)} (L : RigidifiedLineBundle c ε p)
    {t : T ⟶ Spec (CommRingCat.of K)} (a : SchemeHomOver t p)
    {r : ℕ} (D : RelEffCartierDiv c r t)
    (e : D.twistModule c ε ≅ (L.pullbackAlong a).L)
    {t' : T' ⟶ Spec (CommRingCat.of K)} (v : SchemeHomOver t' t) :
    (D.pullbackAlong v.1 v.2).twistModule c ε ≅
      (L.pullbackAlong (postComp a v)).L :=
  (RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε v D).some ≪≫
    (Scheme.Modules.pullback (baseChangeSnd c v)).mapIso e ≪≫
    L.pullbackAlongPullbackAlongIso a v

private theorem exists_divisor_charts
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    {P : RelativePic0Designation K c} [LocallyOfFiniteType P.toBase]
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) P) :
    ∃ (r : ℕ), 0 < r ∧ ∃ (n : ℕ) (V : Fin n → P.P.Opens),
      TopologicalSpace.IsOpenCover V ∧
      ∀ i : Fin n, ∃ E : RelEffCartierDiv c r ((V i).ι ≫ P.toBase),
        Nonempty (E.twistModule c ε ≅
          (h.poincare.pullbackAlong (⟨(V i).ι, rfl⟩ :
            SchemeHomOver ((V i).ι ≫ P.toBase) P.toBase)).L) := by
  classical
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  have h𝔉 := P2mJacAbs.exists_finiteMapData K c ε
  obtain ⟨n, g, r, hgr, γ, hγ⟩ := P2mJacAbs.exists_hasChartSections K c
  have hg := HasChartSections.forall_geometricFibre_riemannRoch_imp_eq hγ
  have hD : ∀ i : Fin n, ∃ D : RelEffCartierDiv c (r - g) (𝟙 (Spec (CommRingCat.of K))),
      D.I = prodKerGraph c (fun j => (γ i j).1) (fun j => (γ i j).2) := fun i =>
    RelEffCartierDiv.exists_I_eq_prodKerGraph (fun j => (γ i j).1) (fun j => (γ i j).2)
  choose Dγ hDγ using hD
  have hχ : ∀ (i : Fin n) (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of K)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H1 = 1 :=
    fun i k _ _ x 𝒲 =>
      eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one
        K c ε g (r - g) r (by omega) (Dγ i) hg k x 𝒲
  have hVexists := fun i : Fin n =>
    exists_opens_range_subset_iff_forall_subsingleton_H1_fibre K c ε h𝔉 P.toBase
      (Mγ K c ε r (Dγ i) P.toBase h.poincare)
      (isInvertible_Mγ K c ε r (Dγ i) P.toBase h.poincare)
  choose V hV using hVexists
  refine ⟨r, by omega, n, V, ?_, ?_⟩
  · apply TopologicalSpace.IsOpenCover.mk
    rw [eq_top_iff]
    intro p _
    obtain ⟨i, hi⟩ := exists_chart_subsingleton_H1_fibre
      K c ε n g r hgr hg γ hγ Dγ hDγ hχ P.toBase h.poincare h.poincare_mem
      (P.P.residueField p) (P.P.fromSpecResidueField p)
    have hmem := (hV i (P.P.residueField p) (P.P.fromSpecResidueField p)).mpr hi
    have hp : p ∈ V i := hmem ⟨IsLocalRing.closedPoint (P.P.residueField p),
      P.P.fromSpecResidueField_apply p _⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hp⟩
  · intro i
    obtain ⟨E, _, _, he⟩ := exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1
      K c ε h𝔉 g (r - g) r (by omega) (Dγ i) (hχ i) P.toBase h.poincare
      h.poincare_mem (V i) (fun k _ s hs => (hV i k s).mp hs)
    exact ⟨E, he⟩

/-- The sums of the actual effective divisors glue to a morphism on the Picard
scheme. Its value is computed by the same universal degree-`r` divisor on every
reduced finite-type family whose twist is the indicated Poincare pullback. -/
theorem exists_divisorSum_glue
    {K : Type u} [Field K] [IsAlgClosed K] {C B : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    {P : RelativePic0Designation K c} [LocallyOfFiniteType P.toBase] [IsReduced P.P]
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) P)
    {b : B ⟶ Spec (CommRingCat.of K)} [Smooth b] [IsProper b]
    [GeometricallyIntegral b] (G : RelativeGroupLaw K b) (q : SchemeHomOver c b) :
    ∃ (r : ℕ) (_ : 0 < r) (Y : Scheme.{u}) (y : Y ⟶ Spec (CommRingCat.of K))
      (U : RelEffCartierDiv c r y) (hU : U.IsUniversal)
      (σ : finFibrePow c r ⟶ Y) (hσ : σ ≫ y = finFibrePow.toBase c r)
      (sum : SchemeHomOver y b) (ψ : SchemeHomOver P.toBase b),
      U.I.comap (mapOnProdOver c σ hσ) = fibrePowOver.tautIdeal c r ∧
      σ ≫ sum.1 = (G.finiteSumMap c q r).1 ∧
      ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K))
        [LocallyOfFiniteType t] [IsReduced T] (D : RelEffCartierDiv c r t)
        (a : SchemeHomOver t P.toBase),
        Nonempty (D.twistModule c ε ≅ (h.poincare.pullbackAlong a).L) →
          a.1 ≫ ψ.1 = hU.lift D ≫ sum.1 := by
  classical
  have : GeometricallyConnected c := GeometricallyIrreducible.geometricallyConnected c
  obtain ⟨r, hr, n, V, hV, hE⟩ := exists_divisor_charts c ε h
  choose E eE using hE
  obtain ⟨Y, y, U, hU⟩ := exists_universal_over_field c r
  obtain ⟨σ, hσ, sum, hI, _, _, _, hsum, _⟩ :=
    exists_finiteSumMap_desc c ε.1 ε.2 G q hU
  let 𝒰 : P.P.OpenCover := P.P.openCoverOfIsOpenCover V hV
  let f : ∀ i : Fin n, (V i : Scheme.{u}) ⟶ B := fun i => hU.lift (E i) ≫ sum.1
  have hf : ∀ i j : Fin n, pullback.fst (V i).ι (V j).ι ≫ f i =
      pullback.snd (V i).ι (V j).ι ≫ f j := by
    intro i j
    let W := pullback (V i).ι (V j).ι
    let t : W ⟶ Spec (CommRingCat.of K) :=
      pullback.fst (V i).ι (V j).ι ≫ (V i).ι ≫ P.toBase
    let vi : SchemeHomOver t ((V i).ι ≫ P.toBase) := ⟨pullback.fst _ _, rfl⟩
    let vj : SchemeHomOver t ((V j).ι ≫ P.toBase) :=
      ⟨pullback.snd _ _, (pullback.condition_assoc P.toBase).symm⟩
    have : IsReduced W := isReduced_of_isOpenImmersion
      (pullback.fst (V i).ι (V j).ι)
    have : LocallyOfFiniteType t := inferInstance
    let ei := pullback_twist_iso c ε h.poincare ⟨(V i).ι, rfl⟩ (E i) (eE i).some vi
    let ej := pullback_twist_iso c ε h.poincare ⟨(V j).ι, rfl⟩ (E j) (eE j).some vj
    have ep : (h.poincare.pullbackAlong
        (postComp (⟨(V i).ι, rfl⟩ : SchemeHomOver ((V i).ι ≫ P.toBase) P.toBase) vi)).L =
        (h.poincare.pullbackAlong
        (postComp (⟨(V j).ι, rfl⟩ : SchemeHomOver ((V j).ι ≫ P.toBase) P.toBase) vj)).L := by
      apply RigidifiedLineBundle_pullbackAlong_L_eq
      exact pullback.condition
    have ee : ((E i).pullbackAlong vi.1 vi.2).twistModule c ε ≅
        ((E j).pullbackAlong vj.1 vj.2).twistModule c ε :=
      ei ≪≫ eqToIso ep ≪≫ ej.symm
    have heq := lift_comp_eq_of_twistModule_iso c ε hU G sum t
      ((E i).pullbackAlong vi.1 vi.2) ((E j).pullbackAlong vj.1 vj.2) ee
    rw [lift_pullbackAlong, lift_pullbackAlong, Category.assoc, Category.assoc] at heq
    exact heq
  let ψ₀ : P.P ⟶ B := 𝒰.glueMorphisms f hf
  have hψ : ∀ i : Fin n, (V i).ι ≫ ψ₀ = f i :=
    fun i => 𝒰.ι_glueMorphisms f hf i
  have hψb : ψ₀ ≫ b = P.toBase := by
    apply 𝒰.hom_ext
    change ∀ i : Fin n, (V i).ι ≫ (ψ₀ ≫ b) = (V i).ι ≫ P.toBase
    intro i
    rw [← Category.assoc, hψ]
    change (hU.lift (E i) ≫ sum.1) ≫ b = (V i).ι ≫ P.toBase
    rw [Category.assoc, sum.2, hU.lift_comp]
  let ψ : SchemeHomOver P.toBase b := ⟨ψ₀, hψb⟩
  have hpoint : ∀ (D : RelEffCartierDiv c r (𝟙 (Spec (CommRingCat.of K))))
      (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) P.toBase),
      Nonempty (D.twistModule c ε ≅ (h.poincare.pullbackAlong a).L) →
        a.1 ≫ ψ.1 = hU.lift D ≫ sum.1 := by
    intro D a ⟨e⟩
    have hp : a.1 (IsLocalRing.closedPoint K) ∈ ⨆ i, V i := by
      rw [hV.iSup_eq_top]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    have haV : Set.range ⇑a.1 ⊆ Set.range ⇑(V i).ι := by
      rintro _ ⟨z, rfl⟩
      have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      exact ⟨⟨a.1 z, hz ▸ hi⟩, rfl⟩
    let x := IsOpenImmersion.lift (V i).ι a.1 haV
    have hx : x ≫ (V i).ι = a.1 := IsOpenImmersion.lift_fac _ _ haV
    let v : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) ((V i).ι ≫ P.toBase) :=
      ⟨x, by rw [← Category.assoc, hx, a.2]⟩
    let ei := pullback_twist_iso c ε h.poincare ⟨(V i).ι, rfl⟩ (E i) (eE i).some v
    let ee : ((E i).pullbackAlong v.1 v.2).twistModule c ε ≅ D.twistModule c ε :=
      ei ≪≫ eqToIso (RigidifiedLineBundle_pullbackAlong_L_eq h.poincare hx) ≪≫ e.symm
    have heq := lift_comp_eq_of_twistModule_iso c ε hU G sum (𝟙 _)
      ((E i).pullbackAlong v.1 v.2) D ee
    rw [lift_pullbackAlong, Category.assoc] at heq
    calc
      a.1 ≫ ψ.1 = x ≫ ((V i).ι ≫ ψ₀) := by rw [← Category.assoc, hx]
      _ = x ≫ f i := by rw [hψ]
      _ = hU.lift D ≫ sum.1 := heq
  refine ⟨r, hr, Y, y, U, hU, σ, hσ, sum, ψ, hI, hsum, ?_⟩
  intro T t _ _ D a ⟨e⟩
  apply ext_of_forall_comp_eq_of_isAlgClosed t b
    (by rw [Category.assoc, ψ.2, a.2])
    (by rw [Category.assoc, sum.2, hU.lift_comp])
  intro x hx
  let v : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) t := ⟨x, hx⟩
  let ee := pullback_twist_iso c ε h.poincare a D e v
  have heq := hpoint (D.pullbackAlong x hx) (postComp a v) ⟨ee⟩
  rw [lift_pullbackAlong, Category.assoc] at heq
  exact heq

end JacobianVarieties.Albanese
