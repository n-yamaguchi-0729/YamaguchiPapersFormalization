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

import Nyll.JacobianVarieties.Albanese.DivisorPicardSumsField
import Nyll.JacobianVarieties.Albanese.LineBundleSumBaseChange
import Nyll.JacobianVarieties.Albanese.SeparableDivisorCharts
import Nyll.JacobianVarieties.Albanese.SameDivisorDescent
import Nyll.JacobianVarieties.Albanese.FiniteSums
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_isUniversal
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivTwist2
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback
import Nyll.AlgebraicCurves.Models.Exists_isAffineOpen_forall_mem_of_finset_of_field
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
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

/-- After a finite separable extension constructed from the pointed curve, the
actual divisor sums glue on the Picard scheme. The calculation rule holds on
every reduced finite-type test scheme over that extension. -/
theorem exists_finite_separable_divisorSum_glue
    (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (_ : Algebra.IsSeparable K L),
      let cL := SmoothProperCurve.baseChange K c L
      let εL := sectionBaseChange L ε
      ∀ (P : RelativePic0Designation L cL)
        [LocallyOfFiniteType P.toBase] [IsReduced P.P]
        (h : RepresentsRelSubPic cL εL (algEquivZeroCut cL εL) P)
        (B : Scheme.{u}) (b : B ⟶ Spec (CommRingCat.of L)) [Smooth b] [IsProper b]
        [GeometricallyIntegral b] (G : RelativeGroupLaw L b) (q : SchemeHomOver cL b),
        ∃ (r : ℕ) (_ : 0 < r) (Y : Scheme.{u}) (y : Y ⟶ Spec (CommRingCat.of L))
          (U : RelEffCartierDiv cL r y) (hU : U.IsUniversal)
          (σ : finFibrePow cL r ⟶ Y) (hσ : σ ≫ y = finFibrePow.toBase cL r)
          (sum : SchemeHomOver y b) (ψ : SchemeHomOver P.toBase b),
          U.I.comap (mapOnProdOver cL σ hσ) = fibrePowOver.tautIdeal cL r ∧
          σ ≫ sum.1 = (G.finiteSumMap cL q r).1 ∧
          (∀ (F : Type u) [Field F] (s : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of L))
            (D : RelEffCartierDiv cL r s) (a : SchemeHomOver s P.toBase),
            Nonempty (D.twistModule cL εL ≅ (h.poincare.pullbackAlong a).L) →
              a.1 ≫ ψ.1 = hU.lift D ≫ sum.1) ∧
          ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of L))
            [LocallyOfFiniteType t] [IsReduced T] (D : RelEffCartierDiv cL r t)
            (a : SchemeHomOver t P.toBase),
            Nonempty (D.twistModule cL εL ≅ (h.poincare.pullbackAlong a).L) →
              a.1 ≫ ψ.1 = hU.lift D ≫ sum.1 := by
  classical
  obtain ⟨L, hL, hKL, hfin, hsep, hcharts⟩ := exists_finite_separable_divisor_charts K c ε
  refine ⟨L, hL, hKL, hfin, hsep, ?_⟩
  intro cL εL P _ _ h B b _ _ _ G q
  have : GeometricallyConnected cL := GeometricallyIrreducible.geometricallyConnected cL
  obtain ⟨r, hr, n, V, hV, hE⟩ := hcharts P h
  choose E eE using hE
  obtain ⟨Y, y, U, hU⟩ := exists_universal_over_field cL r
  obtain ⟨σ, hσ, sum, hI, _, _, _, hsum, _⟩ :=
    exists_finiteSumMap_desc cL εL.1 εL.2 G q hU
  let 𝒰 : P.P.OpenCover := P.P.openCoverOfIsOpenCover V hV
  let f : ∀ i : Fin n, (V i : Scheme.{u}) ⟶ B := fun i => hU.lift (E i) ≫ sum.1
  have hf : ∀ i j : Fin n, pullback.fst (V i).ι (V j).ι ≫ f i =
      pullback.snd (V i).ι (V j).ι ≫ f j := by
    intro i j
    let W := pullback (V i).ι (V j).ι
    let t : W ⟶ Spec (CommRingCat.of L) :=
      pullback.fst (V i).ι (V j).ι ≫ (V i).ι ≫ P.toBase
    let vi : SchemeHomOver t ((V i).ι ≫ P.toBase) := ⟨pullback.fst _ _, rfl⟩
    let vj : SchemeHomOver t ((V j).ι ≫ P.toBase) :=
      ⟨pullback.snd _ _, (pullback.condition_assoc P.toBase).symm⟩
    have : IsReduced W := isReduced_of_isOpenImmersion
      (pullback.fst (V i).ι (V j).ι)
    have : LocallyOfFiniteType t := inferInstance
    let ei := pullback_twist_iso cL εL h.poincare ⟨(V i).ι, rfl⟩ (E i) (eE i).some vi
    let ej := pullback_twist_iso cL εL h.poincare ⟨(V j).ι, rfl⟩ (E j) (eE j).some vj
    have ep : (h.poincare.pullbackAlong
        (postComp (⟨(V i).ι, rfl⟩ : SchemeHomOver ((V i).ι ≫ P.toBase) P.toBase) vi)).L =
        (h.poincare.pullbackAlong
        (postComp (⟨(V j).ι, rfl⟩ : SchemeHomOver ((V j).ι ≫ P.toBase) P.toBase) vj)).L := by
      apply congrArg (fun v : SchemeHomOver t P.toBase => (h.poincare.pullbackAlong v).L)
      exact Subtype.ext pullback.condition
    have ee : ((E i).pullbackAlong vi.1 vi.2).twistModule cL εL ≅
        ((E j).pullbackAlong vj.1 vj.2).twistModule cL εL :=
      ei ≪≫ eqToIso ep ≪≫ ej.symm
    have heq := lift_comp_eq_of_twistModule_iso_of_field cL εL hU G sum t
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
  have hpoint : ∀ (F : Type u) [Field F]
      (s : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of L))
      (D : RelEffCartierDiv cL r s) (a : SchemeHomOver s P.toBase),
      Nonempty (D.twistModule cL εL ≅ (h.poincare.pullbackAlong a).L) →
        a.1 ≫ ψ.1 = hU.lift D ≫ sum.1 := by
    intro F _ s D a ⟨e⟩
    have hp : a.1 (IsLocalRing.closedPoint F) ∈ ⨆ i, V i := by
      rw [hV.iSup_eq_top]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    have haV : Set.range ⇑a.1 ⊆ Set.range ⇑(V i).ι := by
      rintro _ ⟨z, rfl⟩
      have hz : z = IsLocalRing.closedPoint F := Subsingleton.elim _ _
      exact ⟨⟨a.1 z, hz ▸ hi⟩, rfl⟩
    let x := IsOpenImmersion.lift (V i).ι a.1 haV
    have hx : x ≫ (V i).ι = a.1 := IsOpenImmersion.lift_fac _ _ haV
    let v : SchemeHomOver s ((V i).ι ≫ P.toBase) :=
      ⟨x, by rw [← Category.assoc, hx, a.2]⟩
    let ei := pullback_twist_iso cL εL h.poincare ⟨(V i).ι, rfl⟩ (E i) (eE i).some v
    have ep : (h.poincare.pullbackAlong
        (postComp (⟨(V i).ι, rfl⟩ : SchemeHomOver ((V i).ι ≫ P.toBase) P.toBase) v)).L =
        (h.poincare.pullbackAlong a).L := by
      apply congrArg (fun z : SchemeHomOver s P.toBase => (h.poincare.pullbackAlong z).L)
      exact Subtype.ext hx
    let ee : ((E i).pullbackAlong v.1 v.2).twistModule cL εL ≅ D.twistModule cL εL :=
      ei ≪≫ eqToIso ep ≪≫ e.symm
    obtain ⟨el⟩ := nonempty_lineBundle_iso_of_twistModule_iso_of_fieldMap cL εL F s
      ((E i).pullbackAlong v.1 v.2) D ee
    have heq := lift_comp_eq_of_lineBundle_iso_of_fieldMap cL hU G sum F s
      ((E i).pullbackAlong v.1 v.2) D el
    rw [lift_pullbackAlong, Category.assoc] at heq
    calc
      a.1 ≫ ψ.1 = x ≫ ((V i).ι ≫ ψ₀) := by rw [← Category.assoc, hx]
      _ = x ≫ f i := by rw [hψ]
      _ = hU.lift D ≫ sum.1 := heq
  refine ⟨r, hr, Y, y, U, hU, σ, hσ, sum, ψ, hI, hsum, hpoint, ?_⟩
  intro T t _ _ D a ⟨e⟩
  let 𝒱 : T.OpenCover := 𝒰.pullback₁ a.1
  apply 𝒱.hom_ext
  change ∀ i : Fin n, pullback.fst a.1 (V i).ι ≫ (a.1 ≫ ψ.1) =
    pullback.fst a.1 (V i).ι ≫ (hU.lift D ≫ sum.1)
  intro i
  let W := pullback a.1 (V i).ι
  let tW : W ⟶ Spec (CommRingCat.of L) := pullback.fst a.1 (V i).ι ≫ t
  let vD : SchemeHomOver tW t := ⟨pullback.fst _ _, rfl⟩
  let vE : SchemeHomOver tW ((V i).ι ≫ P.toBase) :=
    ⟨pullback.snd _ _, by rw [← Category.assoc, ← pullback.condition,
      Category.assoc, a.2]⟩
  have : IsReduced W := isReduced_of_isOpenImmersion (pullback.fst a.1 (V i).ι)
  have : LocallyOfFiniteType tW := inferInstance
  let eD := pullback_twist_iso cL εL h.poincare a D e vD
  let eV := pullback_twist_iso cL εL h.poincare ⟨(V i).ι, rfl⟩ (E i) (eE i).some vE
  have ep : (h.poincare.pullbackAlong (postComp a vD)).L =
      (h.poincare.pullbackAlong
        (postComp (⟨(V i).ι, rfl⟩ : SchemeHomOver ((V i).ι ≫ P.toBase) P.toBase) vE)).L := by
    apply congrArg (fun v : SchemeHomOver tW P.toBase => (h.poincare.pullbackAlong v).L)
    exact Subtype.ext pullback.condition
  let ee : (D.pullbackAlong vD.1 vD.2).twistModule cL εL ≅
      ((E i).pullbackAlong vE.1 vE.2).twistModule cL εL :=
    eD ≪≫ eqToIso ep ≪≫ eV.symm
  have heq := lift_comp_eq_of_twistModule_iso_of_field cL εL hU G sum tW
    (D.pullbackAlong vD.1 vD.2) ((E i).pullbackAlong vE.1 vE.2) ee
  rw [lift_pullbackAlong, lift_pullbackAlong, Category.assoc, Category.assoc] at heq
  calc
    pullback.fst a.1 (V i).ι ≫ (a.1 ≫ ψ.1) =
        pullback.snd a.1 (V i).ι ≫ ((V i).ι ≫ ψ₀) := by
      rw [← Category.assoc, pullback.condition, Category.assoc]
    _ = pullback.snd a.1 (V i).ι ≫ f i := by rw [hψ]
    _ = pullback.fst a.1 (V i).ι ≫ (hU.lift D ≫ sum.1) := heq.symm

end JacobianVarieties.Albanese
