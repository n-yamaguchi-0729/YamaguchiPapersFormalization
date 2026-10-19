/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Descent.EtalePrimeLocalization
import Nyll.EtaleFundamentalGroups.Purity.FiniteEtaleFromBoundaryStalks
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrum
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumPurityIntegralClosure
import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.BaseMinimalPrimeLocalization
import Nyll.SchemeTheory.FunctionFields.OpenImmersion
import Nyll.EtaleFundamentalGroups.GaloisCovers.PullbackComponentFunctionField

/-!
# The punctured cover at a minimal non-etale base point

A finite algebra over a local ring which is etale at every target prime away
from the closed point restricts to a finite-etale cover of the punctured
spectrum.  Applying this to the localization at a minimal base cotangent-
support point packages the prime-local result of
`BaseMinimalPrimeLocalization` as the cover needed by punctured purity.
-/

noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

namespace EtaleFundamentalGroups.SpecialLocalPurity

universe u

private theorem eqToHom_stalk_eq_stalkCongr
    (Z : Scheme.{u}) {z z' : Z} (h : z = z') :
    eqToHom (congrArg (fun w ↦ Z.presheaf.stalk w) h) =
      (Z.presheaf.stalkCongr (.of_eq h)).hom := by
  subst z'
  exact (Z.presheaf.stalkSpecializes_refl z).symm

private theorem functionFieldMap_eq_of_eq
    {T S : Scheme.{u}} [IsIntegral T] [IsIntegral S]
    (a b : S ⟶ T) (hab : a = b)
    (ha : DenseRange a) (hb : DenseRange b) :
    a.functionFieldMap ha = b.functionFieldMap hb := by
  subst b
  rfl

private theorem specFunctionField_algebraMap_ΓSpecIso_hom
    (R : Type u) [CommRing R] [IsDomain R]
    (r : Γ(Spec (.of R), ⊤)) :
    let X := Spec (.of R)
    letI : Nonempty (⊤ : X.Opens) :=
      ⟨⟨genericPoint X, by trivial⟩⟩
    letI : Algebra R X.functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
    algebraMap R X.functionField ((Scheme.ΓSpecIso (.of R)).hom r) =
      X.germToFunctionField ⊤ r := by
  dsimp only
  let X := Spec (.of R)
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨genericPoint X, by trivial⟩⟩
  change X.presheaf.germ ⊤ (genericPoint X) (by trivial)
      ((Scheme.ΓSpecIso (.of R)).inv
        ((Scheme.ΓSpecIso (.of R)).hom r)) =
    X.presheaf.germ ⊤ (genericPoint X) (by trivial) r
  exact congrArg (fun s ↦
    X.presheaf.germ ⊤ (genericPoint X) (by trivial) s)
      (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of R)) r)

/-- If the finite algebra map is injective and the local base has positive
dimension, the inverse image of its puncture is nonempty: it contains the
generic point of the target spectrum. -/
theorem puncturedRestriction_nonempty_of_injective
    {A B : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B))
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim A) :
    let f : Spec (.of B) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A B))
    Nonempty (f ⁻¹ᵁ Scheme.puncturedSpectrumOpen A) := by
  dsimp only
  let f : Spec (.of B) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  let etaA : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  let etaB : PrimeSpectrum B := ⟨⊥, inferInstance⟩
  have hmap : f etaB = etaA := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap A B) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective (algebraMap A B) hinj
  have hmaximal : maximalIdeal A ≠ ⊥ := by
    intro hmaximal
    have hdimZero : ringKrullDim A = 0 := by
      rw [← maximalIdeal_height_eq_ringKrullDim, hmaximal,
        Ideal.height_bot]
      rfl
    rw [hdimZero] at hpos
    exact (not_le_of_gt (by norm_num : (0 : WithBot ℕ∞) < 1)) hpos
  have heta : etaA ∈ Scheme.puncturedSpectrumOpen A := by
    rw [Scheme.mem_puncturedSpectrumOpen_iff]
    intro h
    apply hmaximal
    exact (congrArg PrimeSpectrum.asIdeal h).symm
  refine ⟨⟨etaB, ?_⟩⟩
  change f etaB ∈ Scheme.puncturedSpectrumOpen A
  rw [hmap]
  exact heta

/-- Under the same hypotheses, the inverse image of the puncture is
connected, since it is a nonempty open subscheme of an integral affine
scheme. -/
theorem puncturedRestriction_connectedSpace_of_injective
    {A B : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B))
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim A) :
    let f : Spec (.of B) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A B))
    ConnectedSpace (f ⁻¹ᵁ Scheme.puncturedSpectrumOpen A) := by
  dsimp only
  let f : Spec (.of B) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  let V : (Spec (.of B)).Opens :=
    f ⁻¹ᵁ Scheme.puncturedSpectrumOpen A
  let : Nonempty V :=
    puncturedRestriction_nonempty_of_injective hinj hpos
  let : IsIntegral (V : Scheme) := inferInstance
  exact inferInstance

/-- A finite algebra which is etale at every target prime away from the closed
point gives a finite-etale cover after restricting its spectrum to the
punctured spectrum of the base. -/
theorem puncturedRestriction_isFiniteEtale_of_isEtaleAt_away_from_closedPoint
    {A B : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    (haway :
      ∀ Q : PrimeSpectrum B,
        PrimeSpectrum.comap (algebraMap A B) Q ≠
          ⟨maximalIdeal A, inferInstance⟩ →
        Algebra.IsEtaleAt A Q.asIdeal) :
    let f : Spec (.of B) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A B))
    IsFiniteEtale (f ∣_ Scheme.puncturedSpectrumOpen A) := by
  dsimp only
  let f : Spec (.of B) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  let U : (Spec (.of A)).Opens := Scheme.puncturedSpectrumOpen A
  have hf : IsFinite f := by
    rw [IsFinite.SpecMap_iff]
    change (algebraMap A B).Finite
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hwFinite : IsFinite (f ∣_ U) :=
    MorphismProperty.of_isPullback
      (isPullback_morphismRestrict f U).flip hf
  let : IsFinite (f ∣_ U) := hwFinite
  have hwEtale : Etale (f ∣_ U) := by
    apply EtaleFundamentalGroups.etale_of_stalkMap_formallyEtale
    intro y
    let Q : PrimeSpectrum B := y.1
    have hQaway :
        PrimeSpectrum.comap (algebraMap A B) Q ≠
          ⟨maximalIdeal A, inferInstance⟩ := by
      have hy : f Q ∈ Scheme.puncturedSpectrumOpen A := y.2
      have hne : f Q ≠ closedPoint (CommRingCat.of A) :=
        (Scheme.mem_puncturedSpectrumOpen_iff A (f Q)).mp hy
      change PrimeSpectrum.comap (algebraMap A B) Q ≠
        ⟨maximalIdeal A, inferInstance⟩ at hne
      exact hne
    have hEtale : Algebra.IsEtaleAt A Q.asIdeal := haway Q hQaway
    let q : Ideal A := Q.asIdeal.under A
    let : q.IsPrime := inferInstance
    let : Q.asIdeal.LiesOver q := inferInstance
    let : Algebra (Localization.AtPrime q)
        (Localization.AtPrime Q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver q Q.asIdeal
    have hlocal : Algebra.FormallyEtale (Localization.AtPrime q)
        (Localization.AtPrime Q.asIdeal) := by
      let : Algebra.FormallyEtale A (Localization.AtPrime Q.asIdeal) :=
        hEtale
      exact Algebra.FormallyEtale.localization_base q.primeCompl
    have hSpec : (f.stalkMap Q).hom.FormallyEtale := by
      apply
        (EtaleFundamentalGroups.RingHom.FormallyEtale.respectsIso.arrow_mk_iso_iff
          (Scheme.arrowStalkMapSpecIso
            (CommRingCat.ofHom (algebraMap A B)) Q)).mpr
      change (Localization.localRingHom q Q.asIdeal
        (algebraMap A B) rfl).FormallyEtale
      exact hlocal
    exact
      (EtaleFundamentalGroups.RingHom.FormallyEtale.respectsIso.arrow_mk_iso_iff
        (morphismRestrictStalkMap f U y)).mpr hSpec
  let : Etale (f ∣_ U) := hwEtale
  exact ⟨⟩

/-- The finite-etale cover of the puncture obtained from a finite algebra
which is etale away from the closed point. -/
noncomputable def puncturedRestrictionFiniteEtale
    {A B : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    (haway :
      ∀ Q : PrimeSpectrum B,
        PrimeSpectrum.comap (algebraMap A B) Q ≠
          ⟨maximalIdeal A, inferInstance⟩ →
        Algebra.IsEtaleAt A Q.asIdeal) :
    FiniteEtale (Scheme.puncturedSpectrum A) := by
  let f : Spec (.of B) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  letI : IsFiniteEtale (f ∣_ Scheme.puncturedSpectrumOpen A) :=
    puncturedRestriction_isFiniteEtale_of_isEtaleAt_away_from_closedPoint
      haway
  exact FiniteEtale.mk (f ∣_ Scheme.puncturedSpectrumOpen A)

/-- If both rings are domains, the cover above is connected whenever the
base map is injective and the local base has positive dimension. -/
theorem puncturedRestrictionFiniteEtale_isConnected
    {A B : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    (haway :
      ∀ Q : PrimeSpectrum B,
        PrimeSpectrum.comap (algebraMap A B) Q ≠
          ⟨maximalIdeal A, inferInstance⟩ →
        Algebra.IsEtaleAt A Q.asIdeal)
    (hinj : Function.Injective (algebraMap A B))
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim A) :
    CategoryTheory.PreGaloisCategory.IsConnected
      (puncturedRestrictionFiniteEtale haway) := by
  let f : Spec (.of B) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  let : Nonempty (Scheme.puncturedSpectrum A) :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim A hpos
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion A) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral (Scheme.puncturedSpectrum A) :=
    isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion A)
  let : ConnectedSpace (Scheme.puncturedSpectrum A) := inferInstance
  let : ConnectedSpace (puncturedRestrictionFiniteEtale haway).left := by
    change ConnectedSpace (f ⁻¹ᵁ Scheme.puncturedSpectrumOpen A)
    exact puncturedRestriction_connectedSpace_of_injective hinj hpos
  exact FiniteEtale.isConnected_of_connectedSpace_left
    (puncturedRestrictionFiniteEtale haway)

/-- Punctured purity removes the only possible closed-point ramification of
a finite normal domain algebra. -/
theorem finiteNormalDomainAlgebra_etale_of_hasPuncturedPurity_of_isEtaleAt_away_from_closedPoint
    {A B : Type u}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B]
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim A)
    (hpurity : AlgebraicGeometry.FiniteEtale.HasPuncturedPurity A)
    (haway :
      ∀ Q : PrimeSpectrum B,
        PrimeSpectrum.comap (algebraMap A B) Q ≠
          ⟨maximalIdeal A, inferInstance⟩ →
        Algebra.IsEtaleAt A Q.asIdeal)
    (hinj : Function.Injective (algebraMap A B)) :
    Algebra.Etale A B := by
  let X := Spec (.of A)
  let Y := Spec (.of B)
  let f : Y ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let U := Scheme.puncturedSpectrum A
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion A
  let V : Y.Opens := f ⁻¹ᵁ Scheme.puncturedSpectrumOpen A
  let w : (V : Scheme) ⟶ U :=
    f ∣_ Scheme.puncturedSpectrumOpen A
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim A hpos
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : IsNormalIntegral U := inferInstance
  let : IsLocallyNoetherian U := inferInstance
  let : Nonempty V :=
    puncturedRestriction_nonempty_of_injective hinj hpos
  let : IsIntegral (V : Scheme) := inferInstance
  let : IsFiniteEtale w :=
    puncturedRestriction_isFiniteEtale_of_isEtaleAt_away_from_closedPoint
      haway
  let W : FiniteEtale U := FiniteEtale.mk w
  let : ConnectedSpace W.left := by
    change ConnectedSpace V
    exact puncturedRestriction_connectedSpace_of_injective hinj hpos
  let : IsConnected W :=
    FiniteEtale.isConnected_of_connectedSpace_left W
  let : IsIntegral W.left := by
    change IsIntegral (V : Scheme)
    infer_instance
  let : Algebra A X.functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨genericPoint X, by trivial⟩⟩
  let : Nonempty (⊤ : Y.Opens) :=
    ⟨⟨genericPoint Y, by trivial⟩⟩
  let : Algebra A U.functionField :=
    AlgebraicGeometry.FiniteEtale.puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension
      A hpos
  let : IsFractionRing A U.functionField :=
    AlgebraicGeometry.FiniteEtale.puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension
      A hpos
  let : Algebra U.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra A W.left.functionField :=
    ((algebraMap U.functionField W.left.functionField).comp
      (algebraMap A U.functionField)).toAlgebra
  let : IsScalarTower A U.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hIC : Algebra.Etale A
      (integralClosure A W.left.functionField) :=
    (open _root_.AlgebraicGeometry.FiniteEtale in
      connectedPuncturedCover_integralClosure_etale_of_hasPuncturedPurity
        A hpos hpurity W)
  let i : W.left ⟶ Y := by
    change (V : Scheme) ⟶ Y
    exact V.ι
  let : IsOpenImmersion i := by
    change IsOpenImmersion V.ι
    infer_instance
  let hi : DenseRange i :=
    i.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace i
  let hf : DenseRange f := by
    change DenseRange (PrimeSpectrum.comap (algebraMap A B))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot (algebraMap A B)).mp hinj]
    exact bot_le
  let hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  let hw : DenseRange W.hom :=
    EtaleFundamentalGroups.finiteEtale_hom_denseRange_of_isConnected W
  let hUright : IsIntegral ((Functor.fromPUnit U).obj W.right) := by
    change IsIntegral U
    infer_instance
  let hWleft : IsIntegral ((Functor.id Scheme).obj W.left) := by
    change IsIntegral W.left
    infer_instance
  let : Algebra B Y.functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of B)
  let : Algebra B W.left.functionField :=
    i.functionFieldAlgebraOfIsOpenImmersionSpec (.of B)
  let : IsFractionRing B W.left.functionField :=
    i.functionField_isFractionRing_of_isOpenImmersionSpec (.of B)
  have hfieldSquare :
      (@Scheme.Hom.functionFieldMap Y W.left i inferInstance
        inferInstance hi).comp
          (@Scheme.Hom.functionFieldMap X Y f inferInstance
            inferInstance hf) =
        (@Scheme.Hom.functionFieldMap
          ((Functor.fromPUnit U).obj W.right)
          ((Functor.id Scheme).obj W.left) W.hom hUright hWleft hw).comp
          (@Scheme.Hom.functionFieldMap X U j inferInstance
            inferInstance hj) := by
    let hif : DenseRange (i ≫ f) := by
      change DenseRange (f.base ∘ i.base)
      exact hf.comp hi f.continuous
    let hwj : DenseRange (W.hom ≫ j) := by
      change DenseRange (j.base ∘ W.hom.base)
      exact hj.comp hw j.continuous
    have hsquare : W.hom ≫ j = i ≫ f := by
      change w ≫ j = V.ι ≫ f
      exact morphismRestrict_ι f (Scheme.puncturedSpectrumOpen A)
    calc
      _ = (i ≫ f).functionFieldMap hif := by
        simpa only [hif] using
          Scheme.Hom.functionFieldMap_comp_of_denseRange f hf i hi
      _ = (W.hom ≫ j).functionFieldMap hwj := by
        exact functionFieldMap_eq_of_eq _ _ hsquare.symm _ _
      _ = _ := by
        symm
        have hcomp :=
          Scheme.Hom.functionFieldMap_comp_of_denseRange j hj W.hom hw
        exact hcomp.trans (functionFieldMap_eq_of_eq _ _ rfl _ _)
  have hpunc :
      (AlgebraicGeometry.FiniteEtale.puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension
        A hpos).toRingHom = j.functionFieldMap hj := by
    unfold AlgebraicGeometry.FiniteEtale.puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension
    unfold Scheme.Hom.functionFieldMap
    rw [eqToHom_stalk_eq_stalkCongr]
    · ext x
      rfl
    · exact (genericPoint_eq_of_isOpenImmersion j).symm
  have hspec :
      (f.functionFieldMap hf).comp (algebraMap A X.functionField) =
        (algebraMap B Y.functionField).comp (algebraMap A B) := by
    have htop := f.functionFieldMap_comp_germToFunctionField_top hf
    apply RingHom.ext
    intro a
    let rA : Γ(X, ⊤) := (Scheme.ΓSpecIso (.of A)).inv a
    let rB : Γ(Y, ⊤) := f.appTop rA
    have hmap := DFunLike.congr_fun htop rA
    have hA : X.germToFunctionField ⊤ rA =
        algebraMap A X.functionField a := by
      rw [← specFunctionField_algebraMap_ΓSpecIso_hom A rA]
      congr 1
      exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of A)) a
    have hB : Y.germToFunctionField ⊤ rB =
        algebraMap B Y.functionField (algebraMap A B a) := by
      rw [← specFunctionField_algebraMap_ΓSpecIso_hom B rB]
      congr 1
      change (Scheme.ΓSpecIso (.of B)).hom (f.appTop rA) =
        algebraMap A B a
      rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality,
        CommRingCat.comp_apply]
      change algebraMap A B ((Scheme.ΓSpecIso (.of A)).hom rA) =
        algebraMap A B a
      rw [show (Scheme.ΓSpecIso (.of A)).hom rA = a by
        exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of A)) a]
    change f.functionFieldMap hf (algebraMap A X.functionField a) =
      algebraMap B Y.functionField (algebraMap A B a)
    rw [← hA, ← hB]
    exact hmap
  let : IsScalarTower A B W.left.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change W.hom.functionFieldMap hw
        ((AlgebraicGeometry.FiniteEtale.puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension
          A hpos) (algebraMap A X.functionField a)) =
      i.functionFieldRingEquivOfIsOpenImmersion
        (algebraMap B Y.functionField (algebraMap A B a))
    rw [Scheme.Hom.functionFieldRingEquivOfIsOpenImmersion_apply]
    have hs := DFunLike.congr_fun hspec a
    have hp := DFunLike.congr_fun hpunc (algebraMap A X.functionField a)
    have hsq := DFunLike.congr_fun hfieldSquare
      (algebraMap A X.functionField a)
    have hs' :
        f.functionFieldMap hf (algebraMap A X.functionField a) =
          algebraMap B Y.functionField (algebraMap A B a) := by
      simpa only [RingHom.comp_apply] using hs
    have hp' :
        (AlgebraicGeometry.FiniteEtale.puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension
          A hpos) (algebraMap A X.functionField a) =
          j.functionFieldMap hj (algebraMap A X.functionField a) := hp
    calc
      _ = W.hom.functionFieldMap hw
          (j.functionFieldMap hj (algebraMap A X.functionField a)) :=
        congrArg (W.hom.functionFieldMap hw) hp'
      _ = ((W.hom.functionFieldMap hw).comp (j.functionFieldMap hj))
          (algebraMap A X.functionField a) := rfl
      _ = ((i.functionFieldMap hi).comp (f.functionFieldMap hf))
          (algebraMap A X.functionField a) := hsq.symm
      _ = i.functionFieldMap hi
          (f.functionFieldMap hf (algebraMap A X.functionField a)) := rfl
      _ = i.functionFieldMap hi
          (algebraMap B Y.functionField (algebraMap A B a)) :=
        congrArg (i.functionFieldMap hi) hs'
      _ = _ := by rfl
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : IsIntegralClosure B A W.left.functionField := inferInstance
  let eB : B ≃ₐ[A] integralClosure A W.left.functionField :=
    IsIntegralClosure.equiv A B W.left.functionField
      (integralClosure A W.left.functionField)
  exact Algebra.Etale.of_equiv eB.symm

/-- At a minimal base cotangent-support point, the localized finite algebra
restricts to a finite-etale cover of the punctured local spectrum. -/
theorem
localizedFiniteAlgebra_puncturedRestriction_isFiniteEtale_of_minimal_base_nonEtaleCotangentSupport
    {R S : Type u} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : PrimeSpectrum R)
    (hp : Minimal
      (· ∈ Module.support R Ω[S⁄R] ∪
        Module.support R (Algebra.H1Cotangent R S)) p) :
    let A := Localization.AtPrime p.asIdeal
    let B := Localization
      (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    let f : Spec (.of B) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A B))
    IsFiniteEtale (f ∣_ Scheme.puncturedSpectrumOpen A) := by
  dsimp only
  apply puncturedRestriction_isFiniteEtale_of_isEtaleAt_away_from_closedPoint
  intro Q hQ
  exact
    localizedFiniteAlgebra_isEtaleAt_away_from_closedPoint_of_minimal_base_nonEtaleCotangentSupport
      p hp Q hQ

/-- Punctured purity at a minimal base cotangent-support point upgrades the
localized finite normal-domain algebra from punctured etale to etale. -/
theorem
    localizedFiniteNormalDomainAlgebra_etale_of_minimalBadPuncturedPurity
    {R S : Type u}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (p : PrimeSpectrum R)
    (hp : Minimal
      (· ∈ Module.support R Ω[S⁄R] ∪
        Module.support R (Algebra.H1Cotangent R S)) p)
    (hpos : (1 : WithBot ℕ∞) ≤
      ringKrullDim (Localization.AtPrime p.asIdeal))
    (hpurity : AlgebraicGeometry.FiniteEtale.HasPuncturedPurity
      (Localization.AtPrime p.asIdeal)) :
    Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization
        (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) := by
  let A := Localization.AtPrime p.asIdeal
  let B := Localization
    (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isLocalization A p.asIdeal.primeCompl
      p.asIdeal.primeCompl_le_nonZeroDivisors
  let hSB : Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl ≤
      nonZeroDivisors S := by
    exact map_le_nonZeroDivisors_of_injective
      (algebraMap R S) hinj p.asIdeal.primeCompl_le_nonZeroDivisors
  let : IsDomain B :=
    IsLocalization.isDomain_of_le_nonZeroDivisors B hSB
  let : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_isLocalization B
      (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) hSB
  apply
    finiteNormalDomainAlgebra_etale_of_hasPuncturedPurity_of_isEtaleAt_away_from_closedPoint
      hpos hpurity
  · intro Q hQ
    exact
      (
localizedFiniteAlgebra_isEtaleAt_away_from_closedPoint_of_minimal_base_nonEtaleCotangentSupport
        p hp Q hQ)
  · exact localizationAlgebra_injective A B hinj

/-- Etaleness of the simultaneous localization at a base prime descends,
after localizing once more, to the original map at the prime below a target
prime. -/
theorem isEtaleAt_under_of_localizedAlgebra_etale
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (p : PrimeSpectrum R)
    (hEtale : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization
        (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
    (Q : PrimeSpectrum
      (Localization
        (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))) :
    Algebra.IsEtaleAt R
      (PrimeSpectrum.comap
        (algebraMap S
          (Localization
            (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))) Q).asIdeal := by
  exact SchemeTheory.isEtaleAt_under_of_localizedAlgebra_etale p hEtale Q

/-- If a target prime lies over `p`, etaleness of the simultaneous
localization at `p` implies etaleness of the original algebra at that target
prime. -/
theorem isEtaleAt_of_localizedAlgebra_etale
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (p : PrimeSpectrum R)
    (hEtale : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization
        (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
    (P : PrimeSpectrum S)
    (hPp : PrimeSpectrum.comap (algebraMap R S) P = p) :
    Algebra.IsEtaleAt R P.asIdeal := by
  exact SchemeTheory.isEtaleAt_of_localizedAlgebra_etale p hEtale P hPp

/-- A minimal point of the two cotangent supports cannot persist when its
positive-dimensional local ring has punctured purity. -/
theorem not_minimal_base_nonEtaleCotangentSupport_of_hasPuncturedPurity
    {R S : Type u}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (p : PrimeSpectrum R)
    (hp : Minimal
      (· ∈ Module.support R Ω[S⁄R] ∪
        Module.support R (Algebra.H1Cotangent R S)) p)
    (hpos : (1 : WithBot ℕ∞) ≤
      ringKrullDim (Localization.AtPrime p.asIdeal))
    (hpurity : AlgebraicGeometry.FiniteEtale.HasPuncturedPurity
      (Localization.AtPrime p.asIdeal)) : False := by
  have hEtale : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization
        (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) :=
    localizedFiniteNormalDomainAlgebra_etale_of_minimalBadPuncturedPurity
      hinj p hp hpos hpurity
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let : Module.Finite S Ω[S⁄R] :=
    kaehlerDifferential_finite_of_finite_over_noetherian
  let : Module.Finite S (Algebra.H1Cotangent R S) :=
    h1Cotangent_finite_of_finite_over_noetherian
  let : Module.Finite R Ω[S⁄R] :=
    Module.Finite.trans (R := R) S Ω[S⁄R]
  let : Module.Finite R (Algebra.H1Cotangent R S) :=
    Module.Finite.trans (R := R) S (Algebra.H1Cotangent R S)
  rcases hp.1 with hpΩ | hpH1
  · rw [← image_comap_support_eq_support_of_finite
      (R := R) (S := S) (M := Ω[S⁄R])] at hpΩ
    obtain ⟨P, hP, hPp⟩ := hpΩ
    have hEtaleP : Algebra.IsEtaleAt R P.asIdeal :=
      isEtaleAt_of_localizedAlgebra_etale p hEtale P hPp
    have hLocus : P ∈ Algebra.etaleLocus R S := hEtaleP
    rw [Algebra.etaleLocus_eq_compl_support] at hLocus
    exact hLocus.1 hP
  · rw [← image_comap_support_eq_support_of_finite
      (R := R) (S := S) (M := Algebra.H1Cotangent R S)] at hpH1
    obtain ⟨P, hP, hPp⟩ := hpH1
    have hEtaleP : Algebra.IsEtaleAt R P.asIdeal :=
      isEtaleAt_of_localizedAlgebra_etale p hEtale P hPp
    have hLocus : P ∈ Algebra.etaleLocus R S := hEtaleP
    rw [Algebra.etaleLocus_eq_compl_support] at hLocus
    exact hLocus.2 hP

/-- A finite normal-domain algebra is formally etale if punctured purity and
positive local dimension hold at every hypothetical minimal cotangent-support
point. -/
theorem
    finiteNormalDomainAlgebra_formallyEtale_of_minimalBadPuncturedPurity
    {R S : Type u}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (hpos : ∀ (p : PrimeSpectrum R),
      Minimal
        (· ∈ Module.support R Ω[S⁄R] ∪
          Module.support R (Algebra.H1Cotangent R S)) p →
      (1 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p.asIdeal))
    (hpurity : ∀ (p : PrimeSpectrum R),
      Minimal
        (· ∈ Module.support R Ω[S⁄R] ∪
          Module.support R (Algebra.H1Cotangent R S)) p →
      AlgebraicGeometry.FiniteEtale.HasPuncturedPurity
        (Localization.AtPrime p.asIdeal)) :
    Algebra.FormallyEtale R S := by
  by_contra hne
  obtain ⟨p, hp, P, hPp, hP⟩ :=
    exists_minimal_base_nonEtaleCotangentSupport_of_not_formallyEtale hne
  exact
    not_minimal_base_nonEtaleCotangentSupport_of_hasPuncturedPurity
      hinj p hp (hpos p hp) (hpurity p hp)

/-- Under the same hypotheses, module-finiteness over the Noetherian base
supplies finite presentation, so the algebra is etale. -/
theorem
    finiteNormalDomainAlgebra_etale_of_hasPuncturedPurity_at_minimal_base_nonEtaleCotangentSupport
    {R S : Type u}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (hpos : ∀ (p : PrimeSpectrum R),
      Minimal
        (· ∈ Module.support R Ω[S⁄R] ∪
          Module.support R (Algebra.H1Cotangent R S)) p →
      (1 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p.asIdeal))
    (hpurity : ∀ (p : PrimeSpectrum R),
      Minimal
        (· ∈ Module.support R Ω[S⁄R] ∪
          Module.support R (Algebra.H1Cotangent R S)) p →
      AlgebraicGeometry.FiniteEtale.HasPuncturedPurity
        (Localization.AtPrime p.asIdeal)) :
    Algebra.Etale R S := by
  let : Algebra.FormallyEtale R S :=
    finiteNormalDomainAlgebra_formallyEtale_of_minimalBadPuncturedPurity
      hinj hpos hpurity
  let : Module.FinitePresentation R S :=
    Module.finitePresentation_of_finite R S
  let : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finitePresentation R S
  exact ⟨inferInstance, inferInstance⟩

end EtaleFundamentalGroups.SpecialLocalPurity

end
