/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Ramification under a finite, flat tensor square

Let `S / R` be finite and let `R' / R` be flat.  A prime of
`R' ⊗[R] S` has two contractions, one to `S` and one to `R'`.  If the
second contraction is the scheme-theoretic extension of the contraction
to `R`, then the two horizontal ramification indices agree in residue
characteristic zero.

The point which is not covered by the usual etale base-change lemma is
that `R' / R` need not be etale (the intended application is an adic
completion).  Instead, the proof identifies the localization of the
`S`-fiber at the retained tensor prime with a localization of

`p'.ResidueField ⊗[p.ResidueField] q.ResidueField`.

The latter is a reduced Artinian algebra: finiteness comes from `S / R`,
and separability comes from residue characteristic zero.  Its prime
localizations are therefore fields, which says that the vertical
ramification index is one.  The tensor prime itself, rather than an
independently selected component, is retained throughout.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uS uR'

section ResidueTensor

variable {R : Type uR} {S : Type uS}
  [CommRing R] [CommRing S] [Algebra R S]

/-- Tensoring a residue field once more with the residue field below does
not change it.  This is the canonical localization-and-quotient
identification; it does not choose a field component. -/
private noncomputable def residueFieldFiberAlgEquiv
    (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)] :
    p.Fiber q.ResidueField ≃ₐ[p.ResidueField] q.ResidueField := by
  let L := q.ResidueField
  let M : Submonoid L :=
    Algebra.algebraMapSubmonoid L p.primeCompl
  let LM := Localization M
  letI : Algebra L (p.Fiber L) :=
    Algebra.TensorProduct.rightAlgebra
  have hMunit : M ≤ IsUnit.submonoid L := by
    rintro z ⟨r, hr, rfl⟩
    change IsUnit (algebraMap R L r)
    rw [isUnit_iff_ne_zero]
    intro hz
    have hzq : algebraMap S L (algebraMap R S r) = 0 := by
      simpa [IsScalarTower.algebraMap_apply R S L] using hz
    have hrq : algebraMap R S r ∈ q :=
      Ideal.algebraMap_residueField_eq_zero.mp hzq
    exact hr ((Ideal.mem_of_liesOver (P := q) (p := p) r).mpr hrq)
  letI : IsLocalization M L :=
    IsLocalization.of_le_isUnit hMunit
  let eLoc : LM ≃ₐ[L] L := Localization.algEquiv M L
  letI : IsScalarTower R L LM :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let pLM : Ideal LM :=
    (p.map (algebraMap R L)).map (algebraMap L LM)
  have hpLM : pLM = ⊥ := by
    have hpL : p.map (algebraMap R L) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker]
      intro r hr
      rw [RingHom.mem_ker]
      rw [IsScalarTower.algebraMap_apply R S L,
        Ideal.algebraMap_residueField_eq_zero]
      exact (Ideal.mem_of_liesOver (P := q) (p := p) r).mp hr
    change (p.map (algebraMap R L)).map (algebraMap L LM) = ⊥
    rw [hpL, Ideal.map_bot]
  let eRight : p.Fiber L ≃ₐ[L] L :=
    (Ideal.Fiber.algEquivAux₁ p).trans <|
      (Ideal.quotientEquivAlgOfEq L hpLM).trans <|
        (AlgEquiv.quotientBot L LM).trans eLoc
  have hcomm :
      eRight.toRingHom.comp
          (algebraMap p.ResidueField (p.Fiber L)) =
        algebraMap p.ResidueField L := by
    apply IsFractionRing.ringHom_ext (A := R ⧸ p)
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    calc
      eRight
          (algebraMap p.ResidueField (p.Fiber L)
            (algebraMap (R ⧸ p) p.ResidueField
              (Ideal.Quotient.mk p r))) =
          eRight (algebraMap R (p.Fiber L) r) := by
            rw [Ideal.algebraMap_quotient_residueField_mk,
              IsScalarTower.algebraMap_apply R p.ResidueField
                (p.Fiber L)]
      _ = eRight
          (algebraMap L (p.Fiber L) (algebraMap R L r)) := by
            rw [IsScalarTower.algebraMap_apply R L (p.Fiber L)]
      _ = algebraMap R L r := eRight.commutes _
      _ = algebraMap p.ResidueField L
          (algebraMap (R ⧸ p) p.ResidueField
            (Ideal.Quotient.mk p r)) := by
            rw [Ideal.algebraMap_quotient_residueField_mk,
              IsScalarTower.algebraMap_apply R p.ResidueField L]
  exact
    { toRingEquiv := eRight.toRingEquiv
      commutes' := fun x ↦ DFunLike.congr_fun hcomm x }

/-- A prime localization of a finite separable tensor product of fields is
a field. -/
private theorem isField_localizationAtPrime_finiteSeparableTensor
    {K H L : Type*} [Field K] [Field H] [Field L]
    [Algebra K H] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (m : Ideal (H ⊗[K] L)) [m.IsPrime] :
    IsField (Localization.AtPrime m) := by
  let G := H ⊗[K] L
  let : Algebra H G := Algebra.TensorProduct.leftAlgebra
  let : Module.Finite H G := Module.Finite.base_change K H L
  let : Algebra.Etale K L :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
      finitePresentation :=
        Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  let : Algebra.Etale H G := by infer_instance
  let : Algebra.FormallyUnramified H (Localization.AtPrime m) :=
    Algebra.FormallyUnramified.comp H G (Localization.AtPrime m)
  let : Module.Finite H (Localization.AtPrime m) :=
    Algebra.FormallyUnramified.finite_of_free H
      (Localization.AtPrime m)
  let : IsArtinianRing (Localization.AtPrime m) :=
    IsArtinianRing.of_finite H (Localization.AtPrime m)
  let : IsReduced (Localization.AtPrime m) :=
    Algebra.FormallyUnramified.isReduced_of_field H
      (Localization.AtPrime m)
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing _

end ResidueTensor

section TensorSquare

variable {R : Type uR} {S : Type uS} {R' : Type uR'}
  [CommRing R] [CommRing S] [CommRing R']
  [Algebra R S] [Algebra R R']

/- The canonical right tensor algebra, scalar tower, and inherited flatness
are owned here once.  This prevents each public wrapper from rebuilding the
same instance path. -/
local instance tensorSquareRightAlgebra :
    Algebra S (R' ⊗[R] S) :=
  Algebra.TensorProduct.rightAlgebra

local instance tensorSquareRightScalarTower :
    IsScalarTower R S (R' ⊗[R] S) :=
  Algebra.TensorProduct.right_isScalarTower

local instance tensorSquareRightFlat [Module.Flat R R'] :
    Module.Flat S (R' ⊗[R] S) :=
  Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight R S R').symm.toLinearEquiv

/-- Transfer the field property from a prime localization of a fiber back
to the corresponding prime localization of the algebra.  The fiber prime
comparison is explicit, so only one localization-algebra instance is live. -/
private theorem isField_localization_of_fiber_prime
    {A : Type*} [CommRing A] [Algebra R' A]
    (p' : Ideal R') [p'.IsPrime]
    (s : PrimeSpectrum (p'.Fiber A))
    (r : Ideal A) [r.IsPrime] [r.LiesOver p']
    (hrs : r = s.asIdeal.comap
      Algebra.TensorProduct.includeRight.toRingHom)
    (hpA : p'.map (algebraMap R' A) = ⊥)
    (hFieldS : IsField (Localization.AtPrime s.asIdeal)) :
    IsField (Localization.AtPrime r) := by
  have hComapOver :
      (s.asIdeal.comap
        Algebra.TensorProduct.includeRight.toRingHom).LiesOver p' := by
    refine ⟨?_⟩
    change p' =
      (s.asIdeal.comap
        (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A).toRingHom).comap
          (algebraMap R' A)
    rw [← hrs]
    exact Ideal.over_def r p'
  let :
      (s.asIdeal.comap
        Algebra.TensorProduct.includeRight.toRingHom).LiesOver p' :=
    hComapOver
  let : Algebra (Localization.AtPrime p')
      (Localization.AtPrime
        (s.asIdeal.comap
          (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A))) :=
    Localization.AtPrime.algebraOfLiesOver p'
      (s.asIdeal.comap
        (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A))
  let eFiber := Ideal.Fiber.localizationAlgEquivQuotient p' s.asIdeal
  have hpLocal : p'.map
      (algebraMap R'
        (Localization.AtPrime
          (s.asIdeal.comap
            (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A)))) = ⊥ := by
    calc
      p'.map
          (algebraMap R'
            (Localization.AtPrime
              (s.asIdeal.comap
                (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A)))) =
          (p'.map (algebraMap R' A)).map
            (algebraMap A
              (Localization.AtPrime
                (s.asIdeal.comap
                  (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A)))) := by
        symm
        rw [Ideal.map_map,
          IsScalarTower.algebraMap_eq R' A
            (Localization.AtPrime
              (s.asIdeal.comap
                (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A)))]
      _ = ⊥ := by rw [hpA, Ideal.map_bot]
  let eLocal : Localization.AtPrime s.asIdeal
      ≃ₐ[Localization.AtPrime p']
        Localization.AtPrime
          (s.asIdeal.comap
            (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A)) :=
    eFiber.trans <|
      (Ideal.quotientEquivAlgOfEq
        (Localization.AtPrime p') hpLocal).trans <|
        AlgEquiv.quotientBot
          (Localization.AtPrime p')
          (Localization.AtPrime
            (s.asIdeal.comap
              (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A)))
  have hFieldComap : IsField
      (Localization.AtPrime
        (s.asIdeal.comap
          (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A))) :=
    eLocal.symm.toMulEquiv.isField hFieldS
  let eIdeal :
      Localization.AtPrime
          (s.asIdeal.comap
            (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A))
        ≃ₐ[A] Localization.AtPrime r :=
    Localization.localAlgEquiv
      (s.asIdeal.comap
        (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A))
      r (AlgEquiv.refl : A ≃ₐ[A] A) hrs.symm
  exact eIdeal.symm.toMulEquiv.isField hFieldComap

/-- A field localization of the retained fiber prime forces the vertical
maximal ideal at the original tensor prime. -/
private theorem right_maximalIdeal_of_fiber_localization_isField
    {T : Type*} [CommRing T] [Algebra S T]
    (q : Ideal S) [q.IsPrime]
    (Q : Ideal T) [Q.IsPrime] [Q.LiesOver q]
    (r : PrimeSpectrum (q.Fiber T))
    (hQr : Q = r.asIdeal.comap
      Algebra.TensorProduct.includeRight.toRingHom)
    (hFieldR : IsField (Localization.AtPrime r.asIdeal)) :
    q.map (algebraMap S (Localization.AtPrime Q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  have hComapOver :
      (r.asIdeal.comap
        Algebra.TensorProduct.includeRight.toRingHom).LiesOver q := by
    refine ⟨?_⟩
    change q =
      (r.asIdeal.comap
        (Algebra.TensorProduct.includeRight : T →ₐ[S] q.Fiber T).toRingHom).comap
          (algebraMap S T)
    rw [← hQr]
    exact Ideal.over_def Q q
  let :
      (r.asIdeal.comap
        Algebra.TensorProduct.includeRight.toRingHom).LiesOver q :=
    hComapOver
  let : Algebra (Localization.AtPrime q)
      (Localization.AtPrime
        (r.asIdeal.comap
          (Algebra.TensorProduct.includeRight : T →ₐ[S] q.Fiber T))) :=
    Localization.AtPrime.algebraOfLiesOver q
      (r.asIdeal.comap
        (Algebra.TensorProduct.includeRight : T →ₐ[S] q.Fiber T))
  let eFiber := Ideal.Fiber.localizationAlgEquivQuotient q r.asIdeal
  have hFieldVerticalAtR :
      IsField
        (Localization.AtPrime
            (r.asIdeal.comap
              (Algebra.TensorProduct.includeRight : T →ₐ[S] q.Fiber T)) ⧸
          q.map
            (algebraMap S
              (Localization.AtPrime
                (r.asIdeal.comap
                  (Algebra.TensorProduct.includeRight : T →ₐ[S] q.Fiber T))))) :=
    eFiber.symm.toMulEquiv.isField hFieldR
  let eIdeal : Localization.AtPrime Q ≃ₐ[T]
      Localization.AtPrime
        (r.asIdeal.comap
          (Algebra.TensorProduct.includeRight : T →ₐ[S] q.Fiber T)) :=
    Localization.localAlgEquiv Q
      (r.asIdeal.comap
        (Algebra.TensorProduct.includeRight : T →ₐ[S] q.Fiber T))
      (AlgEquiv.refl : T ≃ₐ[T] T) hQr
  have hqMap :
      q.map
          (algebraMap S
            (Localization.AtPrime
              (r.asIdeal.comap
                (Algebra.TensorProduct.includeRight : T →ₐ[S] q.Fiber T)))) =
        (q.map (algebraMap S (Localization.AtPrime Q))).map
          eIdeal.toRingEquiv.toRingHom := by
    rw [Ideal.map_map]
    congr 1
    ext x
    change algebraMap S
        (Localization.AtPrime
          (r.asIdeal.comap
            (Algebra.TensorProduct.includeRight : T →ₐ[S] q.Fiber T))) x =
      eIdeal (algebraMap S (Localization.AtPrime Q) x)
    rw [IsScalarTower.algebraMap_apply S T (Localization.AtPrime Q),
      eIdeal.commutes,
      IsScalarTower.algebraMap_apply S T
        (Localization.AtPrime
          (r.asIdeal.comap
            (Algebra.TensorProduct.includeRight : T →ₐ[S] q.Fiber T)))]
  let eVerticalQuotient :
      (Localization.AtPrime Q ⧸
          q.map (algebraMap S (Localization.AtPrime Q))) ≃+*
        (Localization.AtPrime
            (r.asIdeal.comap
              (Algebra.TensorProduct.includeRight : T →ₐ[S] q.Fiber T)) ⧸
          q.map
            (algebraMap S
              (Localization.AtPrime
                (r.asIdeal.comap
                  (Algebra.TensorProduct.includeRight : T →ₐ[S] q.Fiber T))))) :=
    Ideal.quotientEquiv
      (q.map (algebraMap S (Localization.AtPrime Q)))
      (q.map
        (algebraMap S
          (Localization.AtPrime
            (r.asIdeal.comap
              (Algebra.TensorProduct.includeRight : T →ₐ[S] q.Fiber T)))))
      eIdeal.toRingEquiv hqMap
  have hFieldVerticalQuotient :
      IsField
        (Localization.AtPrime Q ⧸
          q.map (algebraMap S (Localization.AtPrime Q))) :=
    eVerticalQuotient.toMulEquiv.isField hFieldVerticalAtR
  have hqMax :
      (q.map (algebraMap S
        (Localization.AtPrime Q))).IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr
      hFieldVerticalQuotient
  exact IsLocalRing.eq_maximalIdeal hqMax

/-- Construct the vertical maximal-ideal equality at the retained tensor
prime.  All residue-fiber instances are owned by this boundary; callers see
only the canonical right tensor algebra fixed above. -/
private theorem tensorProduct_localization_right_maximalIdeal_core
    [Module.Finite R S] [Module.Flat R R']
    (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (p' : Ideal R')
    (Q : Ideal (R' ⊗[R] S)) [Q.IsPrime] [Q.LiesOver p']
    (hQq : Q.comap
      Algebra.TensorProduct.includeRight.toRingHom = q)
    (hpmap : p.map (algebraMap R R') = p')
    [CharZero (R ⧸ p)] :
    q.map (algebraMap S (Localization.AtPrime Q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  let T := R' ⊗[R] S
  let : Q.LiesOver q :=
    { over := by
        simpa [Ideal.under_def,
          Algebra.TensorProduct.algebraMap_eq_includeRight] using hQq.symm }
  have hQOverp : Q.LiesOver p := Ideal.LiesOver.trans Q q p
  let : Q.LiesOver p := hQOverp
  have hp'Overp : p'.LiesOver p :=
    Ideal.LiesOver.tower_bot Q p' p
  let : p'.LiesOver p := hp'Overp
  let : p'.IsPrime := Ideal.isPrime_of_liesOver Q p'
  let : Algebra (Localization.AtPrime p)
      (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra (Localization.AtPrime p)
      (Localization.AtPrime p') :=
    Localization.AtPrime.algebraOfLiesOver p p'
  let : CharZero p.ResidueField :=
    IsFractionRing.charZero_of_isFractionRing (R ⧸ p)
  let : PerfectField p.ResidueField := by infer_instance
  let : Module.Finite p.ResidueField q.ResidueField := by
    infer_instance
  let : Algebra.IsSeparable p.ResidueField q.ResidueField :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  let A := q.Fiber T
  let Qover : q.primesOver T := ⟨Q, inferInstance, inferInstance⟩
  let r : PrimeSpectrum A :=
    PrimeSpectrum.primesOverOrderIsoFiber S T q Qover
  have hQr :
      Q = r.asIdeal.comap
        Algebra.TensorProduct.includeRight.toRingHom := by
    change (Q : Ideal T) = r.asIdeal.comap
      (Algebra.TensorProduct.includeRight : T →ₐ[S] A)
    rw [← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply,
      OrderIso.symm_apply_apply]
  let rprimeToA : R' →+* A :=
    (Algebra.TensorProduct.includeRight : T →ₐ[S] A).toRingHom.comp
      (Algebra.TensorProduct.includeLeft : R' →ₐ[R] T).toRingHom
  let : Algebra R' A := rprimeToA.toAlgebra
  have hrOverp' : r.asIdeal.LiesOver p' := by
    refine ⟨?_⟩
    change p' = r.asIdeal.comap
      ((Algebra.TensorProduct.includeRight : T →ₐ[S] A).toRingHom.comp
        (Algebra.TensorProduct.includeLeft : R' →ₐ[R] T).toRingHom)
    rw [← Ideal.comap_comap, ← hQr]
    exact Ideal.over_def Q p'
  let : r.asIdeal.LiesOver p' := hrOverp'
  have hpA : p'.map (algebraMap R' A) = ⊥ := by
    rw [← hpmap, Ideal.map_map,
      Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker]
    change (1 : q.ResidueField) ⊗ₜ[S]
        ((algebraMap R R' x) ⊗ₜ[R] (1 : S)) = 0
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
    calc
      (1 : q.ResidueField) ⊗ₜ[S]
          (1 ⊗ₜ[R] algebraMap R S x : T) =
          (1 : q.ResidueField) ⊗ₜ[S]
            algebraMap S T (algebraMap R S x) := rfl
      _ = algebraMap S q.ResidueField (algebraMap R S x) ⊗ₜ[S]
          (1 : T) :=
        (Algebra.TensorProduct.tmul_one_eq_one_tmul
          (R := S) (A := q.ResidueField) (B := T)
          (algebraMap R S x)).symm
      _ = 0 := by
        rw [Ideal.algebraMap_residueField_eq_zero.mpr
          ((Ideal.mem_of_liesOver (P := q) (p := p) x).mp hx)]
        exact TensorProduct.zero_tmul _ _
  let B := p'.Fiber A
  let rover : p'.primesOver A :=
    ⟨r.asIdeal, inferInstance, inferInstance⟩
  let s : PrimeSpectrum B :=
    PrimeSpectrum.primesOverOrderIsoFiber R' A p' rover
  have hrs :
      r.asIdeal = s.asIdeal.comap
        Algebra.TensorProduct.includeRight.toRingHom := by
    change r.asIdeal = s.asIdeal.comap
      (Algebra.TensorProduct.includeRight : A →ₐ[R'] B)
    rw [← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply,
      OrderIso.symm_apply_apply]
  let AR := q.ResidueField ⊗[R] R'
  let eAq : A ≃ₐ[q.ResidueField] AR :=
    (Algebra.TensorProduct.congr AlgEquiv.refl
      (Algebra.TensorProduct.commRight R S R').symm).trans
      (Algebra.TensorProduct.cancelBaseChange
        R S q.ResidueField q.ResidueField R')
  let : Algebra R' AR := Algebra.TensorProduct.rightAlgebra
  let eAR' : A ≃ₐ[R'] AR :=
    { toRingEquiv := eAq.toRingEquiv
      commutes' := by
        intro x
        change eAq ((1 : q.ResidueField) ⊗ₜ[S]
          ((x : R') ⊗ₜ[R] (1 : S))) =
            (1 : q.ResidueField) ⊗ₜ[R] x
        simp only [eAq, AlgEquiv.trans_apply]
        rw [Algebra.TensorProduct.congr_apply,
          Algebra.TensorProduct.map_tmul]
        change (Algebra.TensorProduct.cancelBaseChange
          R S q.ResidueField q.ResidueField R')
            ((1 : q.ResidueField) ⊗ₜ[S]
              ((Algebra.TensorProduct.commRight R S R').symm
                ((x : R') ⊗ₜ[R] (1 : S)))) =
            (1 : q.ResidueField) ⊗ₜ[R] x
        rw [Algebra.TensorProduct.commRight_symm_tmul,
          Algebra.TensorProduct.cancelBaseChange_tmul, one_smul] }
  let H := p'.ResidueField
  let G := H ⊗[p.ResidueField] q.ResidueField
  let eB0 : B ≃ₐ[H] (H ⊗[R] q.ResidueField) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl eAR').trans <|
      (Algebra.TensorProduct.congr AlgEquiv.refl
        (Algebra.TensorProduct.commRight
          R R' q.ResidueField).symm).trans <|
        Algebra.TensorProduct.cancelBaseChange
          R R' H H q.ResidueField
  let eResidue : p.Fiber q.ResidueField
      ≃ₐ[p.ResidueField] q.ResidueField :=
    residueFieldFiberAlgEquiv p q
  let eReduce : (H ⊗[R] q.ResidueField) ≃ₐ[H] G :=
    (Algebra.TensorProduct.cancelBaseChange
      R p.ResidueField H H q.ResidueField).symm.trans <|
      Algebra.TensorProduct.congr AlgEquiv.refl eResidue
  let eB : B ≃ₐ[H] G := eB0.trans eReduce
  let m : Ideal G := s.asIdeal.map eB.toRingEquiv
  let : m.IsPrime := by
    exact Ideal.map_isPrime_of_surjective eB.surjective fun x hx ↦ by
      have hx0 : x = 0 := eB.injective (hx.trans eB.map_zero.symm)
      subst x
      exact s.asIdeal.zero_mem
  have hsComap : s.asIdeal = m.comap eB.toRingHom := by
    symm
    exact Ideal.comap_map_of_bijective
      eB.toRingEquiv eB.bijective
  let eLocalB : Localization.AtPrime s.asIdeal
      ≃ₐ[H] Localization.AtPrime m :=
    Localization.localAlgEquiv s.asIdeal m eB hsComap
  have hFieldM : IsField (Localization.AtPrime m) :=
    isField_localizationAtPrime_finiteSeparableTensor m
  have hFieldS : IsField (Localization.AtPrime s.asIdeal) :=
    eLocalB.toMulEquiv.isField hFieldM
  have hFieldR : IsField (Localization.AtPrime r.asIdeal) :=
    isField_localization_of_fiber_prime p' s r.asIdeal hrs hpA hFieldS
  exact right_maximalIdeal_of_fiber_localization_isField
    q Q r hQr hFieldR

/-- Ramification is preserved at the retained prime of a finite tensor
square after a flat base change in residue characteristic zero.

`hQq` is the literal right-coordinate contraction of `Q`; `hpmap` says
that its left contraction is the scheme-theoretic extension of `p`.
Neither a tensor component, a residue-field comparison, nor a
ramification-index equality is supplied as an input. -/
theorem ramificationIdx_tensorProduct_eq_of_finite_flat_charZero
    [Module.Finite R S] [Module.Flat R R']
    (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (p' : Ideal R')
    (Q : Ideal (R' ⊗[R] S)) [Q.IsPrime] [Q.LiesOver p']
    (hQq : Q.comap
      Algebra.TensorProduct.includeRight.toRingHom = q)
    (hpmap : p.map (algebraMap R R') = p')
    [CharZero (R ⧸ p)] :
    Q.ramificationIdx R' = q.ramificationIdx R := by
  let : Q.LiesOver q :=
    { over := by
        simpa [Ideal.under_def,
          Algebra.TensorProduct.algebraMap_eq_includeRight] using hQq.symm }
  have hQOverp : Q.LiesOver p := Ideal.LiesOver.trans Q q p
  let : Q.LiesOver p := hQOverp
  have hp'Overp : p'.LiesOver p :=
    Ideal.LiesOver.tower_bot Q p' p
  let : p'.LiesOver p := hp'Overp
  let : p'.IsPrime := Ideal.isPrime_of_liesOver Q p'
  have hqLocal :=
    tensorProduct_localization_right_maximalIdeal_core
      (p := p) (q := q) (p' := p') (Q := Q) hQq hpmap
  have hVertical : Q.ramificationIdx S = 1 := by
    rw [Ideal.ramificationIdx_eq q Q, hqLocal,
      ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
      Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
      ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff]
  let TQ := Localization.AtPrime Q
  have hSameBaseIdeal :
      p'.map (algebraMap R' TQ) =
        p.map (algebraMap R TQ) := by
    rw [← hpmap, Ideal.map_map,
      IsScalarTower.algebraMap_eq R R' TQ]
  have hAcrossBase :
      Q.ramificationIdx R' = Q.ramificationIdx R := by
    rw [Ideal.ramificationIdx_eq p' Q,
      Ideal.ramificationIdx_eq p Q, hSameBaseIdeal]
  calc
    Q.ramificationIdx R' = Q.ramificationIdx R := hAcrossBase
    _ = q.ramificationIdx R * Q.ramificationIdx S :=
      Ideal.ramificationIdx_tower q Q
    _ = q.ramificationIdx R := by rw [hVertical, mul_one]

/-- At the retained tensor prime, the vertical local maximal ideal is
exactly the extension of the old prime.

This is the ideal-theoretic content hidden behind the vertical
ramification index one in
`ramificationIdx_tensorProduct_eq_of_finite_flat_charZero`.  It is useful
before passing to a normalization: no independently chosen prime, formal
unramifiedness hypothesis, or comparison of local rings is supplied. -/
theorem tensorProduct_localization_right_maximalIdeal_eq_of_finite_flat_charZero
    [Module.Finite R S] [Module.Flat R R']
    (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (p' : Ideal R')
    (Q : Ideal (R' ⊗[R] S)) [Q.IsPrime] [Q.LiesOver p']
    (hQq : Q.comap
      Algebra.TensorProduct.includeRight.toRingHom = q)
    (hpmap : p.map (algebraMap R R') = p')
    [CharZero (R ⧸ p)] :
    q.map (algebraMap S (Localization.AtPrime Q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  exact tensorProduct_localization_right_maximalIdeal_core
    (p := p) (q := q) (p' := p') (Q := Q) hQq hpmap

/-- Principal-branch form of
`tensorProduct_localization_right_maximalIdeal_eq_of_finite_flat_charZero`.
The equality between the mapped source branch and the completed branch is
discharged by `Ideal.map_span`. -/
theorem tensorProduct_localization_right_maximalIdeal_eq_span_of_finite_flat_charZero
    [Module.Finite R S] [Module.Flat R R']
    (y : R)
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (Ideal.span ({y} : Set R))]
    (Q : Ideal (R' ⊗[R] S)) [Q.IsPrime]
    [Q.LiesOver
      (Ideal.span ({algebraMap R R' y} : Set R'))]
    (hQq : Q.comap
      Algebra.TensorProduct.includeRight.toRingHom = q)
    [CharZero (R ⧸ Ideal.span ({y} : Set R))] :
    q.map (algebraMap S (Localization.AtPrime Q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  let : (Ideal.span ({y} : Set R)).IsPrime :=
    Ideal.isPrime_of_liesOver q (Ideal.span ({y} : Set R))
  exact
    tensorProduct_localization_right_maximalIdeal_eq_of_finite_flat_charZero
      (p := Ideal.span ({y} : Set R))
      (q := q)
      (p' := Ideal.span ({algebraMap R R' y} : Set R'))
      (Q := Q) hQq (by
        rw [Ideal.map_span, Set.image_singleton])

/-- Application form for a retained completion prime over a principal
height-one boundary.  The mapped-prime equality is generated internally
from `Ideal.map_span`; the only prime comparison is the literal right
contraction of the retained tensor prime. -/
theorem ramificationIdx_tensorProduct_span_eq_of_finite_flat_charZero
    [Module.Finite R S] [Module.Flat R R']
    (y : R)
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (Ideal.span ({y} : Set R))]
    (Q : Ideal (R' ⊗[R] S)) [Q.IsPrime]
    [Q.LiesOver
      (Ideal.span ({algebraMap R R' y} : Set R'))]
    (hQq : Q.comap
      Algebra.TensorProduct.includeRight.toRingHom = q)
    [CharZero (R ⧸ Ideal.span ({y} : Set R))] :
    Q.ramificationIdx R' = q.ramificationIdx R := by
  let : (Ideal.span ({y} : Set R)).IsPrime :=
    Ideal.isPrime_of_liesOver q (Ideal.span ({y} : Set R))
  exact ramificationIdx_tensorProduct_eq_of_finite_flat_charZero
    (p := Ideal.span ({y} : Set R))
    (q := q)
    (p' := Ideal.span ({algebraMap R R' y} : Set R'))
    (Q := Q) hQq (by
      rw [Ideal.map_span, Set.image_singleton])

/-- Exact-index form used after a selected branch has supplied its
ramification index before completion. -/
theorem ramificationIdx_tensorProduct_span_eq_of_finite_flat_charZero_of_eq
    [Module.Finite R S] [Module.Flat R R']
    (y : R)
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (Ideal.span ({y} : Set R))]
    (Q : Ideal (R' ⊗[R] S)) [Q.IsPrime]
    [Q.LiesOver
      (Ideal.span ({algebraMap R R' y} : Set R'))]
    (hQq : Q.comap
      Algebra.TensorProduct.includeRight.toRingHom = q)
    [CharZero (R ⧸ Ideal.span ({y} : Set R))]
    {N : ℕ} (hq : q.ramificationIdx R = N) :
    Q.ramificationIdx R' = N := by
  rw [ramificationIdx_tensorProduct_span_eq_of_finite_flat_charZero
    (y := y) (q := q) (Q := Q) hQq, hq]

end TensorSquare

end EtaleFundamentalGroups

end
