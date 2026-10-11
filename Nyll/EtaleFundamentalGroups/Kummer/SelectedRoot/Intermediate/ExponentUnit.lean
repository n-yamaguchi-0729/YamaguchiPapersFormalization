/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.RingHom.Etale
import Nyll.EtaleFundamentalGroups.Kummer.Boundary.IteratedRadical
import Nyll.EtaleFundamentalGroups.Kummer.Descent.FormallyUnramifiedDescent
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Regularity
import Nyll.EtaleFundamentalGroups.Kummer.PureRadical.HeightOneRootsOfUnity
import Nyll.EtaleFundamentalGroups.Kummer.PureRadical.IntegralClosure
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwo.IntegralClosure.HeightTwo
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.Defs

/-!
# The selected intermediate-root exponent is a boundary unit

Let `A` be a two-parameter regular local domain with selected boundary
parameter `t`, and let `K` be its fraction field.  In a pure radical field
extension `L / K`, every intermediate field `F` has a concrete generator
`β` satisfying `β ^ [F : K] = t`.  If the actual normalization of `A` in
`F` is etale away from `t`, then `[F : K]` is invertible modulo `t`.

The proof constructs the root algebra from `β`; neither its identification
with the normalization nor the desired unit assertion is assumed.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing Polynomial
open scoped BigOperators TensorProduct

universe u v w z

/-- Base change of one pure root algebra, in the ordinary `AdjoinRoot`
presentation. -/
noncomputable def oneRootBaseChangeAlgEquiv
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    (m : ℕ) (t : A) :
    S ⊗[A] AdjoinRoot (X ^ m - C t) ≃ₐ[S]
      AdjoinRoot (X ^ m - C (algebraMap A S t)) := by
  let p : A[X] := X ^ m - C t
  let pS : S[X] := X ^ m - C (algebraMap A S t)
  let ePrefix : S ⊗[A] A ≃ₐ[S] S :=
    AlgEquiv.ofAlgHom
      ((Algebra.ofId A S).liftEquiv A S A S)
      (Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[A] A)
      (by ext)
      (by ext)
  let q : (S ⊗[A] A)[X] :=
    p.map Algebra.TensorProduct.includeRight.toRingHom
  have hcomm :
      ePrefix (algebraMap A S t ⊗ₜ[A] (1 : A)) =
        algebraMap S S (algebraMap A S t) := by
    simpa only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
      using ePrefix.commutes (algebraMap A S t)
  exact
    (AdjoinRoot.tensorAlgEquiv p q rfl).trans
      (AdjoinRoot.mapAlgEquiv ePrefix q pS <| by
        apply Associated.of_eq
        dsimp only [q, p, pS]
        rw [Polynomial.map_map, Polynomial.map_sub, Polynomial.map_pow,
          Polynomial.map_X, Polynomial.map_C]
        change (X : S[X]) ^ m - C (ePrefix ((1 : S) ⊗ₜ[A] t)) =
          (X : S[X]) ^ m - C (algebraMap A S t)
        have htensor : (1 : S) ⊗ₜ[A] t =
            algebraMap A S t ⊗ₜ[A] (1 : A) := by
          simpa only [Algebra.algebraMap_self_apply] using
            (Algebra.TensorProduct.tmul_one_eq_one_tmul
              (A := S) (B := A) t).symm
        rw [htensor, hcomm]
        rfl)

/-- The one-stage recursive radical is the ordinary one-root algebra. -/
noncomputable def oneIteratedRadicalAlgEquiv
    (A : Type u) [CommRing A] (m : ℕ) (t : A) :
    iteratedRadical A 1 (fun _ : Fin 1 ↦ m) (fun _ : Fin 1 ↦ t) ≃ₐ[A]
      AdjoinRoot (X ^ m - C t) := by
  let n₁ : Fin 1 → ℕ := fun _ ↦ m
  let a₁ : Fin 1 → A := fun _ ↦ t
  let T : CommAlgCat.{u} A :=
    iteratedRadical A 0 (Fin.init n₁) (Fin.init a₁)
  let pT : T[X] :=
    X ^ n₁ (Fin.last 0) -
      C (algebraMap A T (a₁ (Fin.last 0)))
  let pA : A[X] := X ^ m - C t
  let ePrefix : T ≃ₐ[A] A := AlgEquiv.refl
  change AdjoinRoot pT ≃ₐ[A] AdjoinRoot pA
  exact AdjoinRoot.mapAlgEquiv ePrefix pT pA <| by
    apply Associated.of_eq
    dsimp only [pT, pA, n₁, a₁]
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rfl

/-- The actual normalization being etale away from `t` makes the localized
pure-root model formally unramified.  The root model and its normalization
structure are constructed from the field generator. -/
private theorem awayMap_formallyUnramified_of_normalization_etale
    {A : Type u} {K : Type v} {F : Type w}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field F] [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F]
    {m : ℕ} (hm : 0 < m) {t y : A}
    (hreg : RingTheory.Sequence.IsRegular A [t, y])
    (hgen : Ideal.ofList [t, y] = maximalIdeal A)
    (β : F) (hdegree : Module.finrank K F = m)
    (hβpow : β ^ m = algebraMap K F (algebraMap A K t))
    (hβgen : IntermediateField.adjoin K {β} = ⊤)
    [Module.Finite A (integralClosure A F)]
    (hEtale : RingHom.Etale
      (R := Localization.Away t)
      (S := Localization.Away (algebraMap A (integralClosure A F) t))
      (Localization.awayMap
        (algebraMap A (integralClosure A F)) t)) :
    RingHom.FormallyUnramified
      (Localization.awayMap
        (algebraMap A (AdjoinRoot (X ^ m - C t))) t) := by
  let p : A[X] := X ^ m - C t
  let B := AdjoinRoot p
  let φ : B →ₐ[A] F :=
    pureRadicalAdjoinRootToField t β hβpow
  let : Algebra B F := φ.toRingHom.toAlgebra
  let : IsScalarTower A B F :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (φ.commutes a).symm
  let : IsFractionRing B F :=
    isFractionRing_adjoinRoot_of_pureRadical
      hm t β hdegree hβpow hβgen
  let : IsDomain B := (IsFractionRing.injective B F).isDomain _
  have hpMonic : p.Monic :=
    Polynomial.monic_X_pow_sub_C t hm.ne'
  let : Module.Finite A B := hpMonic.finite_adjoinRoot
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : IsRegularLocalRing B :=
    isRegularLocalRing_adjoinRoot_X_pow_sub_C_of_regular_parameters
      hm hreg hgen
  have hdimB : ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞) := by
    simpa [B, p] using
      (localRootCoverParameterList_length_eq_ringKrullDim
        (R := A) (n := m) (a := t) (rs := [y]) hm hreg hgen)
  let D := integralClosure A F
  let ψ : B →ₐ[A] D := IsIntegralClosure.lift A D F
  let : Algebra B D := ψ.toRingHom.toAlgebra
  let : IsScalarTower A B D :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (ψ.commutes a).symm
  let : IsScalarTower B D F :=
    IsScalarTower.of_algebraMap_eq fun b ↦
      (IsIntegralClosure.algebraMap_lift A D F b).symm
  let : IsIntegralClosure D B F :=
    IsIntegralClosure.tower_top (R := A) (A := B) (B := F) (C := D)
  let : Module.Finite B D :=
    Module.Finite.of_restrictScalars_finite A B D
  let E := integralClosure B F
  let e : E ≃ₐ[B] D := IsIntegralClosure.equiv B E F D
  let : Module.Finite B E :=
    Module.Finite.equiv e.symm.toLinearEquiv
  let : Module.Free B E :=
    (open _root_.EtaleFundamentalGroups.SpecialLocalPurity in
      integralClosure_free_of_isRegularLocalRing_dimension_two
        (A := B) (K := F) (L := F) hdimB)
  let : Module.Free B D := Module.Free.of_equiv e.toLinearEquiv
  let b : B := algebraMap A B t
  let S := Localization.Away t
  let Bs := Localization.Away b
  let Ds := Localization.Away (algebraMap A D t)
  let f : S →+* Bs := Localization.awayMap (algebraMap A B) t
  let mapBDs : B →+* Ds :=
    (algebraMap D Ds).comp (algebraMap B D)
  have hbUnit : IsUnit (mapBDs b) := by
    change IsUnit (algebraMap D Ds (ψ (algebraMap A B t)))
    rw [ψ.commutes]
    exact IsLocalization.Away.algebraMap_isUnit _
  let g : Bs →+* Ds := Localization.awayLift mapBDs b hbUnit
  let : Algebra S Bs := f.toAlgebra
  let : IsScalarTower A S Bs :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap A Bs a = f (algebraMap A S a)
      rw [show f (algebraMap A S a) =
        algebraMap B Bs (algebraMap A B a) by
          simp [f, S, Bs, b, IsLocalization.Away.map]]
      exact IsScalarTower.algebraMap_apply A B Bs a
  let : Algebra Bs Ds := g.toAlgebra
  let : IsScalarTower B Bs Ds :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      change algebraMap B Ds z = g (algebraMap B Bs z)
      rw [show g (algebraMap B Bs z) = mapBDs z by simp [g]]
      exact IsScalarTower.algebraMap_apply B D Ds z
  have hcomp : g.comp f =
      Localization.awayMap (algebraMap A D) t := by
    apply IsLocalization.ringHom_ext (Submonoid.powers t)
    ext a
    simp only [RingHom.comp_apply]
    calc
      g (f (algebraMap A S a)) =
          g (algebraMap B Bs (algebraMap A B a)) := by
        rw [show f (algebraMap A S a) =
          algebraMap B Bs (algebraMap A B a) by
            simp [f, S, Bs, b, IsLocalization.Away.map]]
      _ = mapBDs (algebraMap A B a) := by simp [g]
      _ = algebraMap D Ds (ψ (algebraMap A B a)) := rfl
      _ = algebraMap D Ds (algebraMap A D a) := by rw [ψ.commutes]
      _ = Localization.awayMap (algebraMap A D) t
          (algebraMap A S a) := by
        simp [S, Ds, IsLocalization.Away.map]
  have hEtaleComp : RingHom.Etale (g.comp f) := by
    rw [hcomp]
    exact hEtale
  let : Algebra S Ds := (g.comp f).toAlgebra
  let : IsScalarTower S Bs Ds :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra.Etale S Ds := hEtaleComp.toAlgebra
  have hbD : algebraMap B D b = algebraMap A D t := by
    exact (IsScalarTower.algebraMap_apply A B D t).symm
  let : IsLocalization
      (Algebra.algebraMapSubmonoid D (Submonoid.powers b)) Ds := by
    change IsLocalization
      ((Submonoid.powers b).map (algebraMap B D)) Ds
    rw [Submonoid.map_powers, hbD]
    infer_instance
  let basisD := Module.Free.chooseBasis B D
  let basisDs :=
    basisD.localizationLocalization Bs (Submonoid.powers b) Ds
  let : Module.Free Bs Ds := Module.Free.of_basis basisDs
  let : Module.Finite Bs Ds := Module.Finite.of_basis basisDs
  let : Algebra.FormallyUnramified Bs Ds :=
    Algebra.FormallyUnramified.of_restrictScalars S Bs Ds
  let : Module.FinitePresentation Bs Ds :=
    Module.finitePresentation_of_finite Bs Ds
  let : Algebra.FinitePresentation Bs Ds :=
    Algebra.FinitePresentation.of_finitePresentation Bs Ds
  let : Algebra.Etale Bs Ds :=
    Algebra.Etale.of_formallyUnramified_of_flat
  let : Algebra.FormallyEtale Bs Ds := inferInstance
  have ht0 : t ≠ 0 :=
    (_root_.EtaleFundamentalGroups.SpecialLocalPurity.regular_pair_nonzero_and_isRelPrime
      hreg).1
  have htD : algebraMap A D t ≠ 0 := by
    intro htD
    apply ht0
    apply IsFractionRing.injective A K
    apply (algebraMap K F).injective
    calc
      algebraMap K F (algebraMap A K t) = algebraMap A F t :=
        (IsScalarTower.algebraMap_apply A K F t).symm
      _ = algebraMap D F (algebraMap A D t) :=
        IsScalarTower.algebraMap_apply A D F t
      _ = 0 := by rw [htD, map_zero]
      _ = algebraMap K F (algebraMap A K 0) := by simp
  let : IsDomain Ds := IsLocalization.Away.isDomain Ds htD
  let : Module.FaithfullyFlat Bs Ds := inferInstance
  have hFU : Algebra.FormallyUnramified S Bs :=
    formallyUnramified_of_formallyEtale_faithfullyFlat
      (R := S) (S := Bs) (T := Ds)
  change @Algebra.FormallyUnramified S Bs _ _ f.toAlgebra
  exact hFU

/-- The embedded variant of
`awayMap_formallyUnramified_of_normalization_etale`.

Here the pure-root fraction field is `F`, but the normalization whose
etaleness is known may be taken in any finite separable overfield `M` of
`F`.  The proof deliberately runs purity on the tower `B ⊆ F ⊆ M`.
Consequently no descent statement identifying the normalization in `F`
with a subalgebra of the normalization in `M` is needed. -/
private theorem awayMap_formallyUnramified_of_embedded_normalization_etale
    {A : Type u} {K : Type v} {F : Type w} {M : Type z}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field F] [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F]
    [Field M] [Algebra K M] [Algebra A M] [IsScalarTower A K M]
    [Algebra F M] [IsScalarTower K F M] [IsScalarTower A F M]
    [FiniteDimensional F M] [Algebra.IsSeparable F M]
    {m : ℕ} (hm : 0 < m) {t y : A}
    (hreg : RingTheory.Sequence.IsRegular A [t, y])
    (hgen : Ideal.ofList [t, y] = maximalIdeal A)
    (β : F) (hdegree : Module.finrank K F = m)
    (hβpow : β ^ m = algebraMap K F (algebraMap A K t))
    (hβgen : IntermediateField.adjoin K {β} = ⊤)
    [Module.Finite A (integralClosure A M)]
    (hEtale : RingHom.Etale
      (Localization.awayMap
        (algebraMap A (integralClosure A M)) t)) :
    RingHom.FormallyUnramified
      (Localization.awayMap
        (algebraMap A (AdjoinRoot (X ^ m - C t))) t) := by
  let p : A[X] := X ^ m - C t
  let B := AdjoinRoot p
  let φ : B →ₐ[A] F :=
    pureRadicalAdjoinRootToField t β hβpow
  let : Algebra B F := φ.toRingHom.toAlgebra
  let : IsScalarTower A B F :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (φ.commutes a).symm
  let : IsFractionRing B F :=
    isFractionRing_adjoinRoot_of_pureRadical
      hm t β hdegree hβpow hβgen
  let φM : B →ₐ[A] M :=
    (IsScalarTower.toAlgHom A F M).comp φ
  let : Algebra B M := φM.toRingHom.toAlgebra
  let : IsScalarTower A B M :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (φM.commutes a).symm
  let : IsScalarTower B F M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsDomain B := (IsFractionRing.injective B F).isDomain _
  have hpMonic : p.Monic :=
    Polynomial.monic_X_pow_sub_C t hm.ne'
  let : Module.Finite A B := hpMonic.finite_adjoinRoot
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : IsRegularLocalRing B :=
    isRegularLocalRing_adjoinRoot_X_pow_sub_C_of_regular_parameters
      hm hreg hgen
  have hdimB : ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞) := by
    simpa [B, p] using
      (localRootCoverParameterList_length_eq_ringKrullDim
        (R := A) (n := m) (a := t) (rs := [y]) hm hreg hgen)
  let D := integralClosure A M
  let ψ : B →ₐ[A] D := IsIntegralClosure.lift A D M
  let : Algebra B D := ψ.toRingHom.toAlgebra
  let : IsScalarTower A B D :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (ψ.commutes a).symm
  let : IsScalarTower B D M :=
    IsScalarTower.of_algebraMap_eq fun b ↦
      (IsIntegralClosure.algebraMap_lift A D M b).symm
  let : IsIntegralClosure D B M :=
    IsIntegralClosure.tower_top (R := A) (A := B) (B := M) (C := D)
  let : Module.Finite B D :=
    Module.Finite.of_restrictScalars_finite A B D
  let E := integralClosure B M
  let e : E ≃ₐ[B] D := IsIntegralClosure.equiv B E M D
  let : Module.Finite B E :=
    Module.Finite.equiv e.symm.toLinearEquiv
  let : Module.Free B E :=
    (open _root_.EtaleFundamentalGroups.SpecialLocalPurity in
      integralClosure_free_of_isRegularLocalRing_dimension_two
        (A := B) (K := F) (L := M) hdimB)
  let : Module.Free B D := Module.Free.of_equiv e.toLinearEquiv
  let b : B := algebraMap A B t
  let S := Localization.Away t
  let Bs := Localization.Away b
  let Ds := Localization.Away (algebraMap A D t)
  let f : S →+* Bs := Localization.awayMap (algebraMap A B) t
  let mapBDs : B →+* Ds :=
    (algebraMap D Ds).comp (algebraMap B D)
  have hbUnit : IsUnit (mapBDs b) := by
    change IsUnit (algebraMap D Ds (ψ (algebraMap A B t)))
    rw [ψ.commutes]
    exact IsLocalization.Away.algebraMap_isUnit _
  let g : Bs →+* Ds := Localization.awayLift mapBDs b hbUnit
  let : Algebra S Bs := f.toAlgebra
  let : IsScalarTower A S Bs :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap A Bs a = f (algebraMap A S a)
      rw [show f (algebraMap A S a) =
        algebraMap B Bs (algebraMap A B a) by
          simp [f, S, Bs, b, IsLocalization.Away.map]]
      exact IsScalarTower.algebraMap_apply A B Bs a
  let : Algebra Bs Ds := g.toAlgebra
  let : IsScalarTower B Bs Ds :=
    IsScalarTower.of_algebraMap_eq fun q ↦ by
      change algebraMap B Ds q = g (algebraMap B Bs q)
      rw [show g (algebraMap B Bs q) = mapBDs q by simp [g]]
      exact IsScalarTower.algebraMap_apply B D Ds q
  have hcomp : g.comp f =
      Localization.awayMap (algebraMap A D) t := by
    apply IsLocalization.ringHom_ext (Submonoid.powers t)
    ext a
    simp only [RingHom.comp_apply]
    calc
      g (f (algebraMap A S a)) =
          g (algebraMap B Bs (algebraMap A B a)) := by
        rw [show f (algebraMap A S a) =
          algebraMap B Bs (algebraMap A B a) by
            simp [f, S, Bs, b, IsLocalization.Away.map]]
      _ = mapBDs (algebraMap A B a) := by simp [g]
      _ = algebraMap D Ds (ψ (algebraMap A B a)) := rfl
      _ = algebraMap D Ds (algebraMap A D a) := by rw [ψ.commutes]
      _ = Localization.awayMap (algebraMap A D) t
          (algebraMap A S a) := by
        simp [S, Ds, IsLocalization.Away.map]
  have hEtaleComp : RingHom.Etale (g.comp f) := by
    rw [hcomp]
    exact hEtale
  let : Algebra S Ds := (g.comp f).toAlgebra
  let : IsScalarTower S Bs Ds :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra.Etale S Ds := hEtaleComp.toAlgebra
  have hbD : algebraMap B D b = algebraMap A D t := by
    exact (IsScalarTower.algebraMap_apply A B D t).symm
  let : IsLocalization
      (Algebra.algebraMapSubmonoid D (Submonoid.powers b)) Ds := by
    change IsLocalization
      ((Submonoid.powers b).map (algebraMap B D)) Ds
    rw [Submonoid.map_powers, hbD]
    infer_instance
  let basisD := Module.Free.chooseBasis B D
  let basisDs :=
    basisD.localizationLocalization Bs (Submonoid.powers b) Ds
  let : Module.Free Bs Ds := Module.Free.of_basis basisDs
  let : Module.Finite Bs Ds := Module.Finite.of_basis basisDs
  let : Algebra.FormallyUnramified Bs Ds :=
    Algebra.FormallyUnramified.of_restrictScalars S Bs Ds
  let : Module.FinitePresentation Bs Ds :=
    Module.finitePresentation_of_finite Bs Ds
  let : Algebra.FinitePresentation Bs Ds :=
    Algebra.FinitePresentation.of_finitePresentation Bs Ds
  let : Algebra.Etale Bs Ds :=
    Algebra.Etale.of_formallyUnramified_of_flat
  let : Algebra.FormallyEtale Bs Ds := inferInstance
  have ht0 : t ≠ 0 :=
    (_root_.EtaleFundamentalGroups.SpecialLocalPurity.regular_pair_nonzero_and_isRelPrime
      hreg).1
  have htD : algebraMap A D t ≠ 0 := by
    intro htD
    apply ht0
    apply IsFractionRing.injective A K
    apply (algebraMap K M).injective
    calc
      algebraMap K M (algebraMap A K t) = algebraMap A M t :=
        (IsScalarTower.algebraMap_apply A K M t).symm
      _ = algebraMap D M (algebraMap A D t) :=
        IsScalarTower.algebraMap_apply A D M t
      _ = 0 := by rw [htD, map_zero]
      _ = algebraMap K M (algebraMap A K 0) := by simp
  let : IsDomain Ds := IsLocalization.Away.isDomain Ds htD
  let : Module.FaithfullyFlat Bs Ds := inferInstance
  have hFU : Algebra.FormallyUnramified S Bs :=
    formallyUnramified_of_formallyEtale_faithfullyFlat
      (R := S) (S := Bs) (T := Ds)
  change @Algebra.FormallyUnramified S Bs _ _ f.toAlgebra
  exact hFU

/--
For a selected intermediate field of a pure radical extension, etaleness of
its actual normalization off the selected boundary forces the intermediate
degree to be a unit on that boundary component.
-/
theorem selectedIntermediateRootExponent_isUnit_mod
    {A : Type u} {K : Type v} {L : Type w}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    {t y : A}
    (hreg : RingTheory.Sequence.IsRegular A [t, y])
    (hgen : Ideal.ofList [t, y] = maximalIdeal A)
    (hCharZero : CharZero (A ⧸ Ideal.span {t}))
    (α : L)
    (hpow : α ^ Module.finrank K L =
      algebraMap K L (algebraMap A K t))
    (hαgen : IntermediateField.adjoin K {α} = ⊤)
    (F : IntermediateField K L)
    [Module.Finite A (integralClosure A F)]
    (hEtale : RingHom.Etale
      (R := Localization.Away t)
      (S := Localization.Away (algebraMap A (integralClosure A F) t))
      (Localization.awayMap
        (algebraMap A (integralClosure A F)) t)) :
    IsUnit (Module.finrank K F : A ⧸ Ideal.span {t}) := by
  let : IsDomain A := isDomain_of_regularSystem [t, y] hreg hgen
  have ht : Prime t :=
    prime_of_mem_regularSystem hreg hgen (by simp)
  have hα : α ≠ 0 := by
    intro hα
    apply ht.ne_zero
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    rw [← hpow, hα, zero_pow (Module.finrank_pos.ne')]
    simp
  let m := Module.finrank K F
  have hm : 0 < m := Module.finrank_pos
  have hroots : ∀ ζ : L, ζ ^ Module.finrank K L = 1 →
      ζ ∈ Set.range (algebraMap K L) := fun ζ hζ ↦
    rootOfUnity_mem_fractionBase_of_primeParameter_pureRadical
      ht hCharZero α hpow hαgen ζ hζ
  obtain ⟨β, _hβval, hβpow, hβgenL, _hdegreeTower⟩ :=
    exists_intermediateField_generator_pow_eq_of_pureRadical
      α hα (algebraMap A K t) hpow hαgen hroots F
  have hβgen : IntermediateField.adjoin K ({β} : Set F) = ⊤ := by
    apply IntermediateField.lift_injective F
    simpa only [IntermediateField.lift_adjoin_simple,
      IntermediateField.lift_top] using hβgenL
  let p : A[X] := X ^ m - C t
  let B := AdjoinRoot p
  let b : B := algebraMap A B t
  let S := Localization.Away t
  let Bs := Localization.Away b
  let f : S →+* Bs := Localization.awayMap (algebraMap A B) t
  have hFU : RingHom.FormallyUnramified f := by
    simpa [f, S, Bs, b, B, p] using
      (awayMap_formallyUnramified_of_normalization_etale
        (A := A) (K := K) (F := F) hm hreg hgen β rfl
          hβpow hβgen hEtale)
  let : Algebra S Bs := f.toAlgebra
  let : Algebra.FormallyUnramified S Bs :=
    hFU
  let : IsScalarTower A S Bs :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap A Bs a = f (algebraMap A S a)
      rw [show f (algebraMap A S a) =
        algebraMap B Bs (algebraMap A B a) by
          simp [f, S, Bs, b, IsLocalization.Away.map]]
      exact IsScalarTower.algebraMap_apply A B Bs a
  let n₁ : Fin 1 → ℕ := fun _ ↦ m
  let a₁ : Fin 1 → A := fun _ ↦ t
  let a₁S : Fin 1 → S := fun _ ↦ algebraMap A S t
  let IR := iteratedRadical S 1 n₁ a₁S
  let eLoc : S ⊗[A] B ≃ₐ[S] Bs := by
    let Tloc := Localization
      (Algebra.algebraMapSubmonoid B (Submonoid.powers t))
    letI : IsLocalization
        (Algebra.algebraMapSubmonoid B (Submonoid.powers t)) Bs := by
      change IsLocalization
        ((Submonoid.powers t).map (algebraMap A B)) Bs
      rw [Submonoid.map_powers]
      change IsLocalization (Submonoid.powers b) Bs
      infer_instance
    let eB : Tloc ≃ₐ[B] Bs :=
      IsLocalization.algEquiv
        (Algebra.algebraMapSubmonoid B (Submonoid.powers t)) Tloc Bs
    let eS : Tloc ≃ₐ[S] Bs :=
      { eB.toRingEquiv with
        commutes' := fun s ↦ by
          have hmaps : eB.toRingHom.comp (algebraMap S Tloc) =
              algebraMap S Bs := by
            apply IsLocalization.ringHom_ext (Submonoid.powers t)
            ext a
            change eB (algebraMap S Tloc (algebraMap A S a)) =
              algebraMap S Bs (algebraMap A S a)
            rw [← IsScalarTower.algebraMap_apply A S Tloc,
              ← IsScalarTower.algebraMap_apply A S Bs,
              IsScalarTower.algebraMap_apply A B Tloc,
              IsScalarTower.algebraMap_apply A B Bs,
              eB.commutes]
          exact RingHom.congr_fun hmaps s }
    exact (Localization.tensorRightAlgEquiv
      (Submonoid.powers t) B).trans eS
  let eBaseChange : S ⊗[A] B ≃ₐ[S] IR := by
    let e₀ := oneRootBaseChangeAlgEquiv (A := A) (S := S) m t
    let e₁ := oneIteratedRadicalAlgEquiv S m (algebraMap A S t)
    exact (show S ⊗[A] B ≃ₐ[S]
        AdjoinRoot (X ^ m - C (algebraMap A S t)) by
          simpa [B, p] using e₀).trans
      (show AdjoinRoot (X ^ m - C (algebraMap A S t)) ≃ₐ[S] IR by
        simpa [IR, n₁, a₁S] using e₁.symm)
  let eRoot : Bs ≃ₐ[S] IR := eLoc.symm.trans eBaseChange
  let : Algebra.FormallyUnramified S IR :=
    Algebra.FormallyUnramified.of_equiv eRoot
  let : IsLocalization.Away
      (∏ i ∈ (Finset.univ : Finset (Fin 1)), a₁ i) S := by
    simpa [a₁, S] using
      (inferInstance : IsLocalization.Away t S)
  let : Algebra.FormallyUnramified S
      (iteratedRadical S 1 n₁
        (fun i ↦ algebraMap A S (a₁ i))) := by
    simpa [IR, a₁S, a₁] using
      (inferInstance : Algebra.FormallyUnramified S IR)
  have hmUnitA : IsUnit (m : A) := by
    have hall :=
      all_exponents_isUnit_of_formallyUnramified_boundaryIteratedRadical
        (R := A) (S := S) (r := 1) (t := a₁)
        (fun _ ↦ by simpa [a₁] using ht)
        (fun _ ↦ by simpa [a₁] using hCharZero)
        n₁ (fun _ ↦ by simpa [n₁] using hm)
    simpa [n₁] using hall (0 : Fin 1)
  simpa [m] using
    hmUnitA.map (Ideal.Quotient.mk (Ideal.span ({t} : Set A)))

/-- Embedded-normalization form of
`selectedIntermediateRootExponent_isUnit_mod`.

The intermediate pure-root field `F` need not itself carry the normalization
for which Away etaleness has been proved.  It is enough that `F` embeds as a
field subextension of a finite separable field `M` and that the normalization
of the original regular local base in `M` is etale off the selected
parameter.  This is the form used after choosing one component of the
other-root tensor product. -/
theorem selectedIntermediateRootExponent_isUnit_mod_of_embedded_normalization_etale
    {A : Type u} {K : Type v} {L : Type w} {M : Type z}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    [Field M] [Algebra K M] [Algebra A M] [IsScalarTower A K M]
    {t y : A}
    (hreg : RingTheory.Sequence.IsRegular A [t, y])
    (hgen : Ideal.ofList [t, y] = maximalIdeal A)
    (hCharZero : CharZero (A ⧸ Ideal.span ({t} : Set A)))
    (α : L)
    (hpow : α ^ Module.finrank K L =
      algebraMap K L (algebraMap A K t))
    (hαgen : IntermediateField.adjoin K {α} = ⊤)
    (F : IntermediateField K L)
    [Algebra F M] [IsScalarTower K F M] [IsScalarTower A F M]
    [FiniteDimensional F M] [Algebra.IsSeparable F M]
    [Module.Finite A (integralClosure A M)]
    (hEtale : RingHom.Etale
      (Localization.awayMap
        (algebraMap A (integralClosure A M)) t)) :
    IsUnit (Module.finrank K F : A ⧸ Ideal.span ({t} : Set A)) := by
  let : IsDomain A := isDomain_of_regularSystem [t, y] hreg hgen
  have ht : Prime t :=
    prime_of_mem_regularSystem hreg hgen (by simp)
  have hα : α ≠ 0 := by
    intro hα
    apply ht.ne_zero
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    rw [← hpow, hα, zero_pow (Module.finrank_pos.ne')]
    simp
  let m := Module.finrank K F
  have hm : 0 < m := Module.finrank_pos
  have hroots : ∀ ζ : L, ζ ^ Module.finrank K L = 1 →
      ζ ∈ Set.range (algebraMap K L) := fun ζ hζ ↦
    rootOfUnity_mem_fractionBase_of_primeParameter_pureRadical
      ht hCharZero α hpow hαgen ζ hζ
  obtain ⟨β, _hβval, hβpow, hβgenL, _hdegreeTower⟩ :=
    exists_intermediateField_generator_pow_eq_of_pureRadical
      α hα (algebraMap A K t) hpow hαgen hroots F
  have hβgen : IntermediateField.adjoin K ({β} : Set F) = ⊤ := by
    apply IntermediateField.lift_injective F
    simpa only [IntermediateField.lift_adjoin_simple,
      IntermediateField.lift_top] using hβgenL
  let p : A[X] := X ^ m - C t
  let B := AdjoinRoot p
  let b : B := algebraMap A B t
  let S := Localization.Away t
  let Bs := Localization.Away b
  let f : S →+* Bs := Localization.awayMap (algebraMap A B) t
  have hFU : RingHom.FormallyUnramified f := by
    simpa [f, S, Bs, b, B, p] using
      (awayMap_formallyUnramified_of_embedded_normalization_etale
        (A := A) (K := K) (F := F) (M := M) hm hreg hgen β rfl
          hβpow hβgen hEtale)
  let : Algebra S Bs := f.toAlgebra
  let : Algebra.FormallyUnramified S Bs := hFU
  let : IsScalarTower A S Bs :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap A Bs a = f (algebraMap A S a)
      rw [show f (algebraMap A S a) =
        algebraMap B Bs (algebraMap A B a) by
          simp [f, S, Bs, b, IsLocalization.Away.map]]
      exact IsScalarTower.algebraMap_apply A B Bs a
  let n₁ : Fin 1 → ℕ := fun _ ↦ m
  let a₁ : Fin 1 → A := fun _ ↦ t
  let a₁S : Fin 1 → S := fun _ ↦ algebraMap A S t
  let IR := iteratedRadical S 1 n₁ a₁S
  let eLoc : S ⊗[A] B ≃ₐ[S] Bs := by
    let Tloc := Localization
      (Algebra.algebraMapSubmonoid B (Submonoid.powers t))
    letI : IsLocalization
        (Algebra.algebraMapSubmonoid B (Submonoid.powers t)) Bs := by
      change IsLocalization
        ((Submonoid.powers t).map (algebraMap A B)) Bs
      rw [Submonoid.map_powers]
      change IsLocalization (Submonoid.powers b) Bs
      infer_instance
    let eB : Tloc ≃ₐ[B] Bs :=
      IsLocalization.algEquiv
        (Algebra.algebraMapSubmonoid B (Submonoid.powers t)) Tloc Bs
    let eS : Tloc ≃ₐ[S] Bs :=
      { eB.toRingEquiv with
        commutes' := fun s ↦ by
          have hmaps : eB.toRingHom.comp (algebraMap S Tloc) =
              algebraMap S Bs := by
            apply IsLocalization.ringHom_ext (Submonoid.powers t)
            ext a
            change eB (algebraMap S Tloc (algebraMap A S a)) =
              algebraMap S Bs (algebraMap A S a)
            rw [← IsScalarTower.algebraMap_apply A S Tloc,
              ← IsScalarTower.algebraMap_apply A S Bs,
              IsScalarTower.algebraMap_apply A B Tloc,
              IsScalarTower.algebraMap_apply A B Bs,
              eB.commutes]
          exact RingHom.congr_fun hmaps s }
    exact (Localization.tensorRightAlgEquiv
      (Submonoid.powers t) B).trans eS
  let eBaseChange : S ⊗[A] B ≃ₐ[S] IR := by
    let e₀ := oneRootBaseChangeAlgEquiv (A := A) (S := S) m t
    let e₁ := oneIteratedRadicalAlgEquiv S m (algebraMap A S t)
    exact (show S ⊗[A] B ≃ₐ[S]
        AdjoinRoot (X ^ m - C (algebraMap A S t)) by
          simpa [B, p] using e₀).trans
      (show AdjoinRoot (X ^ m - C (algebraMap A S t)) ≃ₐ[S] IR by
        simpa [IR, n₁, a₁S] using e₁.symm)
  let eRoot : Bs ≃ₐ[S] IR := eLoc.symm.trans eBaseChange
  let : Algebra.FormallyUnramified S IR :=
    Algebra.FormallyUnramified.of_equiv eRoot
  let : IsLocalization.Away
      (∏ i ∈ (Finset.univ : Finset (Fin 1)), a₁ i) S := by
    simpa [a₁, S] using
      (inferInstance : IsLocalization.Away t S)
  let : Algebra.FormallyUnramified S
      (iteratedRadical S 1 n₁
        (fun i ↦ algebraMap A S (a₁ i))) := by
    simpa [IR, a₁S, a₁] using
      (inferInstance : Algebra.FormallyUnramified S IR)
  have hmUnitA : IsUnit (m : A) := by
    have hall :=
      all_exponents_isUnit_of_formallyUnramified_boundaryIteratedRadical
        (R := A) (S := S) (r := 1) (t := a₁)
        (fun _ ↦ by simpa [a₁] using ht)
        (fun _ ↦ by simpa [a₁] using hCharZero)
        n₁ (fun _ ↦ by simpa [n₁] using hm)
    simpa [n₁] using hall (0 : Fin 1)
  simpa [m] using
    hmUnitA.map (Ideal.Quotient.mk (Ideal.span ({t} : Set A)))

end EtaleFundamentalGroups.Kummer
