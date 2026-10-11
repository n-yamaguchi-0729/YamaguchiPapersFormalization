/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Full.ActualRootFirstFinite
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.GaloisFullRootCoverActualRoot
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Full.ActualRootFirstTower
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.ActiveRoot.ConditionalLocalizationEtale
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.FullRootCover.SelectedBranchEtale

/-!
# Actual-root-first fixed-component localization

The height-one prime and its contraction are fixed before the generic tensor
component is introduced.  This is the order used by the active-root source
theorem, and keeps the actual-root-first coordinate calculation independent
of the large component-localization telescope.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uA uK uL

/-- For an active other branch, fix the full-cover height-one prime first.
The actual-root-first finite faithful presentation then supplies the literal
localized normalization for every generic tensor component. -/
theorem
    localization_integralClosure_galoisFullRootCover_actualRootFirst_fixedComponent_etale
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {s r : ℕ} {f : A} {t : Fin (s + 2) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (s + 2))
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P)
    (sigma : Equiv.Perm (Fin (s + 1)))
    (k : Fin (s + 1))
    (hkActive : (i.succAbove (sigma k)).1 < r)
    (htkP : t (i.succAbove (sigma k)) ∈ P)
    (hCharZero : CharZero
      (A ⧸ Ideal.span ({t (i.succAbove (sigma k))} : Set A))) :
    let e := heightTwoOtherBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let N := heightTwoSelectedBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let R := Localization.AtPrime P
    let n := heightTwoConditionalOtherExponent t i r P e sigma
    let a : Fin (s + 1) → R := heightTwoConditionalOtherRadicand t i P sigma
    let B := iteratedRadical R (s + 1) n a
    let y : R := algebraMap A R (t i)
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let D := AdjoinRoot F
    ∀ (hn : ∀ l, 0 < n l) [IsDomain D] [IsIntegrallyClosed D]
      (q : Ideal D) [q.IsPrime], q.height = 1 →
      q.under B = Ideal.span
        ({iteratedRadicalRoot R n a k} : Set B) →
      let : Algebra R K :=
        localizationAtPrimeToFractionFieldAlgebra (K := K) P
      let : IsFractionRing R K :=
        localizationAtPrimeToFractionField_isFractionRing (K := K) P
      let K' := FractionRing D
      let : Algebra K K' :=
        galoisFullRootCoverFractionFieldAlgebra n a hn N
          (heightTwoSelectedBranchGaloisRamificationIndex_pos
            (K := K) (L := L) t hNC i) y
      ∀ (m : Ideal (K' ⊗[K] L)) (hm : m.IsMaximal),
        let : m.IsMaximal := hm
        let M := GenericTensorFieldComponent m
        let : Algebra D M :=
          genericTensorFieldComponentLeftScalarAlgebra (R := D) m
        let : SMul D M :=
          (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
        let : IsScalarTower D K' M :=
          IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        let Q := Localization.AtPrime q
        let : Algebra Q K' :=
          localizationAtPrimeToFractionFieldAlgebra (K := K') q
        let : IsFractionRing Q K' :=
          localizationAtPrimeToFractionField_isFractionRing (K := K') q
        let : Algebra Q M :=
          localizationAtPrimeToExtensionAlgebra (K := K') (L := M) q
        let : SMul Q M :=
          (localizationAtPrimeToExtensionAlgebra (K := K') (L := M) q).toSMul
        let : IsScalarTower Q K' M :=
          localizationAtPrimeToFractionFieldToExtension_isScalarTower
            (K := K') (L := M) q
        let : IsScalarTower D Q M :=
          localizationAtPrimeToExtension_isScalarTower
            (K := K') (L := M) q
        let : Algebra (integralClosure D M) (integralClosure Q M) :=
          integralClosureLocalizationAlgebra (L := M) q
        Algebra.Etale Q
          (Localization (Algebra.algebraMapSubmonoid
            (integralClosure D M) q.primeCompl)) := by
  intro e N R n a B y F D hn hDomainD hIntegrallyClosedD
    q hqPrime hqHeight hunderB aRK hFracRK K' aKK'
  have hN : 0 < N :=
    heightTwoSelectedBranchGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC i
  have hqEq : q = Ideal.span
      ({algebraMap B D (iteratedRadicalRoot R n a k)} : Set D) :=
    splitStrictNormalCrossings_heightTwo_galoisFullRootCover_heightOnePrime_eq_span_actualRoot
      (A := A) (K := K) (L := L) hNC i P hP htiP
        sigma k hkActive htkP q hqHeight hunderB
  let : Module.FaithfullyFlat R B := faithfullyFlat_iteratedRadical n a hn
  let : FaithfulSMul R B := Module.FaithfullyFlat.faithfulSMul
  let : Nontrivial B :=
    (FaithfulSMul.algebraMap_injective R B).nontrivial
  let : Module.FaithfullyFlat B D :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hN (algebraMap R B y)
  let : FaithfulSMul B D := Module.FaithfullyFlat.faithfulSMul
  let : FaithfulSMul R D := FaithfulSMul.trans R B D
  let : FaithfulSMul R K' := FaithfulSMul.trans R D K'
  let : IsScalarTower R K K' :=
    galoisFullRootCoverFractionField_isScalarTower n a hn N hN y
  have hother : ∀ l, l ≠ k → n l = 1 :=
    heightTwoConditionalOtherExponent_eq_one_of_ne_actual
      hNC i P hP htiP e sigma k hkActive htkP
  have hnk : 0 < n k := hn k
  let gx : R[X] := X ^ n k - C (a k)
  let Xroot := AdjoinRoot gx
  let qx := Ideal.span ({AdjoinRoot.root gx} : Set Xroot)
  let : Algebra Xroot D :=
    fullRootCoverActualRootFirstAlgebra n a k hother N y
  let : Module.Finite Xroot D :=
    fullRootCoverActualRootFirst_moduleFinite n a k hother N hN y
  let : Module.FaithfullyFlat Xroot D :=
    fullRootCoverActualRootFirst_faithfullyFlat
      n a k hother hnk N hN y
  let : FaithfulSMul Xroot D := Module.FaithfullyFlat.faithfulSMul
  let : IsScalarTower R Xroot D :=
    fullRootCoverActualRootFirst_isScalarTower n a k hother N y
  have hunder : q.under Xroot = qx := by
    rw [hqEq]
    exact fullRootCoverActualRootFirst_under_eq_span_root
      n a k hother hnk N hN y
  exact (
  localization_integralClosure_strictNormalCrossingsGaloisConditionalActiveRoot_fixedComponent_etale
    (K := K) (L := L) hNC i P hP sigma k hkActive htkP hCharZero
      (D := D) q hunder)

end EtaleFundamentalGroups.Kummer

end
