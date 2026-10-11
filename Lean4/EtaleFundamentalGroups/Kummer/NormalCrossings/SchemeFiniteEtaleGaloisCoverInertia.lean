/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Spectrum.Prime.Defs
import EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeSelectedBranch
import EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverInertia
import EtaleFundamentalGroups.LocalGeometry.RegularLocal.DimensionTwoIntegrallyClosed

/-!
# Scheme normal crossings and inertia of local Galois covers

A height-one divisor branch below a height-two point is selected by the
scheme-theoretic strict-normal-crossings data.  Every categorical Galois
finite-etale cover of the resulting boundary complement then has tame
normalization inertia along a prime over that selected branch.
-/

noncomputable section

open AlgebraicGeometry
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups
open EtaleFundamentalGroups.Kummer

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u uk

/-- Scheme-theoretic strict normal crossings at a height-two point produce a
local split chart on which every categorical finite-etale Galois cover has
normalization inertia prime to the selected residue characteristic.

The local ring is proved normal from its regular height-two geometry.  No
finite-type, Nagata, or arithmetic-base hypothesis is used. -/
theorem IsStrictNormalCrossings.exists_localSplitChart_galoisCover_inertia_coprime
    {X : Scheme.{u}} {I : X.IdealSheafData} {x : X}
    {k : Type uk} [CommRing k] [Nontrivial k]
    (hI : I.IsStrictNormalCrossings)
    (P : AlgebraicGeometry.Spec (X.presheaf.stalk x))
    (hPheight : P.asIdeal.height = 2)
    (q : Ideal (X.presheaf.stalk x)) [q.IsPrime]
    (hqheight : q.height = 1)
    (hIq : I.stalkIdeal x ≤ q) (hqP : q ≤ P.asIdeal) :
    let : P.asIdeal.IsPrime := P.isPrime
    let A := X.presheaf.stalk x
    let V := Localization.AtPrime P.asIdeal
    let qV := q.map (algebraMap A V)
    ∃ (r : ℕ) (t : Fin 2 → V) (i : Fin 2)
      (_ : IsDomain V) (_ : IsRegularRing V)
      (_ : IsIntegrallyClosed V)
      (hNC : IsSplitStrictNormalCrossingsAt (boundaryProduct t r) t r),
      i.1 < r ∧ qV = Ideal.span ({t i} : Set V) ∧
      ∀ (_hCharZero : ∀ j, j.1 < r →
          CharZero (V ⧸ Ideal.span ({t j} : Set V)))
        (Y : FiniteEtale
          (Spec (.of (Localization.Away (boundaryProduct t r))))),
        let f := boundaryProduct t r
        let hf :=
          splitStrictNormalCrossings_boundaryEquation_ne_zero hNC
        let S := Localization.Away f
        let : IsDomain S := IsLocalization.Away.isDomain S hf
        let : IsIntegrallyClosed S :=
          isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
            (Submonoid.powers_le.mpr
              (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
        ∀ hY : CategoryTheory.PreGaloisCategory.IsGalois Y,
        let : IsIntegral Y.left :=
          isIntegral_left_of_isConnected_finiteEtale Y
        let K := (Spec (.of S)).functionField
        let L := Y.left.functionField
        let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
        let : Algebra V K :=
          localizationAwaySpecFunctionFieldAlgebra f hf
        let : Algebra V L := finiteEtaleAwayFunctionFieldAlgebra f hf Y
        let : IsScalarTower V K L :=
          finiteEtaleAway_functionField_isScalarTower f hf Y
        let : IsFractionRing V K :=
          localizationAwaySpecFunctionField_isFractionRing f hf
        let : FiniteDimensional K L :=
          finiteDimensional_functionField_of_finiteEtale_isConnected Y
        let : _root_.IsGalois K L :=
          isGalois_functionField_of_isGalois_finiteEtale Y hY
        ∀ (Q : Ideal (integralClosure V L)) (_ : Q.IsPrime),
          Q.LiesOver qV →
          ∀ (_phi : (V ⧸ Ideal.span ({t i} : Set V)) →+* k)
            (p : ℕ) (_ : CharP k p), p.Prime →
            Nat.Coprime
              (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) p := by
  intro hPPrime A V qV
  obtain ⟨r, t, i, hVdomain, hVregular, hNC, hi, hqi⟩ :=
    hI.exists_localSplitChart_with_selectedBranch P hPheight q
      hqheight hIq hqP
  let : IsRegularLocalRing V :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing V
  have hdimV : ringKrullDim V = ((2 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ringKrullDim V = (P.asIdeal.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal V
      _ = ((2 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hPheight
  have hVnormal : IsIntegrallyClosed V :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdimV
  refine ⟨r, t, i, hVdomain, hVregular, hVnormal, hNC, hi, hqi, ?_⟩
  intro hCharZero Y f hf S sDomain sNormal hY yIntegral K L
    klAlgebra vkAlgebra vlAlgebra vklTower vFraction klFinite klGalois
    Q hQprime hQq phi p hpChar hp
  have hQbranch : Q.LiesOver (Ideal.span ({t i} : Set V)) := by
    rw [← hqi]
    exact hQq
  exact
    splitStrictNormalCrossings_finiteEtaleGaloisCover_normalizationInertia_coprime
      (A := V) (k := k) (d := 1) (r := r) (f := f) (t := t)
      hNC i hi hCharZero Y hY Q hQprime hQbranch phi p hpChar hp

end AlgebraicGeometry.Scheme.IdealSheafData

end
