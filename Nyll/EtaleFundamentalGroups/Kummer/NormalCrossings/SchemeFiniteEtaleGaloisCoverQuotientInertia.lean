/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Spectrum.Prime.Defs
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeFiniteEtaleGaloisCoverInertia
import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverIdealCoprimality

/-!
# Scheme normal crossings and inertia in pointed finite Galois quotients

The strict-normal-crossings chart at a height-two point selects a height-one branch.  The
normalization-prime inertia over that branch maps to a subgroup of every pointed finite Galois
quotient whose order is prime to the selected residue characteristic.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups
open EtaleFundamentalGroups.Kummer

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u uk

/-- At a height-two strict-normal-crossings point, the image of normalization-prime inertia
in every pointed finite Galois quotient has order prime to the selected residue
characteristic.  No finite-type, Nagata, or arithmetic-base hypothesis is used. -/
theorem IsStrictNormalCrossings.exists_localSplitChart_galoisCover_quotientIdealInertia_coprime
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
        ∀ {Omega : Type u} [Field Omega] [IsSepClosed Omega]
          (xi : Spec (.of Omega) ⟶ Spec (.of S))
          (y : (FiniteEtale.fiber xi).obj Y)
          (Q : Ideal (integralClosure V L)) (_ : Q.IsPrime),
          Q.LiesOver qV →
          ∀ (_phi : (V ⧸ Ideal.span ({t i} : Set V)) →+* k)
            (p : ℕ) (_ : CharP k p), p.Prime →
            let : IsFractionRing (integralClosure V L) L :=
              IsIntegralClosure.isFractionRing_of_finite_extension
                V K L (integralClosure V L)
            let : MulSemiringAction Gal(L/K) (integralClosure V L) :=
              IsIntegralClosure.MulSemiringAction
                V K L (integralClosure V L)
            let : MulSemiringAction (Aut Y)ᵐᵒᵖ (integralClosure V L) :=
              finiteEtaleGaloisCoverNormalizationAction
                Y hY V (integralClosure V L)
            Nat.Coprime
              (Nat.card
                (Subgroup.map
                  (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
                  (Subgroup.comap
                    (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
                    (Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ)))) p := by
  intro hPPrime A V qV
  obtain ⟨r, t, i, hVdomain, hVregular, hVnormal, hNC, hi, hqi, _⟩ :=
    hI.exists_localSplitChart_galoisCover_inertia_coprime
      (k := k) P hPheight q hqheight hIq hqP
  refine ⟨r, t, i, hVdomain, hVregular, hVnormal, hNC, hi, hqi, ?_⟩
  intro hCharZero Y f hf S sDomain sNormal hY yIntegral K L
    klAlgebra vkAlgebra vlAlgebra vklTower vFraction klFinite klGalois
    Omega instField instSepClosed xi y Q hQprime hQq phi p hpChar hp
    normalizationFractionRing galoisAction coverAction
  have hQbranch : Q.LiesOver (Ideal.span ({t i} : Set V)) := by
    rw [← hqi]
    exact hQq
  exact
    splitStrictNormalCrossings_finiteEtaleGaloisCover_quotientIdealInertia_coprime
      (A := V) (k := k) (d := 1) (r := r) (f := f) (t := t)
      hNC i hi hCharZero Y hY xi y Q hQprime hQbranch phi p hpChar hp

end AlgebraicGeometry.Scheme.IdealSheafData
