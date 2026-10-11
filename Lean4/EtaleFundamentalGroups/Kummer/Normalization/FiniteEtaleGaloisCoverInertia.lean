/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Away.FunctionFieldNormalization
import EtaleFundamentalGroups.GaloisCovers.FunctionField
import EtaleFundamentalGroups.Kummer.Normalization.FiniteSeparableInertia

/-!
# Inertia from a finite-etale Galois cover of a normal-crossings complement

A categorical Galois cover of the complement `Spec (A[1/f])` supplies all
field-theoretic and boundary-etaleness inputs of the local Kummer inertia
theorem.  In particular, neither a separately postulated Galois extension nor
a separately postulated etale normalization is present in the source-facing
statement.
-/

noncomputable section

open AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Kummer

universe u uk

/-- The local equation in a split strict-normal-crossings chart is nonzero. -/
theorem splitStrictNormalCrossings_boundaryEquation_ne_zero
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    {d r : ℕ} {f : A} {t : Fin d → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r) : f ≠ 0 := by
  apply (hNC.2.2.2.2.1.ne_zero_iff).mpr
  rw [boundaryProduct]
  exact Finset.prod_ne_zero_iff.mpr fun j hj ↦
    (hNC.2.2.2.1 j (Finset.mem_filter.mp hj).2).ne_zero

/-- A categorical finite-etale Galois cover of the complement of a split
strict-normal-crossings boundary has normalization inertia of order prime to
the residue characteristic along every active component.

Only the normal Noetherian local hypotheses used by the local theorem occur;
there is no finite-type, Nagata, or arithmetic-base assumption. -/
theorem
    splitStrictNormalCrossings_finiteEtaleGaloisCover_normalizationInertia_coprime
    {A : Type u} {k : Type uk}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [IsIntegrallyClosed A]
    [CommRing k] [Nontrivial k]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (hCharZero : ∀ j, j.1 < r →
      CharZero (A ⧸ Ideal.span ({t j} : Set A)))
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) :
    let hf := splitStrictNormalCrossings_boundaryEquation_ne_zero hNC
    let S := Localization.Away f
    letI : IsDomain S := IsLocalization.Away.isDomain S hf
    letI : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
        (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    ∀ hY : CategoryTheory.PreGaloisCategory.IsGalois Y,
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K := (Spec (.of S)).functionField
    let L := Y.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    letI : Algebra A K :=
      localizationAwaySpecFunctionFieldAlgebra f hf
    letI : Algebra A L := finiteEtaleAwayFunctionFieldAlgebra f hf Y
    letI : IsScalarTower A K L :=
      finiteEtaleAway_functionField_isScalarTower f hf Y
    letI : IsFractionRing A K :=
      localizationAwaySpecFunctionField_isFractionRing f hf
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected Y
    letI : _root_.IsGalois K L :=
      isGalois_functionField_of_isGalois_finiteEtale Y hY
    ∀ (Q : Ideal (integralClosure A L)) (_ : Q.IsPrime),
      Q.LiesOver (Ideal.span ({t i} : Set A)) →
      ∀ (_phi : (A ⧸ Ideal.span ({t i} : Set A)) →+* k)
        (p : ℕ) (_ : CharP k p), p.Prime →
        Nat.Coprime
          (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) p := by
  dsimp only
  intro hY
  have hf : f ≠ 0 :=
    splitStrictNormalCrossings_boundaryEquation_ne_zero hNC
  let S := Localization.Away f
  let : IsDomain S := IsLocalization.Away.isDomain S hf
  let : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let X := Spec (.of S)
  let K : Type u := X.functionField
  let L : Type u := Y.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  let : Algebra A K :=
    localizationAwaySpecFunctionFieldAlgebra f hf
  let : Algebra A L := finiteEtaleAwayFunctionFieldAlgebra f hf Y
  let : IsScalarTower A K L :=
    finiteEtaleAway_functionField_isScalarTower f hf Y
  let : IsFractionRing A K :=
    localizationAwaySpecFunctionField_isFractionRing f hf
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  have hAway : (Localization.awayMap
      (algebraMap A (integralClosure A L)) f).Etale :=
    localization_away_integralClosure_functionField_etale_of_finiteEtale
      f hf Y
  intro Q hQprime hQLiesOver phi p hpChar hp
  exact
    splitStrictNormalCrossings_normalizationInertia_coprime_of_isIntegrallyClosed
      (K := K) (L := L) hNC i hi hCharZero hAway Q phi p hp

end EtaleFundamentalGroups.Kummer

end
