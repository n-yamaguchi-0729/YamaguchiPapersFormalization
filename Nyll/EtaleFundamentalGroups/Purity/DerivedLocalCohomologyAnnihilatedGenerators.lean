/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyGeneratorCountDomain
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyMayerVietoris
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPrincipalAnnihilated
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyRadical
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Generator-count vanishing with an annihilated coefficient module

If one generator of the support ideal annihilates the coefficient module,
local cohomology vanishes above the number of remaining generators.  The
proof uses strong induction on that number.  Mayer--Vietoris removes one
remaining generator; its intersection term has the same radical as the
product ideal, which again has an annihilating generator and fewer remaining
generators.  The induction starts with principal-support degree-one
vanishing for an annihilated module.
-/

noncomputable section

open CategoryTheory Limits

namespace EtaleFundamentalGroups

universe u

/-- Over a Noetherian local domain, an annihilating support generator lowers
by one the generator-count bound for local cohomology of the coefficient
module.  No regularity or nonzero assumption on the annihilating generator
is needed. -/
theorem derivedLocalCohomology_ofList_cons_isZero_of_smul_id_eq_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    (x : R) (xs : List R) (M : ModuleCat.{u} R)
    (hx : x • 𝟙 M = 0) (i : ℕ) (hi : xs.length < i) :
    IsZero (derivedLocalCohomology (Ideal.ofList (x :: xs)) M i) := by
  suffices h : ∀ (n : ℕ) (z : R) (zs : List R),
      zs.length = n → z • 𝟙 M = 0 →
      ∀ (j : ℕ), zs.length < j →
        IsZero (derivedLocalCohomology (Ideal.ofList (z :: zs)) M j) by
    exact h xs.length x xs rfl hx i hi
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z zs hlen hz j hj
    cases zs with
    | nil =>
        by_cases hjOne : j = 1
        · subst j
          simpa only [Ideal.ofList_singleton] using
            derivedLocalCohomology_span_singleton_isZero_one_of_smul_id_eq_zero
              z M hz
        · exact derivedLocalCohomology_ofList_isZero_of_isDomain
            [z] M j (by
              simp only [List.length_cons, List.length_nil] at hj ⊢
              omega)
    | cons y ys =>
        have hysLength : ys.length < n := by
          simp only [List.length_cons] at hlen
          omega
        have hjTwo : 2 ≤ j := by
          simp only [List.length_cons] at hj
          omega
        let J : Ideal R := Ideal.ofList (z :: ys)
        let products : List R := ys.map fun a ↦ y * a
        have hproductsLength : products.length < n := by
          simpa only [products, List.length_map] using hysLength
        have hyz : (y * z) • 𝟙 M = 0 := by
          have h := congrArg (fun f : M ⟶ M ↦ y • f) hz
          simpa only [smul_smul, smul_zero] using h
        have hProduct :
            IsZero (derivedLocalCohomology
              (Ideal.ofList ((y * z) :: products)) M (j - 1)) :=
          ih products.length hproductsLength (y * z) products rfl hyz
            (j - 1) (by
              simp only [products, List.length_map, List.length_cons] at hj ⊢
              omega)
        have hInfRadical :
            (Ideal.span {y} ⊓ J).radical =
              (Ideal.ofList ((y * z) :: products)).radical := by
          calc
            (Ideal.span {y} ⊓ J).radical =
                (Ideal.span {y}).radical ⊓ J.radical :=
              Ideal.radical_inf (Ideal.span {y}) J
            _ = (Ideal.span {y} * J).radical :=
              (Ideal.radical_mul (Ideal.span {y}) J).symm
            _ = (Ideal.ofList ((y * z) :: products)).radical :=
              congrArg Ideal.radical (span_singleton_mul_ofList y (z :: ys))
        have hInf :
            IsZero (derivedLocalCohomology
              (Ideal.span {y} ⊓ J) M (j - 1)) :=
          hProduct.of_iso
            (derivedLocalCohomologyIsoOfSameRadical hInfRadical M (j - 1))
        have hPrincipal :
            IsZero (derivedLocalCohomology (Ideal.span {y}) M j) := by
          have h := derivedLocalCohomology_ofList_isZero_of_isDomain
            [y] M j (by
              simp only [List.length_cons, List.length_nil]
              omega)
          simpa only [Ideal.ofList_singleton] using h
        have hTail : IsZero (derivedLocalCohomology J M j) :=
          ih ys.length hysLength z ys rfl hz j (by
            simp only [List.length_cons] at hj
            omega)
        have hSupport :
            Ideal.ofList (z :: y :: ys) = Ideal.span {y} ⊔ J := by
          change Ideal.ofList (z :: y :: ys) =
            Ideal.span {y} ⊔ Ideal.ofList (z :: ys)
          simp only [Ideal.ofList_cons]
          exact sup_left_comm (Ideal.span {z}) (Ideal.span {y}) (Ideal.ofList ys)
        rw [hSupport]
        exact derivedLocalCohomology_sup_isZero_of_mayerVietoris
          (Ideal.span {y}) J M (j - 1) j (by omega) hInf hPrincipal hTail

end EtaleFundamentalGroups

end
