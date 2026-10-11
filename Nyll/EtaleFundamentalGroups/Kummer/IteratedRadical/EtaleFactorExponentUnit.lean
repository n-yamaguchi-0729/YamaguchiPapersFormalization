/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.Etale
import Nyll.EtaleFundamentalGroups.Kummer.Descent.FormallyUnramifiedDescent
import Nyll.EtaleFundamentalGroups.Kummer.IteratedRadical.BaseChange
import Nyll.EtaleFundamentalGroups.Kummer.Descent.MultiAwayUnitDescent

/-!
# Exponent units from an etale factor of an iterated radical

Let `B / A` be the full positive diagonal iterated radical along prime
boundary parameters.  If `D / B` is formally etale and faithfully flat, and
the underlying map `A -> D` is etale after removing the whole boundary, then
every radical exponent is a unit in `A`.

The proof localizes the complete diagram at the boundary product.  Formal
unramifiedness of the localized composite descends from the localized factor
to the localized iterated radical by faithful flatness.  The explicit
iterated-radical derivative obstruction then makes every exponent invertible
on the complement, and prime-boundary descent brings the units back to `A`.

No finiteness hypothesis on `D / B` is needed for this terminal consumer.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped BigOperators TensorProduct

universe u

/--
An etale faithfully-flat factor over the full iterated radical detects that
all radical exponents are units, provided the composite is etale away from
the full prime boundary.

Only formal etaleness and faithful flatness of the factor are used; module
finiteness is deliberately absent from the statement.
-/
theorem all_exponents_isUnit_of_iteratedRadical_formallyEtaleFactor
    {A : Type u} [CommRing A] [IsDomain A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (haPrime : ∀ i, Prime (a i))
    (hCharZero : ∀ i, CharZero (A ⧸ Ideal.span {a i})) :
    let B := iteratedRadical A r n a
    ∀ {D : Type u} [CommRing D] [Algebra B D]
      [Algebra A D] [IsScalarTower A B D]
      [Algebra.FormallyEtale B D] [Module.FaithfullyFlat B D],
      (Localization.awayMap (algebraMap A D)
        (∏ i ∈ (Finset.univ : Finset (Fin r)), a i)).Etale →
      ∀ i, IsUnit (n i : A) := by
  dsimp only
  intro D _ _ _ _ _ _ hAway
  classical
  let B := iteratedRadical A r n a
  let fA : A := ∏ i ∈ (Finset.univ : Finset (Fin r)), a i
  let MA : Submonoid A := Submonoid.powers fA
  let MB : Submonoid B := Algebra.algebraMapSubmonoid B MA
  let MD : Submonoid D := Algebra.algebraMapSubmonoid D MB
  let MDA : Submonoid D := Algebra.algebraMapSubmonoid D MA
  let S := Localization MA
  let T := Localization MB
  let U := Localization MD
  have hMD : MD = MDA := by
    simp [MD, MDA, MB]
  let : IsLocalization MDA U := by
    rw [← hMD]
    infer_instance
  let : Algebra S U := localizationAlgebra MA D
  let : IsScalarTower A S U :=
    isScalarTower_localizationAlgebra MA D
  let : IsLocalization.Away (algebraMap A D fA) U := by
    change IsLocalization (Submonoid.powers (algebraMap A D fA)) U
    simpa only [MDA, MA, Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization MDA U)
  have hSTU :
      (algebraMap T U).comp (algebraMap S T) = algebraMap S U := by
    change
      (IsLocalization.map U (algebraMap B D) _).comp
          (IsLocalization.map T (algebraMap A B) _) =
        IsLocalization.map U (algebraMap A D) _
    rw [IsLocalization.map_comp_map]
    congr 1
    exact (IsScalarTower.algebraMap_eq A B D).symm
  let : IsScalarTower S T U :=
    IsScalarTower.of_algebraMap_eq' hSTU.symm
  have hAwayU : (algebraMap S U).Etale := by
    change (IsLocalization.Away.map S U (algebraMap A D) fA).Etale
    exact
      ((RingHom.Etale.respectsIso.isLocalization_away_iff
        (R' := S) (S' := U) (algebraMap A D) fA).mp hAway)
  let : Algebra.Etale S U := hAwayU.toAlgebra
  let : IsLocalization (MB.map (algebraMap B D)) U := by
    change IsLocalization MD U
    infer_instance
  let : Algebra.FormallyEtale T U :=
    Algebra.FormallyEtale.localization_map
      (R := B) (S := D) (Rₘ := T) (Sₘ := U) MB
  let eTensor : T ⊗[B] D ≃ₐ[T] U :=
    Localization.tensorRightAlgEquiv MB D
  let : Module.FaithfullyFlat T U :=
    Module.FaithfullyFlat.of_linearEquiv
      (R := T) (M := T ⊗[B] D) eTensor.symm.toLinearEquiv
  let : Algebra.FormallyUnramified S T :=
    formallyUnramified_of_formallyEtale_faithfullyFlat
      (R := S) (S := T) (T := U)
  let rootS :=
    iteratedRadical S r n (fun i ↦ algebraMap A S (a i))
  let eBase : S ⊗[A] B ≃ₐ[S] rootS :=
    iteratedRadicalBaseChangeAlgEquiv n a
  let eTensorLoc : S ⊗[A] B ≃ₐ[S] T :=
    Localization.tensorRightAlgEquiv MA B
  let eRootT : rootS ≃ₐ[S] T := eBase.symm.trans eTensorLoc
  let : Algebra.FormallyUnramified S rootS :=
    Algebra.FormallyUnramified.of_equiv eRootT.symm
  have hfA : fA ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ (haPrime i).ne_zero
  let : IsDomain S := IsLocalization.Away.isDomain S hfA
  have hnS : ∀ i, IsUnit (n i : S) :=
    all_exponents_isUnit_of_formallyUnramified_iteratedRadical
      (A := S) n (fun i ↦ algebraMap A S (a i)) hn
  intro i
  exact isUnit_natCast_of_isUnit_algebraMap_away_finsetProduct
    (R := A) (S := S) Finset.univ a
    (fun j _ ↦ haPrime j) (fun j _ ↦ hCharZero j)
    (hn i) (by simpa using hnS i)

end EtaleFundamentalGroups.Kummer

end
