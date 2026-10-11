/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PowerSeries.Ideal
import EtaleFundamentalGroups.Kummer.Completions.MaximalAdic.FiniteGeneratorEvaluation

/-!
# Noetherian finite-variable power-series rings

Splitting a finite set of variables into one variable and the remaining
variables identifies the corresponding multivariate power-series ring with
an iterated univariate power-series ring.  This gives the finite-variable
Hilbert basis theorem for formal power series and, as an application, the
Noetherianity of maximal-adic completions of Noetherian local rings.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u v

open Finset
open IsLocalRing

namespace MvPowerSeriesFinite

variable {R : Type u} {σ : Type v}

/-- Split an exponent on `Unit ⊕ σ` into the exponent of the distinguished
variable and the exponent vector on the remaining variables. -/
private noncomputable def splitIndex :
    (Unit ⊕ σ →₀ ℕ) ≃ ℕ × (σ →₀ ℕ) :=
  Finsupp.sumFinsuppEquivProdFinsupp.trans
    (Equiv.prodCongr (Finsupp.uniqueEquiv ()) (Equiv.refl _))

@[simp]
private lemma splitIndex_symm_apply (n : ℕ) (d : σ →₀ ℕ) :
    (splitIndex (σ := σ)).symm (n, d) =
      (Finsupp.single () n).sumElim d := rfl

@[simp]
private lemma splitIndex_apply_sumElim (n : ℕ) (d : σ →₀ ℕ) :
    splitIndex ((Finsupp.single () n).sumElim d) = (n, d) := by
  rw [← splitIndex_symm_apply]
  exact Equiv.apply_symm_apply _ _

/-- Curry the coefficient function of a power series in `Unit ⊕ σ` into a
univariate power series whose coefficients are power series in `σ`. -/
private def curryFun [Semiring R] :
    MvPowerSeries (Unit ⊕ σ) R → PowerSeries (MvPowerSeries σ R) :=
  fun p ↦ PowerSeries.mk fun n ↦
    (fun d ↦ p ((splitIndex (σ := σ)).symm (n, d)) : MvPowerSeries σ R)

/-- Undo `curryFun` by joining the two exponent vectors. -/
private def uncurryFun [Semiring R] :
    PowerSeries (MvPowerSeries σ R) → MvPowerSeries (Unit ⊕ σ) R :=
  fun p d ↦
    PowerSeries.coeff ((splitIndex (σ := σ) d).1) p
      ((splitIndex (σ := σ) d).2)

@[simp]
private lemma coeff_coeff_curryFun [Semiring R]
    (p : MvPowerSeries (Unit ⊕ σ) R) (n : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (PowerSeries.coeff n (curryFun p)) =
      MvPowerSeries.coeff ((Finsupp.single () n).sumElim d) p := by
  rw [MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply]
  have hcoeff : PowerSeries.coeff n (curryFun p) =
      (fun e : σ →₀ ℕ ↦ p ((splitIndex (σ := σ)).symm (n, e)) :
        MvPowerSeries σ R) := by
    unfold curryFun
    exact PowerSeries.coeff_mk n _
  calc
    (PowerSeries.coeff n (curryFun p)) d =
        p ((splitIndex (σ := σ)).symm (n, d)) :=
      congrArg (fun q : MvPowerSeries σ R ↦ q d) hcoeff
    _ = p ((Finsupp.single () n).sumElim d) :=
      congrArg p (splitIndex_symm_apply n d)

@[simp]
private lemma coeff_uncurryFun [Semiring R]
    (p : PowerSeries (MvPowerSeries σ R)) (d : Unit ⊕ σ →₀ ℕ) :
    MvPowerSeries.coeff d (uncurryFun p) =
      MvPowerSeries.coeff ((splitIndex (σ := σ) d).2)
        (PowerSeries.coeff ((splitIndex (σ := σ) d).1) p) := by
  rw [MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply]
  rfl

private lemma curryFun_mul [CommSemiring R]
    (p q : MvPowerSeries (Unit ⊕ σ) R) :
    curryFun (p * q) = curryFun p * curryFun q := by
  classical
  have hsumElim : Function.Injective
      (fun x : (Unit →₀ ℕ) × (σ →₀ ℕ) ↦ x.1.sumElim x.2) := by
    intro a b h
    apply Prod.ext
    · apply Finsupp.ext
      intro i
      exact DFunLike.congr_fun h (Sum.inl i)
    · apply Finsupp.ext
      intro i
      exact DFunLike.congr_fun h (Sum.inr i)
  have hcombine : Function.Injective
      (fun x : ((Unit →₀ ℕ) × (Unit →₀ ℕ)) ×
          ((σ →₀ ℕ) × (σ →₀ ℕ)) ↦
        (x.1.1.sumElim x.2.1, x.1.2.sumElim x.2.2)) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ h
    have hac : (a, c) = (a', c') :=
      hsumElim (congr_arg Prod.fst h)
    have hbd : (b, d) = (b', d') :=
      hsumElim (congr_arg Prod.snd h)
    have ha : a = a' := congr_arg Prod.fst hac
    have hc : c = c' := congr_arg Prod.snd hac
    have hb : b = b' := congr_arg Prod.fst hbd
    have hd : d = d' := congr_arg Prod.snd hbd
    cases ha
    cases hb
    cases hc
    cases hd
    rfl
  apply PowerSeries.ext
  intro n
  apply MvPowerSeries.ext
  intro d
  rw [coeff_coeff_curryFun, PowerSeries.coeff_mul, map_sum]
  simp_rw [MvPowerSeries.coeff_mul]
  rw [← Finsupp.image_sumElim_product_antidiagonal]
  rw [Finset.sum_image hcombine.injOn]
  rw [Finset.sum_product]
  rw [Finsupp.antidiagonal_single, Finset.sum_map]
  simp_rw [coeff_coeff_curryFun]
  rfl

/-- A finite-variable multivariate power-series ring with one distinguished
variable is an iterated univariate power-series ring. -/
noncomputable def sumUnitEquivPowerSeries [CommSemiring R] :
    MvPowerSeries (Unit ⊕ σ) R ≃+* PowerSeries (MvPowerSeries σ R) where
  toFun := curryFun
  invFun := uncurryFun
  left_inv p := by
    apply MvPowerSeries.ext
    intro d
    rw [coeff_uncurryFun, coeff_coeff_curryFun]
    exact congr_arg (fun e ↦ MvPowerSeries.coeff e p)
      ((splitIndex (σ := σ)).symm_apply_apply d)
  right_inv p := by
    apply PowerSeries.ext
    intro n
    apply MvPowerSeries.ext
    intro d
    rw [coeff_coeff_curryFun, coeff_uncurryFun,
      splitIndex_apply_sumElim]
  map_mul' := curryFun_mul
  map_add' p q := by
    apply PowerSeries.ext
    intro n
    apply MvPowerSeries.ext
    intro d
    rw [coeff_coeff_curryFun, map_add, map_add, map_add,
      coeff_coeff_curryFun, coeff_coeff_curryFun]

end MvPowerSeriesFinite

/-- Formal power series in `n` variables over a Noetherian coefficient ring
form a Noetherian ring. -/
theorem isNoetherianRing_mvPowerSeries_fin
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
      exact isNoetherianRing_of_surjective R
        (MvPowerSeries (Fin 0) R) MvPowerSeries.C
        MvPowerSeries.C_surjective
  | succ n ih =>
      let : IsNoetherianRing (MvPowerSeries (Fin n) R) := ih
      let eIndex : Fin (n + 1) ≃ Unit ⊕ Fin n :=
        (finSuccEquiv n).trans
          ((Equiv.optionEquivSumPUnit.{0} (Fin n)).trans
            (Equiv.sumComm _ _))
      let e : MvPowerSeries (Fin (n + 1)) R ≃+*
          PowerSeries (MvPowerSeries (Fin n) R) :=
        (MvPowerSeries.renameEquiv R eIndex).toRingEquiv.trans
          MvPowerSeriesFinite.sumUnitEquivPowerSeries
      exact isNoetherianRing_of_ringEquiv
        (PowerSeries (MvPowerSeries (Fin n) R)) e.symm

/-- A multivariate formal-power-series ring over a Noetherian ring is
Noetherian whenever its variable type is finite. -/
theorem isNoetherianRing_mvPowerSeries_finite
    {R : Type u} {σ : Type v} [CommRing R] [IsNoetherianRing R] [Finite σ] :
    IsNoetherianRing (MvPowerSeries σ R) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let : IsNoetherianRing (MvPowerSeries (Fin n) R) :=
    isNoetherianRing_mvPowerSeries_fin R n
  exact isNoetherianRing_of_ringEquiv
    (MvPowerSeries (Fin n) R)
    (MvPowerSeries.renameEquiv R e.symm).toRingEquiv

/-- Typeclass form of the finite-variable formal-power-series Hilbert basis
theorem. -/
instance mvPowerSeries_isNoetherianRing_of_finite
    {R : Type u} {σ : Type v} [CommRing R] [IsNoetherianRing R] [Finite σ] :
    IsNoetherianRing (MvPowerSeries σ R) :=
  isNoetherianRing_mvPowerSeries_finite

/-- A finite family generating the closed point presents the maximal-adic
completion as a quotient of a Noetherian finite-variable power-series ring. -/
theorem maximalAdicCompletion_isNoetherianRing_of_generators
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {ι : Type v} [Finite ι] (t : ι → B)
    (hgen : Ideal.span (Set.range t) = maximalIdeal B) :
    IsNoetherianRing (AdicCompletion (maximalIdeal B) B) := by
  rcases mvPowerSeries_surjective_maximalAdicCompletion_of_generators
      t hgen with ⟨f, hf⟩
  exact isNoetherianRing_of_surjective
    (MvPowerSeries ι B) (AdicCompletion (maximalIdeal B) B) f hf

/-- The maximal-adic completion of every Noetherian local ring is
Noetherian.  A finite generating family is obtained from Noetherianity, so
no regular-system hypothesis or bound on the dimension is required. -/
theorem maximalAdicCompletion_isNoetherianRing
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] :
    IsNoetherianRing (AdicCompletion (maximalIdeal B) B) := by
  let ι := (maximalIdeal B).generators
  let : Finite ι :=
    Set.finite_coe_iff.mpr
      (Submodule.FG.finite_generators
        ((maximalIdeal B).fg_of_isNoetherianRing :
          (maximalIdeal B : Submodule B B).FG))
  let t : ι → B := fun i ↦ i.1
  have hgen : Ideal.span (Set.range t) = maximalIdeal B := by
    calc
      Ideal.span (Set.range t) =
          Ideal.span ((maximalIdeal B).generators) := by
        congr 1
        ext x
        simp [t, ι]
      _ = maximalIdeal B := (maximalIdeal B).span_generators
  exact maximalAdicCompletion_isNoetherianRing_of_generators t hgen

/-- Typeclass form of Noetherianity of maximal-adic completion. -/
instance maximalAdicCompletion_isNoetherianRing_instance
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] :
    IsNoetherianRing (AdicCompletion (maximalIdeal B) B) :=
  maximalAdicCompletion_isNoetherianRing

end EtaleFundamentalGroups.Kummer

end
