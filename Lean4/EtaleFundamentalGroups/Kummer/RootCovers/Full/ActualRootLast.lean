/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedHeightOne
import EtaleFundamentalGroups.Kummer.RootCovers.SelectedDivisor.ConditionalRootCover
import EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.ConditionalRootCover.Core
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Algebra.Hom

/-!
# Putting the actual boundary root last in the full local root cover

At a height-two normal-crossings point, all conditional radical stages except
the actual second boundary branch have degree one.  This file first removes
those degree-one stages without changing the distinguished actual root.  It
then commutes that root adjunction past the selected-branch root adjunction.
The result presents the same full cover with the actual boundary root as the
last one-root extension.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct

universe u

private theorem exists_adjoinRootOneAlgEquiv_preserving
    {R T U : Type u} [CommRing R] [CommRing T] [CommRing U]
    [Algebra R T] [Algebra R U]
    (f : T[X]) (c : T) (hf : f = X ^ 1 - C c)
    (g : T ≃ₐ[R] U) (z : T) (w : U) (hz : g z = w) :
    ∃ e : AdjoinRoot f ≃ₐ[R] U, e (AdjoinRoot.of f z) = w := by
  let eT : AdjoinRoot f ≃ₐ[T] T :=
    (AdjoinRoot.algEquivOfEq T f (X ^ 1 - C c) hf).trans
      (adjoinRootOneAlgEquiv c)
  refine ⟨(eT.restrictScalars R).trans g, ?_⟩
  change g (eT (AdjoinRoot.of f z)) = w
  exact (congrArg g (eT.commutes z)).trans hz

private theorem exists_iteratedRadicalSingleRoot_oneLastStep
    {R : Type u} [CommRing R] {s : ℕ}
    (n : Fin (s + 2) → ℕ) (a : Fin (s + 2) → R)
    (k : Fin (s + 1)) (hlast : n (Fin.last (s + 1)) = 1)
    (hInit : ∃ e : iteratedRadical R (s + 1) (Fin.init n) (Fin.init a) ≃ₐ[R]
        AdjoinRoot (X ^ n k.castSucc - C (a k.castSucc)),
      e (iteratedRadicalRoot R (Fin.init n) (Fin.init a) k) =
        AdjoinRoot.root (X ^ n k.castSucc - C (a k.castSucc))) :
    ∃ e : iteratedRadical R (s + 2) n a ≃ₐ[R]
        AdjoinRoot (X ^ n k.castSucc - C (a k.castSucc)),
      e (iteratedRadicalRoot R n a k.castSucc) =
        AdjoinRoot.root (X ^ n k.castSucc - C (a k.castSucc)) := by
  let T : CommAlgCat R :=
    iteratedRadical R (s + 1) (Fin.init n) (Fin.init a)
  let f : T[X] := X ^ n (Fin.last (s + 1)) -
    C (algebraMap R T (a (Fin.last (s + 1))))
  let g : R[X] := X ^ n k.castSucc - C (a k.castSucc)
  obtain ⟨eInit, heInit⟩ := hInit
  have hf : f = X ^ 1 - C (algebraMap R T (a (Fin.last (s + 1)))) := by
    simp only [f, hlast]
  rw [iteratedRadicalRoot_castSucc]
  change ∃ e : AdjoinRoot f ≃ₐ[R] AdjoinRoot g,
    e (AdjoinRoot.of f
      (iteratedRadicalRoot R (Fin.init n) (Fin.init a) k)) = AdjoinRoot.root g
  exact exists_adjoinRootOneAlgEquiv_preserving f
    (algebraMap R T (a (Fin.last (s + 1)))) hf eInit
    (iteratedRadicalRoot R (Fin.init n) (Fin.init a) k)
    (AdjoinRoot.root g) heInit

private theorem exists_iteratedRadicalSingleRootAlgEquiv
    {R : Type u} [CommRing R] :
    {s : ℕ} → (n : Fin (s + 1) → ℕ) → (a : Fin (s + 1) → R) →
      (k : Fin (s + 1)) → (hother : ∀ l, l ≠ k → n l = 1) →
      ∃ e : iteratedRadical R (s + 1) n a ≃ₐ[R]
          AdjoinRoot (X ^ n k - C (a k)),
        e (iteratedRadicalRoot R n a k) =
          AdjoinRoot.root (X ^ n k - C (a k))
  | 0, n, a, k, _ => by
      have hk : k = Fin.last 0 := by
        simpa using Fin.eq_zero k
      subst k
      let T : CommAlgCat R :=
        iteratedRadical R 0 (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last 0) - C (algebraMap R T (a (Fin.last 0)))
      let g : R[X] := X ^ n (Fin.last 0) - C (a (Fin.last 0))
      let ePrefix : T ≃ₐ[R] R :=
        iteratedRadicalAllOneAlgEquiv
          (Fin.init n) (Fin.init a) (fun l ↦ Fin.elim0 l)
      have hfg : f.map ePrefix.toRingHom = g := by
        ext m
        simp [f, g, ePrefix]
      let e : AdjoinRoot f ≃ₐ[R] AdjoinRoot g :=
        AdjoinRoot.mapAlgEquiv ePrefix f g (Associated.of_eq hfg)
      simp only [iteratedRadicalRoot_last]
      change ∃ e : AdjoinRoot f ≃ₐ[R] AdjoinRoot g,
        e (AdjoinRoot.root f) = AdjoinRoot.root g
      refine ⟨e, ?_⟩
      simp [e]
  | s + 1, n, a, k, hother => by
      let nInit : Fin (s + 1) → ℕ := Fin.init n
      let aInit : Fin (s + 1) → R := Fin.init a
      let T : CommAlgCat R := iteratedRadical R (s + 1) nInit aInit
      let f : T[X] :=
        X ^ n (Fin.last (s + 1)) -
          C (algebraMap R T (a (Fin.last (s + 1))))
      revert hother
      refine Fin.lastCases ?_ (fun kInit ↦ ?_) k
      · intro hother
        have hprefix : ∀ l : Fin (s + 1), nInit l = 1 := by
          intro l
          exact hother l.castSucc (Fin.castSucc_ne_last l)
        let ePrefix : T ≃ₐ[R] R :=
          iteratedRadicalAllOneAlgEquiv nInit aInit hprefix
        let g : R[X] :=
          X ^ n (Fin.last (s + 1)) - C (a (Fin.last (s + 1)))
        have hfg : f.map ePrefix.toRingHom = g := by
          ext m
          simp [f, g, ePrefix]
        let e : AdjoinRoot f ≃ₐ[R] AdjoinRoot g :=
          AdjoinRoot.mapAlgEquiv ePrefix f g (Associated.of_eq hfg)
        simp only [iteratedRadicalRoot_last]
        change ∃ e : AdjoinRoot f ≃ₐ[R] AdjoinRoot g,
          e (AdjoinRoot.root f) = AdjoinRoot.root g
        refine ⟨e, ?_⟩
        simp [e]
      · intro hother
        have hlast : n (Fin.last (s + 1)) = 1 := by
          exact hother _ (Fin.castSucc_ne_last kInit).symm
        have hotherInit : ∀ l, l ≠ kInit → nInit l = 1 := by
          intro l hl
          exact hother l.castSucc (by
            intro h
            exact hl (Fin.castSucc_injective _ h))
        exact exists_iteratedRadicalSingleRoot_oneLastStep n a kInit hlast
          (exists_iteratedRadicalSingleRootAlgEquiv nInit aInit kInit hotherInit)

/-- An iterated diagonal radical with only one possibly nontrivial exponent is
canonically the corresponding one-root algebra. -/
def iteratedRadicalSingleRootAlgEquiv
    {R : Type u} [CommRing R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1) :
    iteratedRadical R (s + 1) n a ≃ₐ[R]
      AdjoinRoot (X ^ n k - C (a k)) :=
  Classical.choose
    (exists_iteratedRadicalSingleRootAlgEquiv n a k hother)

/-- The single-root equivalence preserves the distinguished actual root. -/
@[simp]
theorem iteratedRadicalSingleRootAlgEquiv_apply_root
    {R : Type u} [CommRing R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1) :
    iteratedRadicalSingleRootAlgEquiv n a k hother
        (iteratedRadicalRoot R n a k) =
      AdjoinRoot.root (X ^ n k - C (a k)) :=
  Classical.choose_spec
    (exists_iteratedRadicalSingleRootAlgEquiv n a k hother)

private theorem exists_twoRootSwapAlgEquiv
    {R : Type u} [CommRing R] (m n : ℕ) (x y : R) :
    let px : R[X] := X ^ m - C x
    let py : R[X] := X ^ n - C y
    let Xroot := AdjoinRoot px
    let Yroot := AdjoinRoot py
    let fy : Xroot[X] := X ^ n - C (algebraMap R Xroot y)
    let gx : Yroot[X] := X ^ m - C (algebraMap R Yroot x)
    ∃ e : AdjoinRoot fy ≃ₐ[R] AdjoinRoot gx,
      e (algebraMap Xroot (AdjoinRoot fy) (AdjoinRoot.root px)) =
          AdjoinRoot.root gx ∧
        e (AdjoinRoot.root fy) =
          algebraMap Yroot (AdjoinRoot gx) (AdjoinRoot.root py) := by
  dsimp only
  let px : R[X] := X ^ m - C x
  let py : R[X] := X ^ n - C y
  let Xroot := AdjoinRoot px
  let Yroot := AdjoinRoot py
  let fy : Xroot[X] := X ^ n - C (algebraMap R Xroot y)
  let gx : Yroot[X] := X ^ m - C (algebraMap R Yroot x)
  let Dxy := AdjoinRoot fy
  let Dyx := AdjoinRoot gx
  have hxRoot : px.eval₂ (Algebra.ofId R Dyx) (AdjoinRoot.root gx) = 0 := by
    dsimp only [px]
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [adjoinRoot_root_pow]
    change algebraMap Yroot Dyx (algebraMap R Yroot x) -
      algebraMap R Dyx x = 0
    rw [← IsScalarTower.algebraMap_apply R Yroot Dyx x]
    exact sub_self _
  let mapX : Xroot →ₐ[R] Dyx :=
    AdjoinRoot.liftAlgHom px (Algebra.ofId R Dyx)
      (AdjoinRoot.root gx) hxRoot
  have hyRoot : fy.eval₂ mapX
      (algebraMap Yroot Dyx (AdjoinRoot.root py)) = 0 := by
    dsimp only [fy]
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    change (algebraMap Yroot Dyx (AdjoinRoot.root py)) ^ n -
      mapX (algebraMap R Xroot y) = 0
    rw [mapX.commutes]
    rw [← map_pow, adjoinRoot_root_pow]
    change algebraMap Yroot Dyx (algebraMap R Yroot y) -
      algebraMap R Dyx y = 0
    rw [← IsScalarTower.algebraMap_apply R Yroot Dyx y]
    exact sub_self _
  let forward : Dxy →ₐ[R] Dyx :=
    AdjoinRoot.liftAlgHom fy mapX
      (algebraMap Yroot Dyx (AdjoinRoot.root py)) hyRoot
  have hyRoot' : py.eval₂ (Algebra.ofId R Dxy) (AdjoinRoot.root fy) = 0 := by
    dsimp only [py]
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [adjoinRoot_root_pow]
    change algebraMap Xroot Dxy (algebraMap R Xroot y) -
      algebraMap R Dxy y = 0
    rw [← IsScalarTower.algebraMap_apply R Xroot Dxy y]
    exact sub_self _
  let mapY : Yroot →ₐ[R] Dxy :=
    AdjoinRoot.liftAlgHom py (Algebra.ofId R Dxy)
      (AdjoinRoot.root fy) hyRoot'
  have hxRoot' : gx.eval₂ mapY
      (algebraMap Xroot Dxy (AdjoinRoot.root px)) = 0 := by
    dsimp only [gx]
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    change (algebraMap Xroot Dxy (AdjoinRoot.root px)) ^ m -
      mapY (algebraMap R Yroot x) = 0
    rw [mapY.commutes]
    rw [← map_pow, adjoinRoot_root_pow]
    change algebraMap Xroot Dxy (algebraMap R Xroot x) -
      algebraMap R Dxy x = 0
    rw [← IsScalarTower.algebraMap_apply R Xroot Dxy x]
    exact sub_self _
  let backward : Dyx →ₐ[R] Dxy :=
    AdjoinRoot.liftAlgHom gx mapY
      (algebraMap Xroot Dxy (AdjoinRoot.root px)) hxRoot'
  have hmapXRoot : mapX (AdjoinRoot.root px) = AdjoinRoot.root gx := by
    exact AdjoinRoot.liftAlgHom_root px (Algebra.ofId R Dyx)
      (AdjoinRoot.root gx) hxRoot
  have hmapYRoot : mapY (AdjoinRoot.root py) = AdjoinRoot.root fy := by
    exact AdjoinRoot.liftAlgHom_root py (Algebra.ofId R Dxy)
      (AdjoinRoot.root fy) hyRoot'
  have hforwardOf (z : Xroot) :
      forward (algebraMap Xroot Dxy z) = mapX z := by
    change forward (AdjoinRoot.of fy z) = mapX z
    exact AdjoinRoot.liftAlgHom_of fy mapX
      (algebraMap Yroot Dyx (AdjoinRoot.root py)) hyRoot z
  have hforwardRoot : forward (AdjoinRoot.root fy) =
      algebraMap Yroot Dyx (AdjoinRoot.root py) := by
    exact AdjoinRoot.liftAlgHom_root fy mapX
      (algebraMap Yroot Dyx (AdjoinRoot.root py)) hyRoot
  have hbackwardOf (z : Yroot) :
      backward (algebraMap Yroot Dyx z) = mapY z := by
    change backward (AdjoinRoot.of gx z) = mapY z
    exact AdjoinRoot.liftAlgHom_of gx mapY
      (algebraMap Xroot Dxy (AdjoinRoot.root px)) hxRoot' z
  have hbackwardRoot : backward (AdjoinRoot.root gx) =
      algebraMap Xroot Dxy (AdjoinRoot.root px) := by
    exact AdjoinRoot.liftAlgHom_root gx mapY
      (algebraMap Xroot Dxy (AdjoinRoot.root px)) hxRoot'
  let e : Dxy ≃ₐ[R] Dyx :=
    AlgEquiv.ofAlgHom forward backward
      (by
        apply AdjoinRoot.algHom_ext'
        · apply AdjoinRoot.algHom_ext
          change forward
              (backward (algebraMap Yroot Dyx (AdjoinRoot.root py))) =
            algebraMap Yroot Dyx (AdjoinRoot.root py)
          rw [hbackwardOf, hmapYRoot, hforwardRoot]
        · change forward (backward (AdjoinRoot.root gx)) =
            AdjoinRoot.root gx
          rw [hbackwardRoot, hforwardOf, hmapXRoot])
      (by
        apply AdjoinRoot.algHom_ext'
        · apply AdjoinRoot.algHom_ext
          change backward
              (forward (algebraMap Xroot Dxy (AdjoinRoot.root px))) =
            algebraMap Xroot Dxy (AdjoinRoot.root px)
          rw [hforwardOf, hmapXRoot, hbackwardRoot]
        · change backward (forward (AdjoinRoot.root fy)) =
            AdjoinRoot.root fy
          rw [hforwardRoot, hbackwardOf, hmapYRoot])
  refine ⟨e, ?_, ?_⟩
  · change forward
        (algebraMap Xroot Dxy (AdjoinRoot.root px)) =
      AdjoinRoot.root gx
    rw [hforwardOf, hmapXRoot]
  · change forward (AdjoinRoot.root fy) =
      algebraMap Yroot Dyx (AdjoinRoot.root py)
    exact hforwardRoot

/-- Two independent Kummer root adjunctions commute.  The equivalence is
oriented so that the first root in the source becomes the last root in the
target. -/
def twoRootSwapAlgEquiv
    {R : Type u} [CommRing R] (m n : ℕ) (x y : R) :
    let px : R[X] := X ^ m - C x
    let py : R[X] := X ^ n - C y
    let Xroot := AdjoinRoot px
    let Yroot := AdjoinRoot py
    let fy : Xroot[X] := X ^ n - C (algebraMap R Xroot y)
    let gx : Yroot[X] := X ^ m - C (algebraMap R Yroot x)
    AdjoinRoot fy ≃ₐ[R] AdjoinRoot gx :=
  Classical.choose (exists_twoRootSwapAlgEquiv m n x y)

/-- Under the swap equivalence, the first root becomes the final adjoined
root. -/
@[simp]
theorem twoRootSwapAlgEquiv_algebraMap_root
    {R : Type u} [CommRing R] (m n : ℕ) (x y : R) :
    let px : R[X] := X ^ m - C x
    let py : R[X] := X ^ n - C y
    let Xroot := AdjoinRoot px
    let Yroot := AdjoinRoot py
    let fy : Xroot[X] := X ^ n - C (algebraMap R Xroot y)
    let gx : Yroot[X] := X ^ m - C (algebraMap R Yroot x)
    twoRootSwapAlgEquiv m n x y
        (algebraMap Xroot (AdjoinRoot fy) (AdjoinRoot.root px)) =
      AdjoinRoot.root gx := by
  exact (Classical.choose_spec
    (exists_twoRootSwapAlgEquiv m n x y)).1

/-- Under the swap equivalence, the second root becomes the root already in
the new coefficient algebra. -/
@[simp]
theorem twoRootSwapAlgEquiv_root
    {R : Type u} [CommRing R] (m n : ℕ) (x y : R) :
    let px : R[X] := X ^ m - C x
    let py : R[X] := X ^ n - C y
    let Xroot := AdjoinRoot px
    let Yroot := AdjoinRoot py
    let fy : Xroot[X] := X ^ n - C (algebraMap R Xroot y)
    let gx : Yroot[X] := X ^ m - C (algebraMap R Yroot x)
    twoRootSwapAlgEquiv m n x y (AdjoinRoot.root fy) =
      algebraMap Yroot (AdjoinRoot gx) (AdjoinRoot.root py) := by
  exact (Classical.choose_spec
    (exists_twoRootSwapAlgEquiv m n x y)).2

/-- Once an actual non-selected branch through a height-two point is fixed,
every other conditional radical stage has exponent one.  This supplies the
single-root hypothesis directly from the strict-normal-crossings chart. -/
theorem heightTwoConditionalOtherExponent_eq_one_of_ne_actual
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsRegularRing A]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1))
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P)
    (e : Fin d → ℕ) (σ : Equiv.Perm (Fin d))
    (k : Fin d)
    (hkActive : (i.succAbove (σ k)).1 < r)
    (htkP : t (i.succAbove (σ k)) ∈ P) :
    ∀ l, l ≠ k →
      heightTwoConditionalOtherExponent t i r P e σ l = 1 := by
  classical
  intro l hl
  change
    (if (i.succAbove (σ l)).1 < r ∧
        t (i.succAbove (σ l)) ∈ P then e (σ l) else 1) = 1
  rw [ite_eq_right]
  intro hlActual
  rcases splitStrictNormalCrossings_heightTwo_branchSupport
      hNC i P hP htiP with hsolo | htwo
  · have hkEq : i.succAbove (σ k) = i :=
      hsolo _ hkActive htkP
    exact Fin.succAbove_ne i (σ k) hkEq
  · obtain ⟨j, _hjActive, _hji, _htjP, hsupport⟩ := htwo
    have hkEq : i.succAbove (σ k) = j := by
      rcases hsupport _ hkActive htkP with hkEqI | hkEqJ
      · exact (Fin.succAbove_ne i (σ k) hkEqI).elim
      · exact hkEqJ
    have hlEq : i.succAbove (σ l) = j := by
      rcases hsupport _ hlActual.1 hlActual.2 with hlEqI | hlEqJ
      · exact (Fin.succAbove_ne i (σ l) hlEqI).elim
      · exact hlEqJ
    apply hl
    apply σ.injective
    apply Fin.succAbove_right_injective
    exact hlEq.trans hkEq.symm

private theorem exists_fullRootCoverActualRootLastAlgEquiv
    {R : Type u} [CommRing R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1)
    (N : ℕ) (y : R) :
    let B := iteratedRadical R (s + 1) n a
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let py : R[X] := X ^ N - C y
    let Yroot := AdjoinRoot py
    let G : Yroot[X] :=
      X ^ n k - C (algebraMap R Yroot (a k))
    ∃ e : AdjoinRoot F ≃ₐ[R] AdjoinRoot G,
      e (algebraMap B (AdjoinRoot F)
            (iteratedRadicalRoot R n a k)) =
          AdjoinRoot.root G ∧
        e (AdjoinRoot.root F) =
          algebraMap Yroot (AdjoinRoot G) (AdjoinRoot.root py) := by
  dsimp only
  let B := iteratedRadical R (s + 1) n a
  let px : R[X] := X ^ n k - C (a k)
  let Xroot := AdjoinRoot px
  let eB : B ≃ₐ[R] Xroot :=
    iteratedRadicalSingleRootAlgEquiv n a k hother
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let F' : Xroot[X] := X ^ N - C (algebraMap R Xroot y)
  let py : R[X] := X ^ N - C y
  let Yroot := AdjoinRoot py
  let G : Yroot[X] := X ^ n k - C (algebraMap R Yroot (a k))
  have hF : F.map eB.toRingHom = F' := by
    dsimp only [F, F']
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    exact congrArg (fun z : Xroot ↦ (X : Xroot[X]) ^ N - C z) (eB.commutes y)
  let eFull : AdjoinRoot F ≃ₐ[R] AdjoinRoot F' :=
    AdjoinRoot.mapAlgEquiv eB F F' (Associated.of_eq hF)
  let eSwap : AdjoinRoot F' ≃ₐ[R] AdjoinRoot G :=
    twoRootSwapAlgEquiv (n k) N (a k) y
  have heFullOf (z : B) :
      eFull (algebraMap B (AdjoinRoot F) z) =
        algebraMap Xroot (AdjoinRoot F') (eB z) := by
    change eFull (AdjoinRoot.of F z) = AdjoinRoot.of F' (eB z)
    simp [eFull]
  have heFullRoot : eFull (AdjoinRoot.root F) =
      AdjoinRoot.root F' := by
    simp [eFull]
  refine ⟨eFull.trans eSwap, ?_, ?_⟩
  · change eSwap
        (eFull (algebraMap B (AdjoinRoot F)
          (iteratedRadicalRoot R n a k))) = AdjoinRoot.root G
    rw [heFullOf, iteratedRadicalSingleRootAlgEquiv_apply_root]
    exact twoRootSwapAlgEquiv_algebraMap_root (n k) N (a k) y
  · change eSwap (eFull (AdjoinRoot.root F)) =
      algebraMap Yroot (AdjoinRoot G) (AdjoinRoot.root py)
    rw [heFullRoot]
    exact twoRootSwapAlgEquiv_root (n k) N (a k) y

/-- The full selected-root cover, with all other conditional stages of degree
one, presented canonically with the specified actual root as its final
one-root extension. -/
def fullRootCoverActualRootLastAlgEquiv
    {R : Type u} [CommRing R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1)
    (N : ℕ) (y : R) :
    let B := iteratedRadical R (s + 1) n a
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let py : R[X] := X ^ N - C y
    let Yroot := AdjoinRoot py
    let G : Yroot[X] := X ^ n k - C (algebraMap R Yroot (a k))
    AdjoinRoot F ≃ₐ[R] AdjoinRoot G :=
  Classical.choose
    (exists_fullRootCoverActualRootLastAlgEquiv
      n a k hother N y)

/-- The distinguished conditional root is exactly the final root in the
reordered full cover. -/
@[simp]
theorem fullRootCoverActualRootLastAlgEquiv_algebraMap_root
    {R : Type u} [CommRing R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1)
    (N : ℕ) (y : R) :
    let B := iteratedRadical R (s + 1) n a
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let py : R[X] := X ^ N - C y
    let Yroot := AdjoinRoot py
    let G : Yroot[X] := X ^ n k - C (algebraMap R Yroot (a k))
    fullRootCoverActualRootLastAlgEquiv n a k hother N y
        (algebraMap B (AdjoinRoot F)
          (iteratedRadicalRoot R n a k)) =
      AdjoinRoot.root G :=
  (Classical.choose_spec
    (exists_fullRootCoverActualRootLastAlgEquiv
      n a k hother N y)).1

/-- The selected-branch root becomes the root in the coefficient algebra of
the reordered full cover. -/
@[simp]
theorem fullRootCoverActualRootLastAlgEquiv_root
    {R : Type u} [CommRing R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1)
    (N : ℕ) (y : R) :
    let B := iteratedRadical R (s + 1) n a
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let py : R[X] := X ^ N - C y
    let Yroot := AdjoinRoot py
    let G : Yroot[X] := X ^ n k - C (algebraMap R Yroot (a k))
    fullRootCoverActualRootLastAlgEquiv n a k hother N y
        (AdjoinRoot.root F) =
      algebraMap Yroot (AdjoinRoot G) (AdjoinRoot.root py) :=
  (Classical.choose_spec
    (exists_fullRootCoverActualRootLastAlgEquiv
      n a k hother N y)).2

end EtaleFundamentalGroups.Kummer

end
