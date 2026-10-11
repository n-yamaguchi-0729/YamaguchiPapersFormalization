/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.IteratedRadical.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Height-one primes of an iterated local root cover

This file exposes the individual roots in a finite diagonal Kummer cover and
uses their defining equations to classify the contractions of height-one
primes meeting the boundary.  It also extracts the corresponding divisibility
of ramification indices directly from the length definition of
`Ideal.ramificationIdx`.

No primality or uniformizer hypothesis is imposed on an adjoined root.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped BigOperators

universe u

/-- The `i`-th root in the final iterated radical, transported through all
subsequent root adjunctions. -/
def iteratedRadicalRoot
    (A : Type u) [CommRing A] :
    {r : ℕ} → (n : Fin r → ℕ) → (a : Fin r → A) →
      Fin r → iteratedRadical A r n a
  | 0, _, _, i => Fin.elim0 i
  | r + 1, n, a, i =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      Fin.lastCases
        (AdjoinRoot.root f)
        (fun j ↦ AdjoinRoot.of f
          (iteratedRadicalRoot A (Fin.init n) (Fin.init a) j)) i

/-- The last distinguished root is the root of the final adjunction. -/
theorem iteratedRadicalRoot_last {A : Type u} [CommRing A] {r : ℕ}
    (n : Fin (r + 1) → ℕ) (a : Fin (r + 1) → A) :
    iteratedRadicalRoot A n a (Fin.last r) =
      AdjoinRoot.root (X ^ n (Fin.last r) -
        C (algebraMap A (iteratedRadical A r (Fin.init n) (Fin.init a)) (a (Fin.last r)))) := by
  let T : CommAlgCat.{u} A := iteratedRadical A r (Fin.init n) (Fin.init a)
  let p : T[X] := X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
  change Fin.lastCases (motive := fun _ : Fin (r + 1) => AdjoinRoot p)
    (AdjoinRoot.root p)
    (fun k => AdjoinRoot.of p (iteratedRadicalRoot A (Fin.init n) (Fin.init a) k))
    (Fin.last r) = AdjoinRoot.root p
  exact Fin.lastCases_last
/-- Earlier distinguished roots enter the final adjunction through its canonical map. -/
theorem iteratedRadicalRoot_castSucc {A : Type u} [CommRing A] {r : ℕ}
    (n : Fin (r + 1) → ℕ) (a : Fin (r + 1) → A) (j : Fin r) :
    iteratedRadicalRoot A n a j.castSucc =
      AdjoinRoot.of (X ^ n (Fin.last r) -
        C (algebraMap A (iteratedRadical A r (Fin.init n) (Fin.init a)) (a (Fin.last r))))
        (iteratedRadicalRoot A (Fin.init n) (Fin.init a) j) := by
  let T : CommAlgCat.{u} A := iteratedRadical A r (Fin.init n) (Fin.init a)
  let p : T[X] := X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
  change Fin.lastCases (motive := fun _ : Fin (r + 1) => AdjoinRoot p)
    (AdjoinRoot.root p)
    (fun k => AdjoinRoot.of p (iteratedRadicalRoot A (Fin.init n) (Fin.init a) k))
    (j.castSucc) = AdjoinRoot.of p (iteratedRadicalRoot A (Fin.init n) (Fin.init a) j)
  exact Fin.lastCases_castSucc j

/-- Each indexed root satisfies its original diagonal Kummer equation in the
final iterated radical. -/
theorem iteratedRadicalRoot_pow
    {A : Type u} [CommRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (i : Fin r) :
    iteratedRadicalRoot A n a i ^ n i =
      algebraMap A (iteratedRadical A r n a) (a i) := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rw [iteratedRadicalRoot_last]
        change AdjoinRoot.root f ^ n (Fin.last r) =
          algebraMap A (AdjoinRoot f) (a (Fin.last r))
        rw [show f = X ^ n (Fin.last r) -
            C (algebraMap A T (a (Fin.last r))) by rfl,
          adjoinRoot_root_pow]
        rfl
      · rw [iteratedRadicalRoot_castSucc]
        change AdjoinRoot.of f
            (iteratedRadicalRoot A (Fin.init n) (Fin.init a) j) ^
              n j.castSucc =
          algebraMap A (AdjoinRoot f) (a j.castSucc)
        rw [show n j.castSucc = Fin.init n j by rfl]
        rw [← map_pow, ih (Fin.init n) (Fin.init a) j]
        rfl

/-- The product of the base radicands becomes the product of the corresponding
root powers in the final iterated cover. -/
theorem algebraMap_prod_radicands_eq_prod_iteratedRadicalRoot_pow
    {A : Type u} [CommRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) :
    algebraMap A (iteratedRadical A r n a) (∏ i, a i) =
      ∏ i, iteratedRadicalRoot A n a i ^ n i := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ ↦
    (iteratedRadicalRoot_pow n a i).symm

/-- A prime avoiding every adjoined root is disjoint from the powers of the
full boundary product.  Thus it defines a prime on the boundary-complement
Away localization. -/
theorem disjoint_powers_prod_radicands_of_iteratedRadicalRoots_not_mem
    {A : Type u} [CommRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (q : Ideal (iteratedRadical A r n a)) [q.IsPrime]
    (havoid : ∀ i, iteratedRadicalRoot A n a i ∉ q) :
    Disjoint
      ((Submonoid.powers
        (algebraMap A (iteratedRadical A r n a) (∏ i, a i)) :
          Submonoid (iteratedRadical A r n a)) :
        Set (iteratedRadical A r n a))
      (q : Set (iteratedRadical A r n a)) := by
  rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  rw [algebraMap_prod_radicands_eq_prod_iteratedRadicalRoot_pow]
  rw [Ideal.IsPrime.prod_mem_iff]
  simp only [Finset.mem_univ, true_and, not_exists]
  intro i hpow
  exact havoid i ((inferInstance : q.IsPrime).mem_of_pow_mem (n i) hpow)

/-- The explicit prime on the Away localization supplied by a height-one
prime which misses every root. -/
theorem map_to_away_prod_radicands_isPrime_of_iteratedRadicalRoots_not_mem
    {A : Type u} [CommRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (q : Ideal (iteratedRadical A r n a)) [q.IsPrime]
    (havoid : ∀ i, iteratedRadicalRoot A n a i ∉ q) :
    (q.map (algebraMap (iteratedRadical A r n a)
      (Localization.Away
        (algebraMap A (iteratedRadical A r n a) (∏ i, a i))))).IsPrime := by
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers
      (algebraMap A (iteratedRadical A r n a) (∏ i, a i)))
    (Localization.Away
      (algebraMap A (iteratedRadical A r n a) (∏ i, a i)))
    q inferInstance
    (disjoint_powers_prod_radicands_of_iteratedRadicalRoots_not_mem
      n a q havoid)

/-- A height-one prime meeting the `i`-th root contracts to the corresponding
prime boundary branch in the base.  The contraction equality is produced
from faithful flatness and going down; it is not an input hypothesis. -/
theorem under_eq_span_radicand_of_height_eq_one_of_iteratedRadicalRoot_mem
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (q : Ideal (iteratedRadical A r n a)) [q.IsPrime]
    (hqheight : q.height = 1) (i : Fin r)
    (hai : Prime (a i))
    (hroot : iteratedRadicalRoot A n a i ∈ q) :
    q.under A = Ideal.span {a i} := by
  let B := iteratedRadical A r n a
  let p : Ideal A := q.under A
  let branch : Ideal A := Ideal.span {a i}
  let : Module.Finite A B := finite_iteratedRadical n a hn
  let : Module.FaithfullyFlat A B := faithfullyFlat_iteratedRadical n a hn
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let : branch.IsPrime := Ideal.isPrime_span_singleton_of_prime hai
  have hradicand_q : algebraMap A B (a i) ∈ q := by
    rw [← iteratedRadicalRoot_pow n a i]
    exact Ideal.pow_mem_of_mem q hroot (n i) (hn i)
  have hbranch_le : branch ≤ p := by
    rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact hradicand_q
  have hbranch_height : branch.height = 1 := by
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hai.ne_zero)
      hai.not_isUnit
  have hp_height_le : p.height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q]
    exact le_add_right (le_refl p.height)
  have hp_height_le_branch : p.height ≤ branch.height := by
    rw [hbranch_height, ← hqheight]
    exact hp_height_le
  exact (branch.eq_of_le_of_height_le hbranch_le hp_height_le_branch).symm

/-- If a height-one prime of an iterated local root cover contains the `i`-th
root, then the exponent `n i` divides its ramification index over the original
base.  Flatness makes the base radicand regular on the cover, hence its root is
regular as well.  Additivity of order of vanishing then computes the quotient
length of the root power.  In particular, the root is not assumed prime or a
uniformizer. -/
theorem exponent_dvd_ramificationIdx_of_height_eq_one_of_iteratedRadicalRoot_mem
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (q : Ideal (iteratedRadical A r n a)) [q.IsPrime]
    (hqheight : q.height = 1) (i : Fin r)
    (hai : Prime (a i))
    (hroot : iteratedRadicalRoot A n a i ∈ q) :
    n i ∣ q.ramificationIdx A := by
  let B := iteratedRadical A r n a
  let : Module.Finite A B := finite_iteratedRadical n a hn
  let : Module.FaithfullyFlat A B := faithfullyFlat_iteratedRadical n a hn
  let Sq := Localization.AtPrime q
  have hunder : q.under A = Ideal.span {a i} :=
    under_eq_span_radicand_of_height_eq_one_of_iteratedRadicalRoot_mem
      n a hn q hqheight i hai hroot
  let z : B := iteratedRadicalRoot A n a i
  let zq : Sq := algebraMap B Sq z
  have hmap_radicand_regular :
      algebraMap A B (a i) ∈ nonZeroDivisors B := by
    rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    have hregular : IsSMulRegular B (a i) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr hai.ne_zero)
    apply hregular
    simpa only [Algebra.smul_def, map_zero, mul_zero] using hx
  have hz_regular : z ∈ nonZeroDivisors B := by
    rw [mem_nonZeroDivisors_iff_left]
    intro x hzx
    have hpowx : z ^ n i * x = 0 := by
      rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (hn i).ne'),
        pow_succ, mul_assoc, hzx, mul_zero]
    apply (mem_nonZeroDivisors_iff_left.mp hmap_radicand_regular) x
    rw [← iteratedRadicalRoot_pow n a i]
    exact hpowx
  have hzq_regular : zq ∈ nonZeroDivisors Sq :=
    IsLocalization.nonZeroDivisors_le_comap q.primeCompl Sq hz_regular
  have hzpow : zq ^ n i = algebraMap A Sq (a i) := by
    calc
      zq ^ n i = algebraMap B Sq (z ^ n i) := (map_pow _ z (n i)).symm
      _ = algebraMap B Sq (algebraMap A B (a i)) := by
        rw [iteratedRadicalRoot_pow n a i]
      _ = algebraMap A Sq (a i) :=
        IsScalarTower.algebraMap_apply A B Sq (a i)
  have hmap_under :
      (q.under A).map (algebraMap A Sq) = Ideal.span {zq ^ n i} := by
    rw [hunder, Ideal.map_span]
    simp only [Set.image_singleton]
    rw [hzpow]
  rw [Ideal.ramificationIdx_def, hmap_under]
  change n i ∣ (Ring.ord Sq (zq ^ n i)).toNat
  rw [Ring.ord_pow hzq_regular, nsmul_eq_mul, ENat.toNat_mul,
    ENat.toNat_natCast]
  exact dvd_mul_right (n i) (Ring.ord Sq zq).toNat

/-- Every height-one prime of the positive iterated root cover either extends
to the full boundary-complement Away localization, or meets a labelled root;
in the latter case its base contraction and the resulting ramification-index
divisibility are both produced by the construction. -/
theorem heightOnePrime_away_or_exists_branch_under_eq_and_exponent_dvd
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i) (ha : ∀ i, Prime (a i))
    (q : Ideal (iteratedRadical A r n a)) [q.IsPrime]
    (hqheight : q.height = 1) :
    Disjoint
        ((Submonoid.powers
          (algebraMap A (iteratedRadical A r n a) (∏ i, a i)) :
            Submonoid (iteratedRadical A r n a)) :
          Set (iteratedRadical A r n a))
        (q : Set (iteratedRadical A r n a)) ∨
      ∃ i,
        q.under A = Ideal.span {a i} ∧
          n i ∣ q.ramificationIdx A := by
  classical
  by_cases havoid : ∀ i, iteratedRadicalRoot A n a i ∉ q
  · exact Or.inl
      (disjoint_powers_prod_radicands_of_iteratedRadicalRoots_not_mem
        n a q havoid)
  · simp only [not_forall, not_not] at havoid
    obtain ⟨i, hroot⟩ := havoid
    exact Or.inr ⟨i,
      under_eq_span_radicand_of_height_eq_one_of_iteratedRadicalRoot_mem
        n a hn q hqheight i (ha i) hroot,
      exponent_dvd_ramificationIdx_of_height_eq_one_of_iteratedRadicalRoot_mem
        n a hn q hqheight i (ha i) hroot⟩

end EtaleFundamentalGroups.Kummer

end
