/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.Nat.GCD.Basic
import Nyll.ProCGroups.InverseSystems.Basic
import Mathlib.Topology.Order

/-!
# The roots-of-unity inverse system over every invertible exponent

The index is the actual set of natural numbers invertible in the base field,
ordered by divisibility. Every index is positive. The transition from degree
`n` to a divisor `m` is the actual power map with exponent `n / m`.

This constructs the complete prime-to-residue-characteristic target of
Stacks Project, Tag 0BUB; no inverse system or comparison is supplied as data.
https://stacks.math.columbia.edu/tag/0BUB
-/

namespace EtaleFundamentalGroups.Inertia

open ProCGroups.InverseSystems

universe u v w

/-- The actual exponents prime to the characteristic of the displayed field. -/
def InvertibleExponent (k : Type u) [Field k] := {n : ℕ // IsUnit (n : k)}

namespace InvertibleExponent

variable (k : Type u) [Field k]

instance : PartialOrder (InvertibleExponent k) where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans a b c hab hbc := dvd_trans hab hbc
  le_antisymm a b hab hba := Subtype.ext (Nat.dvd_antisymm hab hba)

instance : Inhabited (InvertibleExponent k) :=
  ⟨⟨1, by simpa only [Nat.cast_one] using (isUnit_one : IsUnit (1 : k))⟩⟩

/-- Zero is excluded by the actual invertibility condition. -/
theorem pos (n : InvertibleExponent k) : 0 < n.val := by
  apply Nat.pos_of_ne_zero
  intro hn
  apply n.property.ne_zero
  rw [hn, Nat.cast_zero]

/-- The actual invertible exponents form a directed divisibility order. -/
theorem directed : Directed (· ≤ ·) (id : InvertibleExponent k → InvertibleExponent k) := by
  intro m n
  let r : InvertibleExponent k := ⟨m.val * n.val, by
    rw [Nat.cast_mul]
    exact m.property.mul n.property⟩
  exact ⟨r, dvd_mul_right m.val n.val, dvd_mul_left n.val m.val⟩

end InvertibleExponent

/-- The standard transition on actual roots of unity for a divisible pair
of exponents. -/
def rootsOfUnityPowerTransition
    (R : Type v) [CommMonoid R] {m n : ℕ} (h : m ∣ n) :
    rootsOfUnity n R →* rootsOfUnity m R where
  toFun ζ := ⟨(ζ : Rˣ) ^ (n / m), by
    apply (mem_rootsOfUnity m ((ζ : Rˣ) ^ (n / m))).mpr
    rw [← pow_mul, Nat.div_mul_cancel h]
    exact (mem_rootsOfUnity n (ζ : Rˣ)).mp ζ.property⟩
  map_one' := by
    apply Subtype.ext
    exact one_pow (n / m)
  map_mul' ξ ζ := by
    apply Subtype.ext
    exact mul_pow (ξ : Rˣ) (ζ : Rˣ) (n / m)

/-- The transition at a positive exponent is the identity. -/
theorem rootsOfUnityPowerTransition_self
    (R : Type v) [CommMonoid R] (n : ℕ) (hn : n ≠ 0)
    (ζ : rootsOfUnity n R) : rootsOfUnityPowerTransition R (dvd_refl n) ζ = ζ := by
  apply Subtype.ext
  change (ζ : Rˣ) ^ (n / n) = (ζ : Rˣ)
  rw [Nat.div_self (Nat.pos_of_ne_zero hn), pow_one]

/-- Divisibility transitions compose with their actual quotient exponents. -/
theorem rootsOfUnityPowerTransition_trans
    (R : Type v) [CommMonoid R] {m n r : ℕ} (hmn : m ∣ n) (hnr : n ∣ r)
    (ζ : rootsOfUnity r R) :
    rootsOfUnityPowerTransition R hmn (rootsOfUnityPowerTransition R hnr ζ) =
      rootsOfUnityPowerTransition R (dvd_trans hmn hnr) ζ := by
  apply Subtype.ext
  change ((ζ : Rˣ) ^ (r / n)) ^ (n / m) = (ζ : Rˣ) ^ (r / m)
  rw [← pow_mul, Nat.div_mul_div hnr hmn]

/-- Coefficient maps commute with the actual roots-of-unity power
transitions. No map between inverse limits is assumed. -/
theorem restrictRootsOfUnity_powerTransition
    {R : Type v} {S : Type w} [CommMonoid R] [CommMonoid S]
    (f : R →* S) {m n : ℕ} (h : m ∣ n) (ζ : rootsOfUnity n R) :
    restrictRootsOfUnity f m (rootsOfUnityPowerTransition R h ζ) =
      rootsOfUnityPowerTransition S h (restrictRootsOfUnity f n ζ) := by
  apply rootsOfUnity.coe_injective
  change f (((ζ : Rˣ) : R) ^ (n / m)) = (f ((ζ : Rˣ) : R)) ^ (n / m)
  exact map_pow f ((ζ : Rˣ) : R) (n / m)

/-- The literal complete prime-to-characteristic roots system. The base
field determines the index; the displayed target field contains the roots. -/
def primeToRootsSystem (k : Type u) (E : Type v) [Field k] [Field E] :
    InverseSystem (I := InvertibleExponent k) where
  X n := rootsOfUnity n.val E
  topologicalSpace n := ⊥
  map := fun {m n} h => rootsOfUnityPowerTransition E (show m.val ∣ n.val from h)
  continuous_map := fun {_ _} _ => continuous_bot
  map_id := by
    intro n
    funext ζ
    exact rootsOfUnityPowerTransition_self E n.val (InvertibleExponent.pos k n).ne' ζ
  map_comp := by
    intro m n r hmn hnr
    funext ζ
    exact rootsOfUnityPowerTransition_trans E hmn hnr ζ

instance primeToRootsSystem_group
    (k : Type u) (E : Type v) [Field k] [Field E] (n : InvertibleExponent k) :
    Group ((primeToRootsSystem k E).X n) :=
  inferInstanceAs (Group (rootsOfUnity n.val E))

instance primeToRootsSystem_isGroupSystem
    (k : Type u) (E : Type v) [Field k] [Field E] :
    IsGroupSystem (primeToRootsSystem k E) where
  map_one := fun {m n} h => map_one (rootsOfUnityPowerTransition E (show m.val ∣ n.val from h))
  map_mul := fun {m n} h ξ ζ =>
    map_mul (rootsOfUnityPowerTransition E (show m.val ∣ n.val from h)) ξ ζ
  map_inv := fun {m n} h ζ => map_inv (rootsOfUnityPowerTransition E (show m.val ∣ n.val from h)) ζ

instance primeToRootsSystem_finite
    (k : Type u) (E : Type v) [Field k] [Field E] (n : InvertibleExponent k) :
    Finite ((primeToRootsSystem k E).X n) := by
  have : NeZero n.val := ⟨(InvertibleExponent.pos k n).ne'⟩
  change Finite (rootsOfUnity n.val E)
  infer_instance

instance primeToRootsSystem_discreteTopology
    (k : Type u) (E : Type v) [Field k] [Field E] (n : InvertibleExponent k) :
    DiscreteTopology ((primeToRootsSystem k E).X n) := ⟨rfl⟩

end EtaleFundamentalGroups.Inertia
