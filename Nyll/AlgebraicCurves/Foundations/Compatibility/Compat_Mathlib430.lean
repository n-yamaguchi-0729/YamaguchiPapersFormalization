/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Compat_Mathlib430.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Earlier source notices recorded for the cited upstream material:
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Authors: Antoine Labelle
https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/RepresentationTheory/Basic.lean
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Authors: Edison Xie, Kim Morrison
https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/RepresentationTheory/Rep/Basic.lean
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Algebra/Group/End.lean
Copyright (c) 2018 Chris Hughes. All rights reserved.
Authors: Chris Hughes, Yury Kudryashov
https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Algebra/GroupWithZero/Action/Basic.lean
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Authors: Yury Kudryashov
https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Algebra/Ring/AddAut.lean
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Authors: David Kurniadi Angdinata
https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean
Copyright (c) 2024 David Ang. All rights reserved.
Authors: David Ang
https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Algebra/Ring/Action/Submonoid.lean
Copyright (c) 2024 Yongle Hu. All rights reserved.
Authors: Yongle Hu, Jiedong Jiang
https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/NumberTheory/RamificationInertia/Galois.lean

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-
Copyright: the vendored blocks below are verbatim copies from Mathlib (Apache-2.0; see Mathlib's
LICENSE),
release v4.30.0 = leanprover-community/mathlib4 commit c5ea00351c28e24afc9f0f84379aa41082b1188f,
with declarations
RENAMED (suffix `Finsupp` / trailing prime) so they do not clash with Mathlib v4.33.0. Bodies
are the Mathlib v4.30.0 text
with its docstrings omitted, otherwise byte-identical unless a line is marked `-- [port]`.
-/

/-! ## Block A — Mathlib v4.30.0 Mathlib/RepresentationTheory/Basic.lean:391-419 (section
MulAction), names suffixed `Finsupp` -/

namespace Representation

section MulAction

variable (k : Type*) [Semiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]

/-- The representation on finitely supported functions induced by the given action on their
indices. -/
noncomputable def ofMulActionFinsupp : Representation k G (H →₀ k) where
  toFun g := Finsupp.lmapDomain k k (g • ·)
  map_one' := by
    ext x y
    simp
  map_mul' x y := by
    ext z w
    simp [mul_smul]

/-- The left regular representation on finitely supported functions on the group. -/
noncomputable abbrev leftRegularFinsupp := ofMulActionFinsupp k G G

/-- The representation on finitely supported functions on tuples under the diagonal group
action. -/
noncomputable abbrev diagonalFinsupp (n : ℕ) := ofMulActionFinsupp k G (Fin n → G)

variable {k G H}

theorem ofMulActionFinsupp_def (g : G) : ofMulActionFinsupp k G H g = Finsupp.lmapDomain k k (g •
  ·) :=
  rfl
@[simp]
theorem ofMulActionFinsupp_single (g : G) (x : H) (r : k) :
    ofMulActionFinsupp k G H g (Finsupp.single x r) = Finsupp.single (g • x) r :=
  Finsupp.mapDomain_single

end MulAction

/-! ## Block B — Mathlib v4.30.0 Mathlib/RepresentationTheory/Basic.lean:472-483 (section Group) -/

section Group

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)
@[simp]
theorem ofMulActionFinsupp_apply {H : Type*} [MulAction G H] (g : G) (f : H →₀ k) (h : H) :
    ofMulActionFinsupp k G H g f h = f (g⁻¹ • h) := by
  conv_lhs => rw [← smul_inv_smul g h]
  let h' := g⁻¹ • h
  change ofMulActionFinsupp k G H g f (g • h') = f h'
  have hg : Function.Injective (g • · : H → H) := by
    intro h₁ h₂
    simp
  simp only [ofMulActionFinsupp_def, Finsupp.lmapDomain_apply, Finsupp.mapDomain_apply_of_injective
    hg]

end Group

section Bridge

variable (k : Type*) [Semiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]

/-- The equivalence between the finitely supported-function model and the monoid-algebra model
of the action. -/
noncomputable def ofMulActionFinsuppEquiv : (ofMulActionFinsupp k G H).Equiv (ofMulAction k G H) :=
  Equiv.mk (MonoidAlgebra.coeffLinearEquiv k).symm fun g => by
    rw [ofMulAction_def, ofMulActionFinsupp_def]
    ext
    simp

end Bridge

end Representation

/-! ## Block C — Mathlib v4.30.0 Mathlib/RepresentationTheory/Rep/Basic.lean:336-346 and
404-412, names suffixed `Finsupp` -/

namespace Rep

open CategoryTheory

universe w' u v

variable {k : Type u} {G : Type v} [Ring k] [Monoid G]

section

variable (k G)

/-- The representation object on finitely supported functions induced by the given action on
their indices. -/
noncomputable abbrev ofMulActionFinsupp (H : Type w') [MulAction G H] : Rep k G :=
  -- [port] `noncomputable` added (4.30 file had a noncomputable section)
  of <| Representation.ofMulActionFinsupp k G H

/-- The left regular representation object on finitely supported functions on the group. -/
noncomputable abbrev leftRegularFinsupp : Rep k G :=
  -- [port] noncomputable
  ofMulActionFinsupp k G G

/-- The representation object on finitely supported functions on tuples under the diagonal group
action. -/
noncomputable abbrev diagonalFinsupp (n : ℕ) : Rep k G :=
  -- [port] noncomputable
  ofMulActionFinsupp k G (Fin n → G)

/-- The isomorphism between the finitely supported-function and monoid-algebra action
representations. -/
noncomputable def ofMulActionFinsuppIso (H : Type w') [MulAction G H] :
    ofMulActionFinsupp k G H ≅ ofMulAction k G H :=
  mkIso (Representation.ofMulActionFinsuppEquiv k G H)

end

/-- The map from the left regular representation sending its identity basis vector to the chosen
vector. -/
noncomputable abbrev leftRegularHomFinsupp (A : Rep k G) (x : A) : leftRegularFinsupp k G ⟶ A :=
  -- [port] noncomputable
  Rep.ofHom ⟨Finsupp.lift A k G fun g ↦ A.ρ g x, fun g ↦ by ext; simp⟩

theorem leftRegularHomFinsupp_hom_single {A : Rep k G} (g : G) (x : A) (r : k) :
    (leftRegularHomFinsupp A x).hom (.single g r) = r • A.ρ g x := by
  simp [leftRegularHomFinsupp]

end Rep

/-! ## Block D — AddAut: Mathlib v4.30.0 Mathlib/Algebra/Group/End.lean:746-801 (+
GroupWithZero/Action/Basic.lean:89-92 and :104-112, Ring/AddAut.lean:32), lemma names primed -/

namespace AddAut

section Compat430

variable (A : Type*) [Add A]

instance : Group (AddAut A) where
  mul g h := AddEquiv.trans h g
  one := AddEquiv.refl _
  inv := AddEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := AddEquiv.self_trans_symm
/- The following thirteen lemmas are Mathlib v4.30.0 `Mathlib/Algebra/Group/End.lean:758-801`
verbatim except that each name carries a trailing prime. -/
@[simp]
theorem coe_mul' (e₁ e₂ : AddAut A) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl
@[simp]
theorem coe_one' : ⇑(1 : AddAut A) = id :=
  rfl
@[simp]
theorem coe_inv' (e : AddAut A) : ⇑e⁻¹ = e.symm := rfl

theorem mul_def' (e₁ e₂ : AddAut A) : e₁ * e₂ = e₂.trans e₁ :=
  rfl

theorem one_def' : (1 : AddAut A) = AddEquiv.refl _ :=
  rfl

theorem inv_def' (e₁ : AddAut A) : e₁⁻¹ = e₁.symm :=
  rfl
@[simp]
theorem mul_apply' (e₁ e₂ : AddAut A) (a : A) : (e₁ * e₂) a = e₁ (e₂ a) :=
  rfl
@[simp]
theorem one_apply' (a : A) : (1 : AddAut A) a = a :=
  rfl
@[simp]
theorem inv_symm' (e : AddAut A) : e⁻¹.symm = e := rfl
@[simp]
theorem symm_inv' (e : AddAut A) : e.symm⁻¹ = e := rfl
@[simp]
theorem inv_apply' (e : AddAut A) (a : A) : e⁻¹ a = e.symm a := rfl

theorem inv_apply_self' (e : AddAut A) (a : A) : e⁻¹ (e a) = a :=
  AddEquiv.apply_symm_apply _ _

theorem apply_inv_self' (e : AddAut A) (a : A) : e (e⁻¹ a) = a :=
  AddEquiv.apply_symm_apply _ _

example (e₁ e₂ : AddAut A) : e₁ * e₂ = e₁ + e₂ := rfl
example : (1 : AddAut A) = 0 := rfl
example (e : AddAut A) : e⁻¹ = -e := rfl

end Compat430

end AddAut

/-- The homomorphism to additive automorphisms induced by a distributive group action. -/
@[simps]
def DistribMulAction.toAddAut' (G A : Type*) [Group G] [AddMonoid A] [DistribMulAction G A] :
    G →* AddAut A where
  toFun := DistribMulAction.toAddEquiv A
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)
/-- The homomorphism sending a unit to the additive automorphism given by left multiplication. -/
@[simps! +simpRhs]
def AddAut.mulLeft' {R : Type*} [Semiring R] : Rˣ →* AddAut R :=
  DistribMulAction.toAddAut' _ _

/-! ### Block D (continued) — Mathlib v4.30.0
Mathlib/Algebra/GroupWithZero/Action/Basic.lean:104-112: the tautological `DistribMulAction
(AddAut A) A`
(`AddAut.applyDistribMulAction`, its `smul_def` and `apply_faithfulSMul`), dropped in v4.33.0
together with the multiplicative structure;
vendored with primed names on top of the Group instance above. -/

namespace AddAut
instance applyDistribMulAction' {A : Type*} [AddMonoid A] : DistribMulAction (AddAut A) A where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := AddEquiv.map_zero
  smul_add := AddEquiv.map_add

@[simp] protected theorem smul_def' {A : Type*} [AddMonoid A] (f : AddAut A) (a : A) : f • a = f a
  := rfl

instance apply_faithfulSMul' {A : Type*} [AddMonoid A] : FaithfulSMul (AddAut A) A :=
  ⟨fun h => AddEquiv.ext h⟩
end AddAut

/-! ## Block E — elliptic (divisibility) sequence predicates: Mathlib v4.30.0
Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:78-110 (verbatim; names primed). Vendored
because Mathlib v4.33.0 (db584cd6,
same file :286-295) RENAMED AND REDEFINED them (`IsEllipticSequence W := ∀ p q r,
IsEllipticNet.rel W p q r 0 = 0`,
`IsDvdSequence` over ℤ instead of ℕ) and kept the 4.30 names only as deprecated aliases of the
NEW predicates. -/

section IsEllDivSequence430

universe u

variable {R : Type u} [CommRing R]

variable (W : ℤ → R)

/-- The elliptic-sequence identity for an integer-indexed sequence. -/
def IsEllSequence' : Prop :=
  ∀ m n r : ℤ, W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

/-- The divisibility condition on sequence values at divisible natural-number indices. -/
def IsDivSequence' : Prop :=
  ∀ m n : ℕ, m ∣ n → W m ∣ W n

/-- The conjunction of the elliptic-sequence and divisibility identities. -/
def IsEllDivSequence' : Prop :=
  IsEllSequence' W ∧ IsDivSequence' W

lemma isEllSequence'_id : IsEllSequence' id :=
  fun _ _ _ => by simp_rw [id_eq]; ring1

lemma isDivSequence'_id : IsDivSequence' id :=
  fun _ _ => Int.ofNat_dvd.mpr

theorem isEllDivSequence'_id : IsEllDivSequence' id :=
  ⟨isEllSequence'_id, isDivSequence'_id⟩

variable {W}

lemma IsEllSequence'.smul (h : IsEllSequence' W) (x : R) : IsEllSequence' (x • W) :=
  fun m n r => by
    linear_combination (norm := (simp_rw [Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h m n r

lemma IsDivSequence'.smul (h : IsDivSequence' W) (x : R) : IsDivSequence' (x • W) :=
  fun m n r => mul_dvd_mul_left x <| h m n r

lemma IsEllDivSequence'.smul (h : IsEllDivSequence' W) (x : R) : IsEllDivSequence' (x • W) :=
  ⟨h.left.smul x, h.right.smul x⟩

end IsEllDivSequence430


/-! ## Block F — notation `α ^+ M` for `FixedPoints.addSubgroup M α`: Mathlib v4.30.0
Mathlib/Algebra/Ring/Action/Submonoid.lean:43
(verbatim). Mathlib v4.33.0 removed the notation line; the definition itself is unchanged, so
re-declaring the notation keeps
every tree statement that uses it textually and semantically identical. -/

/-- The additive subgroup fixed by the action of the monoid. -/
notation α "^+" M:51 => FixedPoints.addSubgroup M α

/-! ## Block G — ramification/inertia cardinality lemmas under the separability hypothesis
(adapted from Mathlib v4.30.0,
Mathlib/NumberTheory/RamificationInertia/Galois.lean; v4.33.0 restates them assuming
PerfectField of the residue field). Theorems only,
primed names; no definitions involved. -/

namespace Ideal

section inertia430

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

open scoped Pointwise


attribute [local instance] Ideal.Quotient.field in
theorem card_stabilizer_eq_card_inertia_mul_finrank' (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (MulAction.stabilizer G P) = Nat.card (inertia G P) *
      Module.finrank (R ⧸ p) (S ⧸ P) := by
  have : IsGalois (R ⧸ p) (S ⧸ P) := { __ := Ideal.Quotient.normal (A := R) G p P }
  have := Ideal.Quotient.finite_of_isInvariant G p P
  have : Subgroup.index _ = _ := Nat.card_congr
    (Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv
  rw [← IsGalois.card_aut_eq_finrank, ← this,
    ← ((inertia G P).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inertia_le_stabilizer (M := G) P)).toEquiv,
    AddSubgroup.subgroupOf_inertia]

lemma ncard_primesOver_mul_card_inertia_mul_finrank' (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    (p.primesOver S).ncard * Nat.card (P.inertia G) *
      Module.finrank (R ⧸ p) (S ⧸ P) = Nat.card G := by
  rw [mul_assoc, ← card_stabilizer_eq_card_inertia_mul_finrank',
    ← Algebra.IsInvariant.orbit_eq_primesOver R S G p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

attribute [local instance] Ideal.Quotient.field in
lemma card_inertia_eq_ramificationIdxIn'
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
    [Module.IsTorsionFree R S]
    (p : Ideal R) (hp : p ≠ ⊥)
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (P.inertia G) = Ideal.ramificationIdxIn p S := by
  have := (show p.IsPrime from P.over_def p ▸ inferInstance).isMaximal hp
  have H := ncard_primesOver_mul_card_inertia_mul_finrank' (G := G) p P
  refine mul_right_injective₀ (IsDedekindDomain.primesOver_ncard_ne_zero p S) ?_
  refine mul_left_injective₀ (b := Module.finrank (R ⧸ p) (S ⧸ P)) ?_ ?_
  · intro e; simp [e, eq_comm, Nat.card_eq_zero, ‹Finite G›.not_infinite] at H
  dsimp only
  rw [H, mul_assoc, ← inertiaDeg_eq_of_isMaximal p P, ← inertiaDegIn_eq_inertiaDeg p P G,
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G]

attribute [local instance] Ideal.Quotient.field in
lemma card_stabilizer_eq' [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
    [Module.IsTorsionFree R S] (p : Ideal R) (hp : p ≠ ⊥) (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (MulAction.stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S := by
  have := (show p.IsPrime from P.over_def p ▸ inferInstance).isMaximal hp
  rw [card_stabilizer_eq_card_inertia_mul_finrank' p P, card_inertia_eq_ramificationIdxIn' p hp,
    inertiaDegIn_eq_inertiaDeg p P G, inertiaDeg_eq_of_isMaximal p P]

end inertia430

end Ideal
