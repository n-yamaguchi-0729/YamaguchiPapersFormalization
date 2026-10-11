/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.HenselianIntegralFiber
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic


/-!
# Stabilizers of the actual integral-fiber idempotents

The unique idempotent isolating a closed-fiber prime has exactly that prime's
stabilizer. Over a local base with separably closed residue field, integrality
makes the residue quotient purely inseparable, so the prime stabilizer is its
inertia group. These are the group-action inputs for the invariant-factor
projection in Stacks tag 0BST.
-/

namespace EtaleFundamentalGroups.Inertia

open scoped Pointwise

universe u v w

variable (A : Type u) (R : Type v) (G : Type w)
  [CommRing A] [CommRing R] [Algebra A R]
  [Group G] [MulSemiringAction G R] [SMulCommClass G A R]

/-- The original ring action induces its canonical permutation action on
all actual primes over a fixed base ideal. No choice of orbit representatives
or new action on the original ring is involved. -/
def primeFiberPermutation (p : Ideal A) : G →* Equiv.Perm (p.primesOver R) where
  toFun g :=
    { toFun := fun q => Ideal.primesOver.mk p (g • q.val)
      invFun := fun q => Ideal.primesOver.mk p (g⁻¹ • q.val)
      left_inv := fun q => Subtype.ext (inv_smul_smul g q.val)
      right_inv := fun q => Subtype.ext (smul_inv_smul g q.val) }
  map_one' := by
    apply Equiv.ext
    intro q
    exact Subtype.ext (one_smul G q.val)
  map_mul' g h := by
    apply Equiv.ext
    intro q
    exact Subtype.ext (mul_smul g h q.val)

private theorem smul_isolating_support (p : Ideal A) (q : Ideal R) (e : R)
    (hsupp : ∀ Q : Ideal R, Q.IsPrime → Q.LiesOver p → (e ∉ Q ↔ Q = q)) (g : G) :
    ∀ Q : Ideal R, Q.IsPrime → Q.LiesOver p → (g • e ∉ Q ↔ Q = g • q) := by
  intro Q hQ hQp
  have : Q.IsPrime := hQ
  have : Q.LiesOver p := hQp
  rw [← Ideal.mem_inv_pointwise_smul_iff, hsupp (g⁻¹ • Q) inferInstance inferInstance]
  constructor
  · intro h
    calc
      Q = g • (g⁻¹ • Q) := (smul_inv_smul g Q).symm
      _ = g • q := congrArg (fun P : Ideal R => g • P) h
  · intro h
    rw [h, inv_smul_smul]

/-- An actual isolating idempotent has precisely the stabilizer of its
prescribed closed-fiber prime. The support hypotheses are supplied by
`existsUnique_idempotent_of_finite_integral_fiber`. -/
theorem isolatingIdempotent_stabilizer_eq [HenselianLocalRing A]
    [Algebra.IsIntegral A R]
    (hfinite : ((IsLocalRing.maximalIdeal A).primesOver R).Finite)
    (q : Ideal R) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal A)]
    (e : R) (he : IsIdempotentElem e)
    (hsupp : ∀ Q : Ideal R, Q.IsPrime → Q.LiesOver (IsLocalRing.maximalIdeal A) →
      (e ∉ Q ↔ Q = q)) :
    MulAction.stabilizer G e = MulAction.stabilizer G q := by
  have heq : e ∉ q := (hsupp q inferInstance inferInstance).mpr rfl
  apply Subgroup.ext
  intro g
  change g • e = e ↔ g • q = q
  constructor
  · intro hg
    apply (hsupp (g • q) inferInstance inferInstance).mp
    rw [← hg]
    exact fun h => heq (Ideal.smul_mem_pointwise_smul_iff.mp h)
  · intro hg
    obtain ⟨e₀, _, huniq⟩ :=
      existsUnique_idempotent_of_finite_integral_fiber A R hfinite q
    have htranslated : ∀ Q : Ideal R, Q.IsPrime →
        Q.LiesOver (IsLocalRing.maximalIdeal A) → (g • e ∉ Q ↔ Q = q) := by
      simpa only [hg] using
        smul_isolating_support A R G (IsLocalRing.maximalIdeal A) q e hsupp g
    exact (huniq (g • e)
      ⟨he.map (MulSemiringAction.toRingAut G R g), htranslated⟩).trans
        (huniq e ⟨he, hsupp⟩).symm

/-- The actual prime-indexed isolating family is equivariant for the
canonical permutations of its prime indices. Every equation follows from
the uniqueness of the already constructed idempotents. -/
theorem isolatingIdempotents_equivariant [HenselianLocalRing A]
    [Algebra.IsIntegral A R]
    (hfinite : ((IsLocalRing.maximalIdeal A).primesOver R).Finite)
    (e : ((IsLocalRing.maximalIdeal A).primesOver R) → R)
    (he : ∀ q, IsIdempotentElem (e q))
    (hsupp : ∀ (q : (IsLocalRing.maximalIdeal A).primesOver R) (Q : Ideal R),
      Q.IsPrime → Q.LiesOver (IsLocalRing.maximalIdeal A) → (e q ∉ Q ↔ Q = q.val))
    (g : G) (q : (IsLocalRing.maximalIdeal A).primesOver R) :
    g • e q = e (primeFiberPermutation A R G (IsLocalRing.maximalIdeal A) g q) := by
  let qg := primeFiberPermutation A R G (IsLocalRing.maximalIdeal A) g q
  obtain ⟨e₀, _, huniq⟩ :=
    existsUnique_idempotent_of_finite_integral_fiber A R hfinite qg.val
  exact (huniq (g • e q)
    ⟨(he q).map (MulSemiringAction.toRingAut G R g),
      smul_isolating_support A R G (IsLocalRing.maximalIdeal A) q.val (e q) (hsupp q) g⟩).trans
    (huniq (e qg) ⟨he qg, hsupp qg⟩).symm

/-- Over a local base with separably closed residue field, every element of
the prime stabilizer acts trivially on the integral residue quotient. Thus
the actual inertia subgroup equals the prime stabilizer, without a finite
type or finite-group hypothesis. -/
theorem inertia_eq_stabilizer_of_integral_of_residue_isSepClosed
    [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    [Algebra.IsIntegral A R]
    (q : Ideal R) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal A)] :
    q.inertia G = MulAction.stabilizer G q := by
  have : q.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal q (IsLocalRing.maximalIdeal A)
  let : Field (R ⧸ q) := Ideal.Quotient.field q
  let : Algebra (IsLocalRing.ResidueField A) (R ⧸ q) :=
    Ideal.Quotient.algebraOfLiesOver q (IsLocalRing.maximalIdeal A)
  have : Algebra.IsIntegral (IsLocalRing.ResidueField A) (R ⧸ q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver q (IsLocalRing.maximalIdeal A)
  have : IsPurelyInseparable (IsLocalRing.ResidueField A) (R ⧸ q) := inferInstance
  let ρ := Ideal.Quotient.stabilizerHom q (IsLocalRing.maximalIdeal A) G
  apply le_antisymm q.inertia_le_stabilizer
  intro g hg
  have hker : (⟨g, hg⟩ : MulAction.stabilizer G q) ∈ ρ.ker := by
    change ρ ⟨g, hg⟩ = 1
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.coe_ringHom_injective
    apply IsPurelyInseparable.injective_comp_algebraMap
      (IsLocalRing.ResidueField A) (R ⧸ q) (R ⧸ q)
    exact ((ρ ⟨g, hg⟩).toAlgHom.comp_algebraMap).trans
      ((1 : (R ⧸ q) ≃ₐ[IsLocalRing.ResidueField A] (R ⧸ q)).toAlgHom.comp_algebraMap).symm
  have hmap : g ∈ ρ.ker.map (Subgroup.subtype (MulAction.stabilizer G q)) :=
    ⟨⟨g, hg⟩, hker, rfl⟩
  rw [Ideal.Quotient.map_ker_stabilizer_subtype] at hmap
  exact hmap

/-- An equivariant family mapping to an actual isolating idempotent has
precisely the original prime's inertia as its selected stabilizer. The map
need not be injective: one direction uses the literal image, and the other
uses the prescribed permutation of the actual prime indices. -/
theorem isolatingIdempotent_stabilizer_eq_inertia_of_map
    [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    [Algebra.IsIntegral A R]
    (hfinite : ((IsLocalRing.maximalIdeal A).primesOver R).Finite)
    {S : Type*} [CommRing S] [MulSemiringAction G S]
    (f : S →+* R) (hf : ∀ (g : G) (s : S), f (g • s) = g • f s)
    (q : (IsLocalRing.maximalIdeal A).primesOver R)
    (eS : ((IsLocalRing.maximalIdeal A).primesOver R) → S)
    (hσ : ∀ g : G, g • eS q =
      eS (primeFiberPermutation A R G (IsLocalRing.maximalIdeal A) g q))
    (e : R) (he : IsIdempotentElem e)
    (hsupp : ∀ Q : Ideal R, Q.IsPrime → Q.LiesOver (IsLocalRing.maximalIdeal A) →
      (e ∉ Q ↔ Q = q.val))
    (hmap : f (eS q) = e) :
    MulAction.stabilizer G (eS q) = q.val.inertia G := by
  rw [inertia_eq_stabilizer_of_integral_of_residue_isSepClosed A R G q.val]
  apply Subgroup.ext
  intro g
  change g • eS q = eS q ↔ g • q.val = q.val
  constructor
  · intro hg
    have hge : g • e = e := by
      rw [← hmap, ← hf, hg]
    have hgmem : g ∈ MulAction.stabilizer G e := hge
    rw [isolatingIdempotent_stabilizer_eq A R G hfinite q.val e he hsupp] at hgmem
    exact hgmem
  · intro hg
    have hq : primeFiberPermutation A R G (IsLocalRing.maximalIdeal A) g q = q :=
      Subtype.ext hg
    rw [hσ, hq]

end EtaleFundamentalGroups.Inertia
