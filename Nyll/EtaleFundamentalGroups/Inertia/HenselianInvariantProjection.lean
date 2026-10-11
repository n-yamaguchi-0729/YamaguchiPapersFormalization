/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.HenselianIntegralFiber
import Nyll.EtaleFundamentalGroups.Inertia.HenselianIntegralFiberAction
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Invariant.Basic


/-!
# Extending the selected inertia-invariant factor to full invariants

An element supported on an idempotent and fixed by its stabilizer can be
transported over the finite orbit. Summing one transported element per orbit
point gives a full invariant. Orthogonality ensures that projection onto the
selected idempotent recovers the original element. No group order is inverted.

For an actual isolating idempotent over a strictly Henselian base, uniqueness
supplies orthogonality of its distinct translates, and its stabilizer is the
actual inertia subgroup. Thus an element of the inertia-fixed algebra has a
full invariant with the same selected-factor projection. This is the
surjectivity input for the invariant-factor comparison in Stacks tag 0BST.

The kernel calculation uses that the orbit of an element outside the chosen
closed-fiber prime generates the unit ideal. It preserves the actual kernel
of the original base map and does not assume that map is injective.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open scoped Pointwise

universe u v w

private theorem exists_fixed_mul_eq_of_orthogonal_orbit
    {R : Type v} {G : Type w} [CommRing R] [Group G] [Finite G]
    [MulSemiringAction G R] (e y : R) (hey : e * y = y)
    (hfix : ∀ g : G, g • e = e → g • y = y)
    (horth : ∀ g : G, g • e ≠ e → e * (g • e) = 0) :
    ∃ r : R, (∀ g : G, g • r = r) ∧ e * r = y := by
  classical
  have hfinite : (MulAction.orbit G e).Finite := Set.finite_range (fun g : G => g • e)
  let : Fintype (MulAction.orbit G e) := hfinite.fintype
  have hwell (g h : G) (hgh : g • e = h • e) : g • y = h • y := by
    have hstab : (h⁻¹ * g) • e = e := by
      rw [mul_smul, hgh, inv_smul_smul]
    have hy : (h⁻¹ * g) • y = y := hfix (h⁻¹ * g) hstab
    calc
      g • y = h • ((h⁻¹ * g) • y) := by rw [smul_smul, mul_inv_cancel_left]
      _ = h • y := congrArg (fun r : R => h • r) hy
  let t : MulAction.orbit G e → R := fun z => Classical.choose z.property • y
  have ht (g : G) (z : MulAction.orbit G e) : t (g • z) = g • t z := by
    have hz := Classical.choose_spec z.property
    have hgz := Classical.choose_spec (g • z).property
    have hindex : Classical.choose (g • z).property • e =
        (g * Classical.choose z.property) • e := by
      calc
        Classical.choose (g • z).property • e = (g • z).val := hgz
        _ = g • z.val := rfl
        _ = g • (Classical.choose z.property • e) := congrArg (fun r : R => g • r) hz.symm
        _ = (g * Classical.choose z.property) • e :=
          (mul_smul g (Classical.choose z.property) e).symm
    exact (hwell _ _ hindex).trans (mul_smul g (Classical.choose z.property) y)
  refine ⟨∑ z, t z, ?_, ?_⟩
  · intro g
    rw [Finset.smul_sum]
    exact Fintype.sum_equiv (MulAction.toPerm g) (fun z => g • t z) t
      (fun z => (ht g z).symm)
  · let z₀ : MulAction.orbit G e := ⟨e, ⟨1, one_smul G e⟩⟩
    have ht₀ : t z₀ = y :=
      (hwell _ 1 ((Classical.choose_spec z₀.property).trans (one_smul G e).symm)).trans
        (one_smul G y)
    rw [Finset.mul_sum]
    calc
      ∑ z : MulAction.orbit G e, e * t z = e * t z₀ := by
        apply Finset.sum_eq_single z₀
        · intro z _ hne
          obtain ⟨g, hg⟩ := z.property
          have hge : g • e ≠ e := by
            intro h
            apply hne
            exact Subtype.ext (hg.symm.trans h)
          have htz : t z = g • y :=
            hwell _ g ((Classical.choose_spec z.property).trans hg.symm)
          rw [htz, ← hey, smul_mul', ← mul_assoc, horth g hge, zero_mul]
        · intro h
          exact (h (Finset.mem_univ z₀)).elim
      _ = y := by rw [ht₀, hey]

/-- A transitive finite complete equivariant family identifies the base
with the selected idempotent localization of its stabilizer invariants.
The only base injectivity input is the actual original algebra map. No
Henselian, finite-presentation, or integrality hypothesis is needed. -/
theorem algebraMap_away_bijective_of_transitive_completeOrthogonalIdempotents
    (A : Type u) (R : Type v) (G : Type w)
    [CommRing A] [CommRing R] [Algebra A R] [Group G] [Finite G]
    [MulSemiringAction G R] [SMulCommClass G A R] [Algebra.IsInvariant A R G]
    {ι : Type*} [Fintype ι] (σ : G →* Equiv.Perm ι)
    (e : ι → R) (he : CompleteOrthogonalIdempotents e)
    (hσ : ∀ (g : G) (j : ι), g • e j = e (σ g j)) (i : ι)
    (htrans : ∀ j : ι, ∃ g : G, σ g i = j)
    (hinj : Function.Injective (algebraMap A R)) :
    let eH : FixedPoints.subalgebra A R (MulAction.stabilizer G (e i)) :=
      ⟨e i, fun g => g.property⟩
    Function.Bijective (algebraMap A (Localization.Away eH)) := by
  intro eH
  have heH : IsIdempotentElem eH := Subtype.ext (he.idem i).eq
  constructor
  · apply (RingHom.injective_iff_ker_eq_bot (algebraMap A (Localization.Away eH))).mpr
    apply bot_unique
    intro a ha
    change algebraMap A (Localization.Away eH) a = 0 at ha
    change a = 0
    apply hinj
    rw [map_zero]
    have hkill : e i * algebraMap A R a = 0 := by
      have hmap : algebraMap (FixedPoints.subalgebra A R (MulAction.stabilizer G (e i)))
          (Localization.Away eH)
          (algebraMap A (FixedPoints.subalgebra A R (MulAction.stabilizer G (e i))) a) =
        algebraMap (FixedPoints.subalgebra A R (MulAction.stabilizer G (e i)))
          (Localization.Away eH) 0 := by
        rw [← IsScalarTower.algebraMap_apply A
          (FixedPoints.subalgebra A R (MulAction.stabilizer G (e i)))
          (Localization.Away eH), map_zero]
        exact ha
      obtain ⟨⟨_, n, rfl⟩, hs⟩ :=
        (IsLocalization.eq_iff_exists (Submonoid.powers eH) (Localization.Away eH)).mp hmap
      rw [mul_zero] at hs
      have hs' := congrArg
        (fun z : FixedPoints.subalgebra A R (MulAction.stabilizer G (e i)) => eH * z) hs
      rw [mul_zero, ← mul_assoc, ← pow_succ', heH.pow_succ_eq] at hs'
      exact congrArg Subtype.val hs'
    have hall : ∀ j : ι, e j * algebraMap A R a = 0 := by
      intro j
      obtain ⟨g, hg⟩ := htrans j
      have h := congrArg (fun r : R => g • r) hkill
      rw [smul_mul', smul_algebraMap, smul_zero, hσ, hg] at h
      exact h
    have hsum := congrArg (fun r : R => r * algebraMap A R a) he.complete
    rw [Finset.sum_mul, Finset.sum_eq_zero (fun j _ => hall j), one_mul] at hsum
    exact hsum.symm
  · intro z
    obtain ⟨x, rfl⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
      (S := Localization.Away eH) eH heH z
    obtain ⟨r, hr, her⟩ := exists_fixed_mul_eq_of_orthogonal_orbit (e i) (e i * (x : R))
      (by rw [← mul_assoc, (he.idem i).eq])
      (fun (g : G) (hg : g • e i = e i) => by
        have hx : g • (x : R) = (x : R) := x.property ⟨g, hg⟩
        rw [smul_mul', hg, hx]) (by
        intro g hg
        rw [hσ]
        apply he.ortho
        intro hij
        apply hg
        rw [hσ, ← hij])
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) r hr
    refine ⟨a, ?_⟩
    apply (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away eH) eH).mul_left_cancel
    rw [IsScalarTower.algebraMap_apply A
      (FixedPoints.subalgebra A R (MulAction.stabilizer G (e i))) (Localization.Away eH),
      ← map_mul, ← map_mul]
    apply congrArg (algebraMap (FixedPoints.subalgebra A R (MulAction.stabilizer G (e i)))
      (Localization.Away eH))
    apply Subtype.ext
    change e i * algebraMap A R a = e i * (x : R)
    rw [ha]
    exact her

private theorem span_orbit_eq_top_of_notMem
    (A : Type u) (R : Type v) (G : Type w)
    [CommRing A] [IsLocalRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] [Group G] [Finite G]
    [MulSemiringAction G R] [SMulCommClass G A R] [Algebra.IsInvariant A R G]
    (q : Ideal R) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal A)]
    (e : R) (heq : e ∉ q) : Ideal.span (MulAction.orbit G e) = ⊤ := by
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span (MulAction.orbit G e)) h
  have : M.IsMaximal := hM
  have hMunder : M.under A = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) M)
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A R G q M
    ((q.over_def (IsLocalRing.maximalIdeal A)).symm.trans hMunder.symm)
  have hmem : g • e ∈ M := hle (Ideal.subset_span ⟨g, rfl⟩)
  rw [hg] at hmem
  exact heq (Ideal.smul_mem_pointwise_smul_iff.mp hmem)

/-- Over a local invariant base, annihilation of a base element by anything
outside a chosen closed-fiber prime already forces its image in the whole
algebra to vanish. No injectivity of the base map is assumed. -/
theorem algebraMap_eq_zero_of_mul_eq_zero_of_notMem
    (A : Type u) (R : Type v) (G : Type w)
    [CommRing A] [IsLocalRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] [Group G] [Finite G]
    [MulSemiringAction G R] [SMulCommClass G A R] [Algebra.IsInvariant A R G]
    (q : Ideal R) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal A)]
    (e : R) (heq : e ∉ q) (a : A) (hea : e * algebraMap A R a = 0) :
    algebraMap A R a = 0 := by
  let K : Ideal R := (LinearMap.toSpanSingleton R R (algebraMap A R a)).ker
  have hspan : Ideal.span (MulAction.orbit G e) ≤ K := by
    apply Ideal.span_le.mpr
    rintro _ ⟨g, rfl⟩
    change (g • e) • algebraMap A R a = 0
    rw [smul_eq_mul]
    have h := congrArg (fun r : R => g • r) hea
    rw [smul_mul', smul_algebraMap, smul_zero] at h
    exact h
  have hone : (1 : R) ∈ K := hspan (by
    rw [span_orbit_eq_top_of_notMem A R G q e heq]
    trivial)
  change (1 : R) • algebraMap A R a = 0 at hone
  simpa only [one_smul] using hone

/-- The selected idempotent factor of the inertia-fixed algebra has exactly
the same kernel on the base as the original algebra. This statement retains
the original base-map kernel; it does not assume that the base embeds. -/
theorem algebraMap_away_eq_zero_iff_of_notMem
    (A : Type u) (R : Type v) (G : Type w)
    [CommRing A] [IsLocalRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] [Group G] [Finite G]
    [MulSemiringAction G R] [SMulCommClass G A R] [Algebra.IsInvariant A R G]
    (q : Ideal R) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal A)]
    (e : FixedPoints.subalgebra A R (q.inertia G)) (he : IsIdempotentElem e)
    (heq : (e : R) ∉ q) (a : A) :
    algebraMap A (Localization.Away e) a = 0 ↔ algebraMap A R a = 0 := by
  constructor
  · intro ha
    have hmap : algebraMap (FixedPoints.subalgebra A R (q.inertia G))
        (Localization.Away e) (algebraMap A (FixedPoints.subalgebra A R (q.inertia G)) a) =
      algebraMap (FixedPoints.subalgebra A R (q.inertia G)) (Localization.Away e) 0 := by
      rw [← IsScalarTower.algebraMap_apply A (FixedPoints.subalgebra A R (q.inertia G))
        (Localization.Away e), map_zero]
      exact ha
    obtain ⟨⟨_, n, rfl⟩, hs⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers e) (Localization.Away e)).mp hmap
    rw [mul_zero] at hs
    have hs' := congrArg (fun z : FixedPoints.subalgebra A R (q.inertia G) => e * z) hs
    rw [mul_zero, ← mul_assoc, ← pow_succ', he.pow_succ_eq] at hs'
    apply algebraMap_eq_zero_of_mul_eq_zero_of_notMem A R G q (e : R) heq a
    exact congrArg Subtype.val hs'
  · intro ha
    have ha' : algebraMap A (FixedPoints.subalgebra A R (q.inertia G)) a = 0 :=
      Subtype.ext ha
    rw [IsScalarTower.algebraMap_apply A (FixedPoints.subalgebra A R (q.inertia G))
      (Localization.Away e), ha', map_zero]

variable (A : Type u) (R : Type v) (G : Type w)
  [CommRing A] [HenselianLocalRing A] [CommRing R] [Algebra A R]
  [Algebra.IsIntegral A R] [Group G] [MulSemiringAction G R] [SMulCommClass G A R]

private theorem isolatingIdempotent_mul_smul_eq_zero
    (hfinite : ((IsLocalRing.maximalIdeal A).primesOver R).Finite)
    (q : Ideal R) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal A)]
    (e : R) (he : IsIdempotentElem e)
    (hsupp : ∀ Q : Ideal R, Q.IsPrime → Q.LiesOver (IsLocalRing.maximalIdeal A) →
      (e ∉ Q ↔ Q = q)) (g : G) (hg : g • e ≠ e) : e * (g • e) = 0 := by
  have heq : e ∉ q := (hsupp q inferInstance inferInstance).mpr rfl
  have hgeq : g • e ∈ q := by
    by_contra h
    have hinv : g⁻¹ • q = q := (hsupp (g⁻¹ • q) inferInstance inferInstance).mp (by
      rw [Ideal.mem_inv_pointwise_smul_iff]
      exact h)
    have hgq : g • q = q := by
      calc
        g • q = g • (g⁻¹ • q) := congrArg (fun P : Ideal R => g • P) hinv.symm
        _ = q := smul_inv_smul g q
    apply hg
    change g ∈ MulAction.stabilizer G e
    rw [isolatingIdempotent_stabilizer_eq A R G hfinite q e he hsupp]
    exact hgq
  have hcut : e * (1 - g • e) = e := by
    obtain ⟨e₀, _, huniq⟩ :=
      existsUnique_idempotent_of_finite_integral_fiber A R hfinite q
    apply (huniq (e * (1 - g • e)) ?_).trans (huniq e ⟨he, hsupp⟩).symm
    refine ⟨he.mul (he.map (MulSemiringAction.toRingAut G R g)).one_sub, ?_⟩
    intro Q hQ hQm
    constructor
    · intro h
      exact (hsupp Q hQ hQm).mp (fun heQ => h (Q.mul_mem_right _ heQ))
    · intro h
      subst Q
      intro hprod
      rcases (inferInstance : q.IsPrime).mem_or_mem hprod with heQ | hcomp
      · exact heq heQ
      · have hone := q.add_mem hcomp hgeq
        rw [sub_add_cancel] at hone
        exact (Ideal.IsPrime.ne_top (inferInstance : q.IsPrime))
          ((Ideal.eq_top_iff_one q).mpr hone)
  rw [mul_sub, mul_one] at hcut
  exact sub_eq_self.mp hcut

/-- Every inertia-invariant element has the same selected-idempotent
projection as an element of the full base invariants. The idempotent and its
support are supplied by the actual Henselian integral-fiber construction;
finite fiber and orthogonality are derived here. -/
theorem exists_base_mul_eq_of_isolatingIdempotent
    [Finite G] [Algebra.IsInvariant A R G]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (q : Ideal R) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal A)]
    (e : R) (he : IsIdempotentElem e)
    (hsupp : ∀ Q : Ideal R, Q.IsPrime → Q.LiesOver (IsLocalRing.maximalIdeal A) →
      (e ∉ Q ↔ Q = q))
    (x : FixedPoints.subalgebra A R (q.inertia G)) :
    ∃ a : A, e * algebraMap A R a = e * (x : R) := by
  have hfinite : ((IsLocalRing.maximalIdeal A).primesOver R).Finite := by
    rw [← Algebra.IsInvariant.orbit_eq_primesOver A R G (IsLocalRing.maximalIdeal A) q]
    exact Set.finite_range (fun g : G => g • q)
  have hstab : MulAction.stabilizer G e = q.inertia G :=
    (isolatingIdempotent_stabilizer_eq A R G hfinite q e he hsupp).trans
      (inertia_eq_stabilizer_of_integral_of_residue_isSepClosed A R G q).symm
  obtain ⟨r, hr, her⟩ := exists_fixed_mul_eq_of_orthogonal_orbit e (e * (x : R))
    (by rw [← mul_assoc, he.eq]) (by
      intro g hg
      have hgI : g ∈ q.inertia G := by
        rw [← hstab]
        exact hg
      have hx : g • (x : R) = (x : R) := x.property ⟨g, hgI⟩
      rw [smul_mul', hg, hx])
    (isolatingIdempotent_mul_smul_eq_zero A R G hfinite q e he hsupp)
  obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) r hr
  refine ⟨a, ?_⟩
  rw [ha]
  exact her

end EtaleFundamentalGroups.Inertia
