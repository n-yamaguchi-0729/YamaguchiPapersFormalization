/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedHeightOne

/-!
# A simultaneous target action for an iterated radical

An action of an iterated diagonal radical on a target algebra is determined
by a compatible target root for every stage.  This file packages the
successive applications of `AdjoinRoot.liftAlgHom` and records all root
coordinates in the final map.

The power equations are explicit data.  In applications they must be
produced by the relevant component or factor construction; this file does
not assert that such roots exist in an arbitrary target.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u v

/-- A compatible family of roots in an `A`-algebra defines an `A`-algebra
map from the corresponding iterated radical. -/
def iteratedRadicalTargetAlgHom
    {A : Type u} {S : Type v} [CommRing A] [CommRing S] [Algebra A S] :
    {r : ℕ} → (n : Fin r → ℕ) → (a : Fin r → A) →
      (x : Fin r → S) →
      (∀ i, x i ^ n i = algebraMap A S (a i)) →
      iteratedRadical A r n a →ₐ[A] S
  | 0, _, _, _, _ => Algebra.ofId A S
  | r + 1, n, a, x, hx => by
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) -
          C (algebraMap A T (a (Fin.last r)))
      let prefixMap : T →ₐ[A] S :=
        iteratedRadicalTargetAlgHom
          (Fin.init n) (Fin.init a) (Fin.init x)
          (fun i ↦ hx i.castSucc)
      have hroot : f.eval₂ prefixMap (x (Fin.last r)) = 0 := by
        simp only [f, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
        rw [hx (Fin.last r)]
        exact sub_eq_zero.mpr (prefixMap.commutes _).symm
      exact AdjoinRoot.liftAlgHom f prefixMap (x (Fin.last r)) hroot

/-- The simultaneous target action sends every distinguished iterated root
to the corresponding supplied target root. -/
@[simp]
theorem iteratedRadicalTargetAlgHom_apply_root
    {A : Type u} {S : Type v} [CommRing A] [CommRing S] [Algebra A S]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (x : Fin r → S)
    (hx : ∀ i, x i ^ n i = algebraMap A S (a i))
    (i : Fin r) :
    iteratedRadicalTargetAlgHom n a x hx
        (iteratedRadicalRoot A n a i) = x i := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp only [iteratedRadicalRoot_last,
          iteratedRadicalTargetAlgHom]
        exact AdjoinRoot.liftAlgHom_root _ _ _ _
      · simp only [iteratedRadicalRoot_castSucc,
          iteratedRadicalTargetAlgHom]
        calc
          _ = iteratedRadicalTargetAlgHom
                (Fin.init n) (Fin.init a) (Fin.init x)
                (fun k ↦ hx k.castSucc)
                (iteratedRadicalRoot A (Fin.init n) (Fin.init a) j) :=
              AdjoinRoot.liftAlgHom_of _ _ _ _ _
          _ = x j.castSucc :=
              ih (Fin.init n) (Fin.init a) (Fin.init x)
                (fun k ↦ hx k.castSucc) j

/-- If the iterated radical is a domain and the original base acts
faithfully on the target, the simultaneous target action is injective.

Integrality of the full iterated radical is produced from the positive
exponents.  Thus injectivity is not an additional map-shaped input for the
fraction-field tower constructed from this action. -/
theorem iteratedRadicalTargetAlgHom_injective
    {A : Type u} {S : Type v}
    [CommRing A] [Nontrivial A] [CommRing S] [Algebra A S]
    [FaithfulSMul A S]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    [IsDomain (iteratedRadical A r n a)]
    (x : Fin r → S)
    (hx : ∀ i, x i ^ n i = algebraMap A S (a i)) :
    Function.Injective (iteratedRadicalTargetAlgHom n a x hx) := by
  let D := iteratedRadical A r n a
  let ρ : D →ₐ[A] S := iteratedRadicalTargetAlgHom n a x hx
  let : Module.Finite A D := finite_iteratedRadical n a hn
  let : Algebra.IsIntegral A D := Algebra.IsIntegral.of_finite A D
  apply (RingHom.injective_iff_ker_eq_bot ρ.toRingHom).2
  apply Ideal.eq_bot_of_under_eq_bot (R := A)
  rw [Ideal.under_def, RingHom.comap_ker]
  have hcomp : ρ.toRingHom.comp (algebraMap A D) = algebraMap A S := by
    ext z
    exact ρ.commutes z
  rw [hcomp]
  exact (RingHom.injective_iff_ker_eq_bot (algebraMap A S)).1
    (FaithfulSMul.algebraMap_injective A S)

end EtaleFundamentalGroups.Kummer

end
