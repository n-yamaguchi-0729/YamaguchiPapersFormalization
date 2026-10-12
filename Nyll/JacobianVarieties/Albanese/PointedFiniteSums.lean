/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Albanese.FiniteSums
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Hilbert.SymmetricPowerData
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn

/-!
# Stabilization of pointed finite sums

Adjoining the rational basepoint defines an actual morphism between successive finite
fibre powers. A morphism sending that basepoint to the identity has the same finite sum
before and after this insertion. This works over any field and needs no commutativity.

This is degree stabilization, not invariance under principal divisors. It asserts neither
an arbitrary-target Albanese factorization nor the existence of a symmetric-power quotient.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry.finFibrePow

/-- Adjoin the given rational basepoint as the first coordinate of a finite fibre power. -/
def insertBasepoint {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) (n : ℕ) :
    SchemeHomOver (toBase c n) (toBase c (n + 1)) :=
  let t : finFibrePow c n ⟶ Spec (CommRingCat.of K) := toBase c n
  let e : SchemeHomOver t c :=
    NeronModelInfra.schemeHomOverComp ⟨t, Category.comp_id t⟩ ε
  let xs : Fin (n + 1) → SchemeHomOver t c :=
    Fin.cons e (fun i => ⟨proj c n i, proj_comp c n i⟩)
  ⟨WidePullback.lift t (fun i => (xs i).1) (fun i => (xs i).2),
    WidePullback.lift_base _ _ _ _⟩

end AlgebraicGeometry.finFibrePow

namespace GoodReductionJacobian.RelativeGroupLaw

/-- A pointed morphism has the same finite sum after adjoining the rational basepoint. -/
theorem finiteSumMap_insertBasepoint {K : Type u} [Field K] {B C : Scheme.{u}}
    {b : B ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K b)
    (c : C ⟶ Spec (CommRingCat.of K))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) (q : SchemeHomOver c b)
    (hq : NeronModelInfra.schemeHomOverComp ε q = G.one (𝟙 (Spec (CommRingCat.of K))))
    (n : ℕ) :
    NeronModelInfra.schemeHomOverComp (finFibrePow.insertBasepoint c ε n)
        (G.finiteSumMap c q (n + 1)) = G.finiteSumMap c q n := by
  let t : finFibrePow c n ⟶ Spec (CommRingCat.of K) := finFibrePow.toBase c n
  let e : SchemeHomOver t c :=
    NeronModelInfra.schemeHomOverComp ⟨t, Category.comp_id t⟩ ε
  let xs : Fin (n + 1) → SchemeHomOver t c :=
    Fin.cons e (fun i => ⟨finFibrePow.proj c n i, finFibrePow.proj_comp c n i⟩)
  have he : NeronModelInfra.schemeHomOverComp e q = G.one t := by
    change NeronModelInfra.schemeHomOverComp
      (NeronModelInfra.schemeHomOverComp ⟨t, Category.comp_id t⟩ ε) q = G.one t
    rw [NeronModelInfra.schemeHomOverComp_assoc, hq]
    exact G.one_natural (𝟙 (Spec (CommRingCat.of K))) t t (Category.comp_id t)
  have h := G.finiteSumMap_evaluate c q t xs
  rw [List.ofFn_succ, G.sumList_cons] at h
  change GoodReductionJacobian.schemeHomOverComp
      (WidePullback.lift t (fun i => (xs i).1) (fun i => (xs i).2))
      (WidePullback.lift_base _ _ _ _) (G.finiteSumMap c q (n + 1)) =
    G.mul t (NeronModelInfra.schemeHomOverComp e q) (G.finiteSumMap c q n) at h
  rw [he, G.one_mul] at h
  exact h

end GoodReductionJacobian.RelativeGroupLaw
