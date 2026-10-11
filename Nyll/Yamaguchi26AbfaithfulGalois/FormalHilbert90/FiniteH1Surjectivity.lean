/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.FiniteCohomology
import Nyll.GaloisCohomology.Topology.ContinuousH1CocycleSurjectivity

/-! # Recovering actual H¹ surjectivity from finite cocycle lifts -/

namespace Yamaguchi26AbfaithfulGalois

universe u

/-- Lifting finite cocycles proves surjectivity of the actual H¹ reduction. -/
theorem h1_reduction_surjective_of_finiteCocycle_lifting
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (θ : Orientation ℓ G) (H : Subgroup G) (n : ℕ) (hn : 1 ≤ n)
    (hlift : ∀ c : FiniteCocycle θ H 1, ∃ d : FiniteCocycle θ H n,
      ∀ g : H, ZMod.castHom (pow_dvd_pow ℓ hn) (ZMod (ℓ ^ 1)) (d.toFun g) = c.toFun g) :
    HasH1ReductionSurjective θ H n hn := by
  apply ContinuousCohomology.map_surjective_of_crossedHom_lifting
    (finiteOrientationTopRep θ H n) (finiteOrientationTopRep θ H 1)
    (finiteOrientationReduction θ H n hn)
  intro c
  let c₀ : FiniteCocycle θ H 1 :=
    { toFun := fun g => (c.toFun g).down
      continuous_toFun := continuous_uliftDown.comp c.continuous_toFun
      cocycle := fun g h => congrArg ULift.down (c.map_mul g h) }
  obtain ⟨d, hd⟩ := hlift c₀
  let d' : ContinuousCohomology.CrossedHom (finiteOrientationTopRep θ H n) :=
    { toFun := fun g => ULift.up (d.toFun g)
      continuous_toFun := continuous_uliftUp.comp d.continuous_toFun
      map_mul := by
        intro g h
        rw [finiteOrientationTopRep_action]
        exact ULift.ext (d.cocycle g h) }
  exact ⟨d', fun g => ULift.ext (hd g)⟩

end Yamaguchi26AbfaithfulGalois
