/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Theorem6Dot1FormalHilbert90
import GaloisCohomology.Topology.ContinuousH1Lifting
import GaloisCohomology.ProfiniteIntegers.PadicInverseLimit

/-! # Concrete finite cocycles and the actual continuous H¹ reduction -/

namespace Yamaguchi26AbfaithfulGalois

universe u

variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private def finiteCocycleCrossedHom (θ : Orientation ℓ G) (H : Subgroup G)
    (n : ℕ) (c : FiniteCocycle θ H n) :
    ContinuousCohomology.CrossedHom (finiteOrientationTopRep θ H n) where
  toFun := fun g => ULift.up (c.toFun g)
  continuous_toFun := continuous_uliftUp.comp c.continuous_toFun
  map_mul := by
    intro g h
    rw [finiteOrientationTopRep_action]
    exact ULift.ext (c.cocycle g h)

/-- Surjectivity on the genuine H¹ map gives exact lifts of finite cocycles
modulo ℓ; the lifted cohomology class is corrected by a principal cocycle. -/
theorem finiteCocycle_lift_mod_one_of_h1
    (θ : Orientation ℓ G) (H : Subgroup G)
    (n : ℕ) (hn : 1 ≤ n) (hH : HasH1ReductionSurjective θ H n hn)
    (c : FiniteCocycle θ H 1) :
    ∃ d : FiniteCocycle θ H n, ∀ x : H,
      ZMod.castHom (pow_dvd_pow ℓ hn) (ZMod (ℓ ^ 1)) (d.toFun x) = c.toFun x := by
  have hf : Function.Surjective (finiteOrientationReduction θ H n hn).hom := by
    intro a
    refine ⟨ULift.up (a.down.val : ZMod (ℓ ^ n)), ?_⟩
    apply ULift.ext
    change ZMod.castHom (pow_dvd_pow ℓ hn) (ZMod (ℓ ^ 1))
      (a.down.val : ZMod (ℓ ^ n)) = a.down
    rw [map_natCast, ZMod.natCast_zmod_val]
  have horbit (a : finiteOrientationTopRep θ H n) :
      Continuous (fun g : H => (finiteOrientationTopRep θ H n).ρ g a) := by
    change Continuous (fun g : H => ULift.up
      (PadicInt.toZModPow n (θ (g : G) : PadicInt ℓ) * a.down))
    apply continuous_uliftUp.comp
    exact ((PadicInt.continuous_toZModPow n).comp
      (Units.continuous_val.comp (θ.continuous.comp continuous_subtype_val))).mul continuous_const
  obtain ⟨d, hd⟩ := ContinuousCohomology.exists_crossedHom_lift_of_map_surjective
    (finiteOrientationTopRep θ H n) (finiteOrientationTopRep θ H 1)
    (finiteOrientationReduction θ H n hn) hf horbit hH
    (finiteCocycleCrossedHom θ H 1 c)
  refine ⟨⟨fun x => (d.toFun x).down,
    continuous_uliftDown.comp d.continuous_toFun, ?_⟩, ?_⟩
  · intro x y
    have hc := congrArg ULift.down (d.map_mul x y)
    exact hc
  · intro x
    exact congrArg ULift.down (hd x)

end Yamaguchi26AbfaithfulGalois
