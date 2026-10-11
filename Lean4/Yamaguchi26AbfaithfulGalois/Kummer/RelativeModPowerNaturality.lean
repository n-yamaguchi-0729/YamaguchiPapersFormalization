/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Yamaguchi26AbfaithfulGalois.Kummer.RelativeAbelianModPowerAction
import GaloisCohomology.Kummer.Concrete.AbsoluteRestrictionConjugation
import GaloisCohomology.Topology.AbsoluteGaloisMap

/-!
# Naturality of relative actions on abelianization modulo powers

An embedding intertwining two relative automorphisms intertwines their actions
on the actual absolute Galois abelianizations, independently of closure lifts.
-/

namespace Yamaguchi26AbfaithfulGalois
open KummerTheory ProCGroups.Abelian
open Field.absoluteGaloisGroup
universe u
variable {K L F E : Type u} [Field K] [Field L] [Field F] [Field E]
  [Algebra K L] [Algebra F E]

/-- Intertwined relative field automorphisms induce intertwined maps on the
absolute Galois abelianizations modulo any power. -/
theorem relativeGaloisAbelianModPowerTransform_naturality
    (q : ℕ) (f : L →+* E) (τ : Gal(L/K)) (σ : Gal(E/F))
    (hcompat : ∀ x : L, σ (f x) = f (τ x))
    (z : abelianModPower Gal(AlgebraicClosure E/E) q) :
    abelianModPowerMap q (map f)
        (relativeGaloisAbelianModPowerTransform F E q σ z) =
      relativeGaloisAbelianModPowerTransform K L q τ
        (abelianModPowerMap q (map f) z) := by
  have heq : f.comp τ.symm.toRingEquiv.toRingHom =
      σ.symm.toRingEquiv.toRingHom.comp f := by
    ext x
    apply σ.injective
    exact (hcompat (τ.symm x)).trans
      ((congrArg f (τ.apply_symm_apply x)).trans (σ.apply_symm_apply (f x)).symm)
  obtain ⟨a, rfl⟩ := abelianModPowerMk_surjective (G := Gal(AlgebraicClosure E/E)) q z
  let χ : Gal(AlgebraicClosure L/L) →ₜ* abelianModPower Gal(AlgebraicClosure L/L) q :=
    abelianModPowerMk _ q
  change χ (map f (absoluteGaloisConjugate σ.toRingEquiv a)) =
    χ (absoluteGaloisConjugate τ.toRingEquiv (map f a))
  have hσ := character_map_symm_eq_absoluteGaloisConjugate σ.toRingEquiv
    (χ.comp (map f)) a
  have hτ := character_map_symm_eq_absoluteGaloisConjugate τ.toRingEquiv χ (map f a)
  exact hσ.symm.trans ((DFunLike.congr_fun (character_map_comp f
    σ.symm.toRingEquiv.toRingHom χ) a).symm.trans
    ((congrArg (fun h : L →+* E => χ (map h a)) heq.symm).trans
      ((DFunLike.congr_fun (character_map_comp τ.symm.toRingEquiv.toRingHom f χ) a).trans hτ)))
end Yamaguchi26AbfaithfulGalois
