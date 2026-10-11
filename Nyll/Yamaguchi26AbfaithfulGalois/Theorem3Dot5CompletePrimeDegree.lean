/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.CompletePrimeOrderDetection
import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.ModPrimeCohomologyDetection

/-! # Proposition 3.5: nontrivial mod-p cohomology action

Source: [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1), Proposition 3.5.
-/

namespace Yamaguchi26AbfaithfulGalois
open KummerTheory ValuationTheory.DiscreteValuationField
universe u v

theorem complete_prime_degree_cohomology_3_5
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [CharZero K] (base : CompleteDVF.{u, v} K)
    (p r : ℕ) [Fact p.Prime] [Fact r.Prime] [CharP base.residueField p]
    (hdegree : Module.finrank K L = r) :
    ∃ τ : Gal(L/K), relativeGaloisH1Action (n := p) K L τ ≠ 1 := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨τ, _, z, hz⟩ := prime_order_detection base p r hdegree
  exact ⟨τ⁻¹, inverse_relativeH1Action_ne_one_of_moved_abelianModPower K L p τ z hz⟩

end Yamaguchi26AbfaithfulGalois
