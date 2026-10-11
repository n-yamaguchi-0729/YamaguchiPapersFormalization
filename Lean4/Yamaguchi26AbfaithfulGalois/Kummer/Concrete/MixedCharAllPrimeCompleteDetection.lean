/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharCompleteDetection
import Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharPrimeToCompleteDetection

/-!
# Faithful p-power cohomology for every prime extension degree

The residue prime controls the coefficients. The Galois extension degree
can be any prime: residue-prime degree uses wild detection, while a different
prime degree is already detected at the first p-power level.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory ValuationTheory.DiscreteValuationField

/-- Every prime-degree Galois extension of a complete mixed-characteristic
DVF has faithful action on its absolute H¹ at some positive p-power level.
The extension degree and the residue prime need not agree. -/
theorem exists_faithful_relativeH1Action_of_complete_mixedChar_prime_order
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsGalois F K] [CharZero F]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete vF]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField vF.valuationSubring) p]
    {r : ℕ} [Fact r.Prime] (hdegree : Module.finrank F K = r) :
    ∃ s : ℕ, 1 ≤ s ∧ Function.Injective (relativeGaloisH1Action (n := p ^ s) F K) := by
  by_cases hrp : r = p
  · exact exists_faithful_relativeH1Action_of_complete_mixedChar_prime_degree
      vF p (hdegree.trans hrp)
  · refine ⟨1, le_rfl, ?_⟩
    exact (congrArg
      (fun n : ℕ => Function.Injective (relativeGaloisH1Action (n := n) F K))
      (pow_one p)).mpr
        (faithful_relativeH1Action_of_complete_mixedChar_primeTo_degree vF p r hrp hdegree)

end ClassFieldTower.Martinet.Shafarevich
