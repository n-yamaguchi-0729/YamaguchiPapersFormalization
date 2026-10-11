/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import ValuedFieldTheory.Valuation.Completion.DiscreteValuedCompletion
import ValuedFieldTheory.Valuation.Completion.DiscreteRingEquiv
import GaloisCohomology.Topology.AbsoluteGaloisAbelianModPower
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Topology.Instances.ZMod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ProCGroups.Abelian.AbelianModPower
import ProCGroups.Abelian.PrimeExponentCharacters
import ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology
import Mathlib.FieldTheory.Galois.Profinite
import GaloisCohomology.Kummer.Concrete.PowerClassCharacterApproximation
import GaloisCohomology.Kummer.Concrete.CyclotomicCompletionApproximation
import ValuedFieldTheory.Valuation.Completion.PowerClasses
import ValuedFieldTheory.Valuation.Completion.ArtinSchreierClasses
import GaloisCohomology.ArtinSchreier.FieldMapApproximation

/-!
# Weak approximation for characters

The stronger simultaneous character-approximation theorem retained from the earlier manuscript.
The restriction of a character uses mathlib's actual continuous absolute
Galois-group map attached to the canonical embedding into a completion.
The product map on maximal exponent-`q` abelian quotients is formed from
mathlib's absolute Galois-group maps and topological abelianization maps.
-/

namespace Yamaguchi26AbfaithfulGalois

open ValuationTheory.DiscreteValuationField ProCGroups.Abelian
open Field.absoluteGaloisGroup

universe u v

/-- Restrict a continuous `ZMod q`-character along the actual completion
embedding. The algebraic-closure lift chosen by `absoluteGaloisGroup.map`
does not affect characters with abelian target. -/
noncomputable def completionCharacterRestriction
    {K : Type u} [Field K] (D : DVF.{u, v} K) (q : ℕ) :
    (Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod q)) →
      (Gal(AlgebraicClosure D.valuation.Completion/D.valuation.Completion) →ₜ*
        Multiplicative (ZMod q)) :=
  fun χ => χ.comp
    (Field.absoluteGaloisGroup.map (algebraMap K D.valuation.Completion))

/-- The natural map from the product of local exponent-`q` abelianizations
to the global one, induced by all completion embeddings. -/
noncomputable def completionAbelianModPowerMap
    {K : Type u} [Field K] (r : ℕ)
    (D : Fin r → DVF.{u, v} K) (q : ℕ) :
    ((i : Fin r) →
      abelianModPower
        Gal(AlgebraicClosure ((D i).valuation.Completion)/((D i).valuation.Completion)) q) →ₜ*
      abelianModPower Gal(AlgebraicClosure K/K) q :=
  let f : ∀ i : Fin r,
      abelianModPower
        Gal(AlgebraicClosure ((D i).valuation.Completion)/((D i).valuation.Completion)) q →ₜ*
        abelianModPower Gal(AlgebraicClosure K/K) q :=
    fun i => abelianModPowerMap q
      ((Field.absoluteGaloisGroup.map
        (algebraMap K ((D i).valuation.Completion))) :
        Gal(AlgebraicClosure ((D i).valuation.Completion)/
          ((D i).valuation.Completion)) →ₜ* Gal(AlgebraicClosure K/K))
  { toMonoidHom :=
      { toFun := fun g => ∏ i : Fin r, f i (g i)
        map_one' := by
          change (∏ i : Fin r, f i 1) = 1
          simp only [map_one, Finset.prod_const_one]
        map_mul' := by
          intro x y
          change (∏ i : Fin r, f i (x i * y i)) =
            (∏ i : Fin r, f i (x i)) * ∏ i : Fin r, f i (y i)
          simp only [map_mul, Finset.prod_mul_distrib] }
    continuous_toFun := by
      classical
      apply continuous_finsetProd
      intro i _
      exact (f i).continuous.comp (continuous_apply i) }

/-- The actual completion restriction and product maps are equivariant under
automorphisms that permute the valuation classes. The induced completion
isomorphisms extend the prescribed automorphism of the original field. -/
theorem completionMapsEquivariant
    {K : Type u} [Field K] (r : ℕ) (D : Fin r → DVF.{u, v} K) (q : ℕ) :
    ∀ (σ : K ≃+* K) (π : Equiv.Perm (Fin r)),
        (∀ i : Fin r,
          (D i).valuation.IsEquiv
            ((D (π i)).valuation.comap σ.toRingHom)) →
        ∃ e : ∀ i : Fin r,
            (D i).valuation.Completion ≃+* (D (π i)).valuation.Completion,
          (∀ (i : Fin r) (x : K),
            e i (algebraMap K ((D i).valuation.Completion) x) =
              algebraMap K ((D (π i)).valuation.Completion) (σ x)) ∧
          (∀ (χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod q))
            (i : Fin r),
            completionCharacterRestriction (D (π i)) q
                (χ.comp (Field.absoluteGaloisGroup.map σ.toRingHom)) =
              (completionCharacterRestriction (D i) q χ).comp
                (Field.absoluteGaloisGroup.map (e i).toRingHom)) ∧
          (∀ g : (j : Fin r) →
              abelianModPower
                Gal(AlgebraicClosure ((D j).valuation.Completion)/
                  ((D j).valuation.Completion)) q,
            abelianModPowerMap q (Field.absoluteGaloisGroup.map σ.toRingHom)
                (completionAbelianModPowerMap r D q g) =
              completionAbelianModPowerMap r D q
                (fun i : Fin r =>
                  abelianModPowerMap q
                    (Field.absoluteGaloisGroup.map (e i).toRingHom)
                    (g (π i)))) := by
  intro σ π hσ
  let e := fun i => DVF.completionRingEquiv (D i) (D (π i)) σ (hσ i)
  have he (i : Fin r) :
      (algebraMap K ((D (π i)).valuation.Completion)).comp σ.toRingHom =
        (e i).toRingHom.comp (algebraMap K ((D i).valuation.Completion)) := by
    ext x
    exact (DVF.completionRingEquiv_algebraMap (D i) (D (π i)) σ (hσ i) x).symm
  refine ⟨e, ?_, ?_, ?_⟩
  · intro i x
    exact DVF.completionRingEquiv_algebraMap (D i) (D (π i)) σ (hσ i) x
  · intro χ i
    unfold completionCharacterRestriction
    calc
      _ = χ.comp (map ((algebraMap K ((D (π i)).valuation.Completion)).comp
          σ.toRingHom)) := (character_map_comp σ.toRingHom
            (algebraMap K ((D (π i)).valuation.Completion)) χ).symm
      _ = χ.comp (map ((e i).toRingHom.comp
          (algebraMap K ((D i).valuation.Completion)))) :=
        congrArg (fun f => χ.comp (map f)) (he i)
      _ = _ := character_map_comp (algebraMap K ((D i).valuation.Completion))
        (e i).toRingHom χ
  · intro g
    change abelianModPowerMap q (map σ.toRingHom)
      (∏ j, abelianModPowerMap q (map (algebraMap K ((D j).valuation.Completion))) (g j)) =
        ∏ i, abelianModPowerMap q (map (algebraMap K ((D i).valuation.Completion)))
          (abelianModPowerMap q (map (e i).toRingHom) (g (π i)))
    rw [map_prod]
    calc
      _ = ∏ i, abelianModPowerMap q (map σ.toRingHom)
          (abelianModPowerMap q (map (algebraMap K ((D (π i)).valuation.Completion)))
            (g (π i))) := (Equiv.prod_comp π _).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        have hh := congrArg (fun h => h (g (π i)))
          ((abelianModPowerMap_map_comp q σ.toRingHom
            (algebraMap K ((D (π i)).valuation.Completion))).symm)
        rw [he i, abelianModPowerMap_map_comp] at hh
        exact hh


/-- Simultaneous extension of completion characters implies injectivity of the
actual product map on abelianizations modulo the prime. -/
theorem completionAbelianModPowerMap_injective_of_character_surjective
    {K : Type u} [Field K] (r : ℕ) (D : Fin r → DVF.{u, v} K)
    (q : ℕ) [Fact q.Prime]
    (hchar : Function.Surjective
      (fun (χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod q))
        (i : Fin r) => completionCharacterRestriction (D i) q χ)) :
    Function.Injective (completionAbelianModPowerMap r D q) := by
  let H := fun i : Fin r =>
    Gal(AlgebraicClosure ((D i).valuation.Completion)/((D i).valuation.Completion))
  have (i : Fin r) : CompactSpace (H i) :=
    (ValuationTheory.Completion.separableClosureAutContinuousEquiv
      ((D i).valuation.Completion)).symm.toHomeomorph.compactSpace
  exact injective_prod_abelianModPowerMap_of_character_surjective H
    (fun i => Field.absoluteGaloisGroup.map
      (algebraMap K ((D i).valuation.Completion))) hchar


/-- If the field contains the relevant roots of unity and the exponent is nonzero,
Kummer theory and weak approximation prescribe all completion characters. -/
theorem completionCharacterRestriction_surjective_of_primitiveRoots
    {K : Type u} [Field K] (r : ℕ) (D : Fin r → DVF.{u, v} K)
    (hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation))
    (n : ℕ+) [NeZero ((n : ℕ) : K)]
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Function.Surjective (fun χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod (n : ℕ)) =>
      fun i => completionCharacterRestriction (D i) (n : ℕ) χ) := by
  let C (i : Fin r) := (D i).valuation.Completion
  let _ : ∀ i, Field (C i) := fun i => inferInstanceAs (Field ((D i).valuation.Completion))
  let f (i : Fin r) : K →+* C i := algebraMap K ((D i).valuation.Completion)
  have hpower : Function.Surjective (fun (a : Kˣ) (i : Fin r) =>
      (Units.map (f i).toMonoidHom a :
        (C i)ˣ ⧸ (powMonoidHom (n : ℕ) : (C i)ˣ →* (C i)ˣ).range)) :=
    DVF.surjective_pi_completion_powerClasses D hD (n : ℕ)
      (NeZero.ne ((n : ℕ) : K))
  exact ClassFieldTower.Martinet.Shafarevich.surjective_characters_of_powerClasses
    C f n hmu hpower


private theorem completionCharacterRestriction_surjective_of_charP
    {K : Type u} [Field K] (r : ℕ) (D : Fin r → DVF.{u, v} K)
    (hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation))
    (q : ℕ) [Fact q.Prime] [CharP K q] :
    Function.Surjective (fun χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod q) =>
      fun i => completionCharacterRestriction (D i) q χ) := by
  let C (i : Fin r) := (D i).valuation.Completion
  let _ : ∀ i, Field (C i) := fun i => inferInstanceAs (Field ((D i).valuation.Completion))
  let f (i : Fin r) : K →+* C i := algebraMap K ((D i).valuation.Completion)
  have (i : Fin r) : CharP (C i) q := charP_of_injective_ringHom (f i).injective q
  have hclasses : Function.Surjective (fun (a : K) (i : Fin r) =>
      (f i a : C i ⧸ ((frobenius (C i) q).toAddMonoidHom - AddMonoidHom.id (C i)).range)) :=
    DVF.surjective_pi_completion_artinSchreierClasses D hD q
  exact ClassFieldTower.Martinet.Shafarevich.surjective_characters_of_artinSchreierClasses
    C q f hclasses


/-- Simultaneous character approximation: characters can be prescribed at every
member of a finite family of inequivalent nontrivial discrete valuations.
The second conjunct is the natural product map's injectivity. The third conjunct states
equivariance of both maps for field automorphisms permuting the valuations; the completion
equivalences are required to extend the automorphism and are produced in the
conclusion. -/
theorem weakApproximationForCharacters
    {K : Type u} [Field K] (r : ℕ) (D : Fin r → DVF.{u, v} K)
    (hD : Pairwise (fun i j : Fin r =>
      ¬ (D i).valuation.IsEquiv (D j).valuation))
    (q : ℕ) [Fact q.Prime] :
    Function.Surjective
      (fun (χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod q))
        (i : Fin r) => completionCharacterRestriction (D i) q χ) ∧
      Function.Injective (completionAbelianModPowerMap r D q) ∧
      (∀ (σ : K ≃+* K) (π : Equiv.Perm (Fin r)),
        (∀ i : Fin r,
          (D i).valuation.IsEquiv
            ((D (π i)).valuation.comap σ.toRingHom)) →
        ∃ e : ∀ i : Fin r,
            (D i).valuation.Completion ≃+* (D (π i)).valuation.Completion,
          (∀ (i : Fin r) (x : K),
            e i (algebraMap K ((D i).valuation.Completion) x) =
              algebraMap K ((D (π i)).valuation.Completion) (σ x)) ∧
          (∀ (χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod q))
            (i : Fin r),
            completionCharacterRestriction (D (π i)) q
                (χ.comp (Field.absoluteGaloisGroup.map σ.toRingHom)) =
              (completionCharacterRestriction (D i) q χ).comp
                (Field.absoluteGaloisGroup.map (e i).toRingHom)) ∧
          (∀ g : (j : Fin r) →
              abelianModPower
                Gal(AlgebraicClosure ((D j).valuation.Completion)/
                  ((D j).valuation.Completion)) q,
            abelianModPowerMap q (Field.absoluteGaloisGroup.map σ.toRingHom)
                (completionAbelianModPowerMap r D q g) =
              completionAbelianModPowerMap r D q
                (fun i : Fin r =>
                  abelianModPowerMap q
                    (Field.absoluteGaloisGroup.map (e i).toRingHom)
                    (g (π i))))) := by
  suffices hchar : Function.Surjective
      (fun (χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod q))
        (i : Fin r) => completionCharacterRestriction (D i) q χ) by
    exact ⟨hchar, completionAbelianModPowerMap_injective_of_character_surjective
      r D q hchar, completionMapsEquivariant r D q⟩
  by_cases hq : (q : K) ≠ 0
  · have : NeZero (q : K) := ⟨hq⟩
    exact KummerTheory.surjective_completion_characters_of_ne_char D hD q
  · have : CharP K q :=
      (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr (not_ne_iff.mp hq)
    exact completionCharacterRestriction_surjective_of_charP r D hD q

end Yamaguchi26AbfaithfulGalois
