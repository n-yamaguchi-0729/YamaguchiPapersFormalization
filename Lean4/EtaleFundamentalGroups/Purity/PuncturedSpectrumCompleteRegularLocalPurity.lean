/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.Local.RegularLocalGeneral
import EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedNormalizationFiberComparison
import EtaleFundamentalGroups.Purity.PuncturedSpectrumDimensionTwoPurity
import EtaleFundamentalGroups.Purity.PuncturedSpectrumParameterInduction
import SchemeTheory.LocalGeometry.RegularLocal.SystemDomain

/-!
# The complete regular-local hypersurface purity step

Grothendieck connectedness for the literal normalization fibre supplies the
connected-cover input in the categorical hypersurface induction theorem.
This file packages that passage as a reusable one-step purity theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

/-- Let x be a nonzero element of the maximal ideal of a complete regular
local domain of dimension at least three.  Purity for the hypersurface
quotient implies purity for the ambient ring.

The connectedness of the quotient puncture and of every normalization fibre
is produced internally by Grothendieck connectedness; callers only supply the
lower-dimensional purity statement. -/
theorem hasPuncturedPurity_of_complete_regularLocal_quotient_span_singleton
    {R : Type u} [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    [IsIntegrallyClosed R]
    [IsAdicComplete (maximalIdeal R) R]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim R)
    (x : R) (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0) :
    let I : Ideal R := Ideal.span {x}
    letI : Nontrivial (R ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
          ((maximalIdeal R).span_singleton_le_iff_mem.mpr hx))
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    AlgebraicGeometry.FiniteEtale.HasPuncturedPurity (R ⧸ I) →
      AlgebraicGeometry.FiniteEtale.HasPuncturedPurity R := by
  dsimp only
  let I : Ideal R := Ideal.span {x}
  have hI : I ≤ maximalIdeal R :=
    (maximalIdeal R).span_singleton_le_iff_mem.mpr hx
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI
  let : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  intro hquotient
  have hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R :=
    (by norm_num : (1 : WithBot ℕ∞) ≤ (3 : ℕ∞)).trans hdim
  have hconnectedR : ConnectedSpace
      (AlgebraicGeometry.Scheme.puncturedSpectrum R) := by
    let U := AlgebraicGeometry.Scheme.puncturedSpectrum R
    let j : U ⟶ AlgebraicGeometry.Spec (.of R) :=
      AlgebraicGeometry.Scheme.puncturedSpectrumInclusion R
    let : Nonempty U :=
      AlgebraicGeometry.Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim
        R hpos
    let : IsOpenImmersion j := by
      dsimp only [j, AlgebraicGeometry.Scheme.puncturedSpectrumInclusion]
      infer_instance
    let : IsIntegral U := isIntegral_of_isOpenImmersion j
    infer_instance
  have hconnectedQuotient : ConnectedSpace
      (AlgebraicGeometry.Scheme.puncturedSpectrum (R ⧸ I)) := by
    exact
      (open _root_.AlgebraicGeometry.FiniteEtale in
        connectedSpace_puncturedSpectrum_quotient_span_singleton_of_completeLocalDomain
          hdim x hx hx0)
  apply hasPuncturedPurity_of_complete_quotient_of_preserves_connected
    I hI hconnectedR hconnectedQuotient hquotient
  intro W hW
  let : IsConnected W := hW
  rw [AlgebraicGeometry.FiniteEtale.connectedPuncturedCoverQuotientRestriction_isConnected_iff
    R hpos W I hI]
  exact
    (open _root_.AlgebraicGeometry.FiniteEtale in
      connectedSpace_connectedPuncturedCoverNormalizationPuncturedFiber_span_singleton
        R hdim W x hx hx0)

/-- One-shot purity from an explicit regular system with two parameters left.

The quotient is taken once by `Ideal.ofList xs`; no normality hypothesis is
placed on that quotient or on any intermediate quotient.  Its regular-local
domain structure and its dimension two are consequences of the displayed
regular system. -/
theorem hasPuncturedPurity_of_complete_regularSystem_prefix_two
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    [IsAdicComplete (maximalIdeal R) R]
    (xs : List R) (y z : R)
    (hreg : RingTheory.Sequence.IsRegular R (xs ++ [y, z]))
    (hgen : Ideal.ofList (xs ++ [y, z]) = maximalIdeal R) :
    AlgebraicGeometry.FiniteEtale.HasPuncturedPurity R := by
  let : IsDomain R :=
    Kummer.isDomain_of_regularSystem (xs ++ [y, z]) hreg hgen
  let : IsRegularLocalRing R :=
    Kummer.isRegularLocalRing_of_regularSystem (xs ++ [y, z]) hreg hgen
  let I : Ideal R := Ideal.ofList xs
  let Q : Type u := R ⧸ I
  have hI : I ≤ maximalIdeal R := by
    calc
      I ≤ Ideal.ofList (xs ++ [y, z]) := by
        rw [Ideal.ofList_append]
        exact le_sup_left
      _ = maximalIdeal R := hgen
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing Q :=
    isNoetherianRing_of_surjective R Q (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hgeometry :
      IsDomain Q ∧ IsRegularLocalRing Q ∧
        ringKrullDim Q = ((2 : ℕ∞) : WithBot ℕ∞) := by
    simpa only [I, Q] using
      (Kummer.quotientPrefix_geometry_dimension_two_of_regularSystem
        xs y z hreg hgen)
  let : IsDomain Q := hgeometry.1
  let : IsRegularLocalRing Q := hgeometry.2.1
  have hdimQ : ringKrullDim Q = ((2 : ℕ∞) : WithBot ℕ∞) :=
    hgeometry.2.2
  have hdimEq :
      ((((xs.length + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) =
        ringKrullDim R) := by
    have hfullDim := Kummer.regularSystem_length_eq_ringKrullDim
      (xs ++ [y, z]) hreg hgen
    simpa using hfullDim
  have hdim :
      ((((xs.length + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
        ringKrullDim R) := hdimEq.le
  have hbase : (1 : WithBot ℕ∞) ≤
      (((xs.length + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    exact_mod_cast (by omega : 1 ≤ xs.length + 2)
  have hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R :=
    hbase.trans hdim
  have hconnectedR : ConnectedSpace
      (AlgebraicGeometry.Scheme.puncturedSpectrum R) := by
    let U := AlgebraicGeometry.Scheme.puncturedSpectrum R
    let j : U ⟶ AlgebraicGeometry.Spec (.of R) :=
      AlgebraicGeometry.Scheme.puncturedSpectrumInclusion R
    let : Nonempty U :=
      AlgebraicGeometry.Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim
        R hpos
    let : IsOpenImmersion j := by
      dsimp only [j, AlgebraicGeometry.Scheme.puncturedSpectrumInclusion]
      infer_instance
    let : IsIntegral U := isIntegral_of_isOpenImmersion j
    infer_instance
  have hconnectedQ : ConnectedSpace
      (AlgebraicGeometry.Scheme.puncturedSpectrum Q) := by
    let U := AlgebraicGeometry.Scheme.puncturedSpectrum Q
    let j : U ⟶ AlgebraicGeometry.Spec (.of Q) :=
      AlgebraicGeometry.Scheme.puncturedSpectrumInclusion Q
    have hposQ : (1 : WithBot ℕ∞) ≤ ringKrullDim Q := by
      rw [hdimQ]
      norm_num
    let : Nonempty U :=
      AlgebraicGeometry.Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim
        Q hposQ
    let : IsOpenImmersion j := by
      dsimp only [j, AlgebraicGeometry.Scheme.puncturedSpectrumInclusion]
      infer_instance
    let : IsIntegral U := isIntegral_of_isOpenImmersion j
    infer_instance
  have hpurityQ :
      AlgebraicGeometry.FiniteEtale.HasPuncturedPurity Q :=
    AlgebraicGeometry.FiniteEtale.hasPuncturedPurity_of_isRegularLocalRing_dimension_two
      Q hdimQ
  apply hasPuncturedPurity_of_complete_quotient_of_preserves_connected
    I hI hconnectedR hconnectedQ hpurityQ
  intro W hW
  let : IsConnected W := hW
  rw [AlgebraicGeometry.FiniteEtale.connectedPuncturedCoverQuotientRestriction_isConnected_iff
    R hpos W I hI]
  exact
    (open _root_.AlgebraicGeometry.FiniteEtale in
      connectedSpace_connectedPuncturedCoverNormalizationPuncturedFiber_ofList
        R xs hI hdim W)

/-- A complete normal local ring with an explicit regular system of length at
least two has punctured purity.  The last two parameters provide the
dimension-two quotient used by
`hasPuncturedPurity_of_complete_regularSystem_prefix_two`. -/
theorem hasPuncturedPurity_of_complete_regularSystem_of_two_le_length
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    [IsAdicComplete (maximalIdeal R) R]
    (ps : List R) (hreg : RingTheory.Sequence.IsRegular R ps)
    (hgen : Ideal.ofList ps = maximalIdeal R)
    (hlen : 2 ≤ ps.length) :
    AlgebraicGeometry.FiniteEtale.HasPuncturedPurity R := by
  obtain ⟨xs, y, z, rfl⟩ : ∃ (xs : List R) (y z : R),
      ps = xs ++ [y, z] := by
    induction ps using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton l z =>
        induction l using List.reverseRecOn with
        | nil => simp at hlen
        | append_singleton xs y =>
            exact ⟨xs, y, z, by simp⟩
  exact hasPuncturedPurity_of_complete_regularSystem_prefix_two
    xs y z hreg hgen

end EtaleFundamentalGroups

end
