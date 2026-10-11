/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedRegularSystem
import Nyll.EtaleFundamentalGroups.LocalGeometry.RegularPair.IntegrallyClosed

/-!
# Normality of two-dimensional iterated radical covers

A positive iterated radical cover of a two-dimensional regular parameter
pair again has an explicit regular parameter pair generating its maximal
ideal.  The dimension-two conductor criterion therefore shows directly that
the cover is integrally closed.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing
open RingTheory.Sequence

universe u

private theorem exists_pair_of_length_eq_two {R : Type u} (xs : List R)
    (hxs : xs.length = 2) :
    ∃ x y : R, xs = [x, y] := by
  rcases xs with _ | ⟨x, xs⟩
  · simp at hxs
  rcases xs with _ | ⟨y, xs⟩
  · simp at hxs
  rcases xs with _ | ⟨z, xs⟩
  · exact ⟨x, y, rfl⟩
  · simp at hxs

/--
The full positive iterated radical cover of a two-dimensional regular
parameter pair is integrally closed.
-/
theorem isIntegrallyClosed_iteratedRadical_of_regular_pair
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (n : Fin 2 → ℕ) (a : Fin 2 → A)
    (hn : ∀ i, 0 < n i)
    (hreg : IsRegular A (List.ofFn a))
    (hgen : Ideal.ofList (List.ofFn a) = maximalIdeal A) :
    IsIntegrallyClosed (iteratedRadical A 2 n a) := by
  let B := iteratedRadical A 2 n a
  let bs := iteratedLocalRootCoverParameterList A n a []
  have ha : ∀ i, a i ∈ maximalIdeal A := by
    intro i
    rw [← hgen]
    have hai : a i ∈ List.ofFn a := List.mem_ofFn.mpr ⟨i, rfl⟩
    exact Ideal.subset_span hai
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  obtain ⟨hNoetherian, hDomain, _, hregB, hgenB, _, _⟩ :=
    iteratedRadical_regularSystem_geometry n a [] hn (by simpa using hreg)
      (by simpa using hgen)
  let : IsNoetherianRing B := hNoetherian
  let : IsDomain B := hDomain
  have hlen : bs.length = 2 := by
    simp [bs]
  obtain ⟨x, y, hbs⟩ := exists_pair_of_length_eq_two bs hlen
  apply SpecialLocalPurity.isIntegrallyClosed_of_isRegular_pair_of_span_eq_maximalIdeal
    B x y
  · simpa [bs, hbs] using hregB
  · simpa [bs, hbs] using hgenB

end EtaleFundamentalGroups.Kummer

end
