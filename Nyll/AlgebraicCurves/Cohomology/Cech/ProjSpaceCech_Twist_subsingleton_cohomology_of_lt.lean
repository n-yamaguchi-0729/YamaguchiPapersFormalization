/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist

/-!
# Proj Space Cech Twist subsingleton cohomology of lt
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.ProjectiveTwistSubsingleton

universe u

noncomputable section

open Finset Function

namespace ProjSpaceCech
open _root_.ProjSpaceCech
open _root_.ProjSpaceCech

section Cohomology

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

namespace Twist
open _root_.ProjSpaceCech.Twist
end Twist
open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.subsingleton_cohomology_of_lt {i : ℕ} (hi : n < i) :
    Subsingleton (Twist.H R n d i) := by
  rcases i with _ | j
  · exact absurd hi (Nat.not_lt_zero n)
  dsimp only [Twist.H]
  have hsub := Twist.cochain_subsingleton_of_lt R n d hi
  exact ⟨fun x y => Quotient.inductionOn₂' x y fun a b =>
    congrArg _ (Subtype.ext (hsub.elim a.1 b.1))⟩

end Cohomology

end ProjSpaceCech

open _root_.AlgebraicCurves.Cohomology.Cech.Proofs in
theorem _root_.ProjSpaceCech.Twist.subsingleton_cohomology_of_lt (R : Type u) [CommRing R] (n :
  ℕ) (d : ℤ) {i : ℕ}
    (hi : n < i) : Subsingleton (ProjSpaceCech.Twist.H R n d i) :=
  ProjectiveTwistSubsingleton.ProjSpaceCech.Twist.subsingleton_cohomology_of_lt R n d hi

end
end AlgebraicCurves.Cohomology.Cech.Proofs.ProjectiveTwistSubsingleton
end ProofImplementation
