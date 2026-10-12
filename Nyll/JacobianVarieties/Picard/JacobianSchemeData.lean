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

import Nyll.JacobianVarieties.Picard.Designation
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle

/-!
# Scheme data associated to a relative Jacobian designation

The data records a relative Picard designation, its group law, and a point comparison.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace MilneJVScheme

open GoodReductionJacobian

variable {k : Type u} [Field k]

/-- A relative Picard designation with a group law, point comparison, and abelian-scheme data. -/
structure JacobianSchemeData (A : Type*) [AddCommGroup A]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (g : ℕ)
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of k)) where
  /-- The designated relative Picard scheme. -/
  D : RelativePic0Designation k c
  /-- The relative group law on the designated scheme. -/
  L : RelativeGroupLaw k D.toBase
  /-- The comparison between the given group and points over the chosen base map. -/
  bridge : AvatarSchemeBridge A D L σ
  /-- Smoothness, properness, connected fibres, and existence of the group law. -/
  hAbel : AbelianSchemePropertyBundle k D.toBase
  /-- An auxiliary proposition; this field alone does not assert a dimension equality. -/
  hDim : Prop

/-- Form the designated scheme data from a group law and an additive point equivalence. -/
def JacobianSchemeData.ofCore (A : Type*) [AddCommGroup A]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (g : ℕ)
    {J : Scheme.{u}} (f : J ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    (pts : A ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (pts_add : ∀ x y : A, pts (x + y) = L.mul (𝟙 (Spec (CommRingCat.of k))) (pts x) (pts y))
    (hsmooth : Smooth f) (hproper : IsProper f)
    (hconn : ∀ s : Spec (CommRingCat.of k), _root_.IsConnected (f.base ⁻¹' {s})) :
    JacobianSchemeData A c g (𝟙 (Spec (CommRingCat.of k))) where
  D :=
    { P := J
      toBase := f
      zeroSection := (pts 0).1
      zeroSection_toBase := (pts 0).2 }
  L := L
  bridge :=
    { pts := pts
      pts_add := pts_add
      pts_zero := (Category.id_comp _).symm }
  hAbel :=
    { smooth := hsmooth
      proper := hproper
      connectedFibres := hconn
      hasGroupLaw := ⟨L⟩ }
  hDim := True

end MilneJVScheme
