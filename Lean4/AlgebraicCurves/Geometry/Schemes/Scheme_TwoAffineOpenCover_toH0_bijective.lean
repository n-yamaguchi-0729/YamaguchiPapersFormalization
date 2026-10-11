/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_toH0_bijective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover

/-!
Global sections identify with degree-zero Cech cohomology for a two-affine open cover.
The sheaf condition supplies a ring equivalence with the equalizer of chart restrictions.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_TwoAffineOpenCover_toH0_bijective

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SheafCondition

variable (X : Scheme.{u}) (U V : X.Opens)

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.SheafCondition.eqLocus
    : Subring (Γ(X, U) × Γ(X, V)) :=
  RingHom.eqLocus
    ((X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom.comp (RingHom.fst Γ(X, U) Γ(X, V)))
    ((X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom.comp (RingHom.snd Γ(X, U) Γ(X, V)))

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.SheafCondition
theorem mem_eqLocus_iff (s : Γ(X, U) × Γ(X, V)) :
    s ∈ eqLocus X U V ↔
      (X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom s.1
        = (X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom s.2 :=
  Iff.rfl

/-- Identify global sections with matching sections on the two opens of a cover. -/
def gammaEquiv (h : U ⊔ V = ⊤) : Γ(X, ⊤) ≃+* eqLocus X U V :=
  ((X.presheaf.mapIso (eqToIso h).op).trans
    (X.sheaf.objSupIsoProdEqLocus U V)).commRingCatIsoToRingEquiv

private theorem map_comp_apply {W₁ W₂ W₃ : X.Opens} (f : W₁ ⟶ W₂) (g : W₂ ⟶ W₃) (a : Γ(X, W₃)) :
    (X.presheaf.map f.op).hom ((X.presheaf.map g.op).hom a)
      = (X.presheaf.map (f ≫ g).op).hom a := by
  rw [op_comp, Functor.map_comp, CommRingCat.comp_apply]

theorem gammaEquiv_apply_fst (h : U ⊔ V = ⊤) (a : Γ(X, ⊤)) :
    (gammaEquiv X U V h a).1.1 = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom a := by
  have h0 : (gammaEquiv X U V h a).1.1
      = ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.1 := rfl
  have h1 : ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.1
      = (X.presheaf.map (homOfLE le_sup_left).op).hom ((X.presheaf.map (eqToHom h).op).hom a) :=
    X.sheaf.objSupIsoProdEqLocus_hom_fst U V _
  rw [h0, h1, map_comp_apply X (homOfLE le_sup_left) (eqToHom h) a,
    Subsingleton.elim ((homOfLE le_sup_left : U ⟶ U ⊔ V) ≫ eqToHom h) (homOfLE (le_top : U ≤ ⊤))]

theorem gammaEquiv_apply_snd (h : U ⊔ V = ⊤) (a : Γ(X, ⊤)) :
    (gammaEquiv X U V h a).1.2 = (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a := by
  have h0 : (gammaEquiv X U V h a).1.2
      = ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.2 := rfl
  have h1 : ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.2
      = (X.presheaf.map (homOfLE le_sup_right).op).hom ((X.presheaf.map (eqToHom h).op).hom a) :=
    X.sheaf.objSupIsoProdEqLocus_hom_snd U V _
  rw [h0, h1, map_comp_apply X (homOfLE le_sup_right) (eqToHom h) a,
    Subsingleton.elim ((homOfLE le_sup_right : V ⟶ U ⊔ V) ≫ eqToHom h) (homOfLE (le_top : V ≤ ⊤))]

end SheafCondition

open SheafCondition

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (.of R))

theorem toH0_bijective' : letI := algebraOfHom c ⊤; Function.Bijective (𝒱.toH0 c) := by
  let := algebraOfHom c ⊤
  have hpair : ∀ s : Γ(X, ⊤),
      ((𝒱.toH0 c s : (𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1))
        = (gammaEquiv X 𝒱.U0 𝒱.U1 𝒱.sup_eq_top s).1 := fun s => by
    rw [toH0_apply_coe]
    exact Prod.ext (gammaEquiv_apply_fst X _ _ _ s).symm (gammaEquiv_apply_snd X _ _ _ s).symm
  constructor
  · intro s s' hss'
    apply (gammaEquiv X 𝒱.U0 𝒱.U1 𝒱.sup_eq_top).injective
    apply Subtype.ext
    rw [← hpair, ← hpair, hss']
  · rintro ⟨p, hp⟩
    have hp' : p ∈ eqLocus X 𝒱.U0 𝒱.U1 :=
      (mem_eqLocus_iff X 𝒱.U0 𝒱.U1 p).mpr ((TwoChartCech.Cover.mem_H0_structureSheaf_iff _ p).mp hp)
    refine ⟨(gammaEquiv X 𝒱.U0 𝒱.U1 𝒱.sup_eq_top).symm ⟨p, hp'⟩, Subtype.ext ?_⟩
    rw [hpair, RingEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.toH0_bijective
    {R : Type u} [CommRing R] {X : AlgebraicGeometry.Scheme.{u}}
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ AlgebraicGeometry.Spec (.of R)) :
    letI := AlgebraicGeometry.Scheme.TwoAffineOpenCover.algebraOfHom c ⊤
    Function.Bijective (𝒱.toH0 c) :=
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.toH0_bijective' 𝒱 c

end
end AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_TwoAffineOpenCover_toH0_bijective
end ProofImplementation
