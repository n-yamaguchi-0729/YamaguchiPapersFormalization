/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafIdealFiltration
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_hasDevissageStep
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_forall_of_forall_idealAnnihilates
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_forall_pushforward_of_isIntegral

/-!
# OModule Presheaf forall coherent of forall integral
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_forall_coherent_of_forall_integral

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace P2mDevissageDriver

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))
  [IsProper π]

include π in
theorem isNoetherian : IsNoetherian V := by
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace π
  exact {}

variable (Q : Closeds V → OModulePresheaf π → Prop)
  (h0 : ∀ (Y : Closeds V) (G : OModulePresheaf π), (∀ U : V.affineOpens, Subsingleton (G.obj U.1))
    → Q Y G)
  (hmono : ∀ (Y Y' : Closeds V) (G : OModulePresheaf π), Y' ≤ Y → Q Y' G → Q Y G)
  (hext : ∀ (Y : Closeds V) (G₁ G₂ G₃ : OModulePresheaf π), Nonempty (AffSES G₁ G₂ G₃) →
    G₁.IsCoherent → G₁.IsQuasicoherent → G₂.IsCoherent → G₂.IsQuasicoherent →
    G₃.IsCoherent → G₃.IsQuasicoherent →
    (Q Y G₁ → Q Y G₃ → Q Y G₂) ∧ (Q Y G₁ → Q Y G₂ → Q Y G₃) ∧ (Q Y G₂ → Q Y G₃ → Q Y G₁))
  (hInt : ∀ Z₀ : Closeds V, (Z₀ : Set V).Nonempty →
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
    (∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' → Q Y'
      G) →
    Q Z₀ (pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι))

include h0 hmono hext hInt in
theorem step (Y : Closeds V)
    (IH : ∀ Y' < Y, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' →
      Q Y' G) :
    ∀ F : OModulePresheaf π, F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → Q Y F := by
  have : IsNoetherian V := isNoetherian π
  refine forall_of_forall_idealAnnihilates π Y (Q Y) (h0 Y) (hext Y) ?_
  intro G hGc hGq hGs hann
  by_cases hY : (Y : Set V).Nonempty
  · obtain ⟨D⟩ := hasDevissageStep π G hGc hGq Y hY hGs hann
    have hG₃ : Q Y D.G₃ :=
      hmono Y D.Z₁ D.G₃ D.Z₁_lt.le (IH D.Z₁ D.Z₁_lt D.G₃ D.isCoherent_G₃ D.isQuasicoherent_G₃
        D.supportedIn_G₃)
    have IH₀ : ∀ Y' < D.Z₀, ∀ G' : OModulePresheaf π,
        G'.IsCoherent → G'.IsQuasicoherent → G'.SupportedIn Y' → Q Y' G' :=
      fun Y' hY' G' h₁ h₂ h₃ => IH Y' (lt_of_lt_of_le hY' D.Z₀_le) G' h₁ h₂ h₃
    have hO : Q D.Z₀ (pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal D.Z₀).subschemeι) :=
      hInt D.Z₀ D.Z₀_nonempty D.isIntegral IH₀
    have hH : Q D.Z₀ (pushforward π (Scheme.IdealSheafData.vanishingIdeal D.Z₀).subschemeι D.H) :=
      forall_pushforward_of_isIntegral π D.Z₀ D.Z₀_nonempty D.isIntegral (Q D.Z₀) (h0 D.Z₀) (hext
        D.Z₀) hO
        (fun Y' hY' G' h₁ h₂ h₃ => hmono D.Z₀ Y' G' hY'.le (IH₀ Y' hY' G' h₁ h₂ h₃))
        D.H D.isCoherent_pushforward D.isQuasicoherent_pushforward D.supportedIn_pushforward
    exact (hext Y _ G D.G₃ ⟨D.ses⟩ D.isCoherent_pushforward D.isQuasicoherent_pushforward hGc hGq
      D.isCoherent_G₃ D.isQuasicoherent_G₃).1 (hmono Y D.Z₀ _ D.Z₀_le hH) hG₃
  · refine h0 Y G fun U => hGs U ?_
    rw [Set.not_nonempty_iff_eq_empty.mp hY, Set.inter_empty]

include h0 hmono hext hInt in
theorem main : ∀ (Y : Closeds V) (F : OModulePresheaf π), F.IsCoherent → F.IsQuasicoherent →
  F.SupportedIn Y → Q Y F := by
  have : IsNoetherian V := isNoetherian π
  intro Y
  induction Y using WellFoundedLT.induction with
  | ind Y IH => exact step π Q h0 hmono hext hInt Y IH

end P2mDevissageDriver

theorem _root_.AlgebraicGeometry.OModulePresheaf.forall_coherent_of_forall_integral
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))
      [IsProper π]
    (Q : Closeds V → OModulePresheaf π → Prop)
    (h0 : ∀ (Y : Closeds V) (G : OModulePresheaf π), (∀ U : V.affineOpens, Subsingleton (G.obj
      U.1)) → Q Y G)
    (hmono : ∀ (Y Y' : Closeds V) (G : OModulePresheaf π), Y' ≤ Y → Q Y' G → Q Y G)
    (hext : ∀ (Y : Closeds V) (G₁ G₂ G₃ : OModulePresheaf π), Nonempty (OModulePresheaf.AffSES G₁
      G₂ G₃) →
      G₁.IsCoherent → G₁.IsQuasicoherent → G₂.IsCoherent → G₂.IsQuasicoherent →
      G₃.IsCoherent → G₃.IsQuasicoherent →
      (Q Y G₁ → Q Y G₃ → Q Y G₂) ∧ (Q Y G₁ → Q Y G₂ → Q Y G₃) ∧ (Q Y G₂ → Q Y G₃ → Q Y G₁))
    (hInt : ∀ Z₀ : Closeds V, (Z₀ : Set V).Nonempty →
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
      (∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' → Q
        Y' G) →
      Q Z₀ (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal
        Z₀).subschemeι)) :
    ∀ (Y : Closeds V) (F : OModulePresheaf π), F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y →
      Q Y F :=
  P2mDevissageDriver.main π Q h0 hmono hext hInt
end AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_forall_coherent_of_forall_integral
end ProofImplementation
