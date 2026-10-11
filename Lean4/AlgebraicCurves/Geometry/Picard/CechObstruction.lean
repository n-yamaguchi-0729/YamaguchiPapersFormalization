/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_CechPicardObstruction.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Pi
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import AlgebraicCurves.Geometry.Picard.Functor


/-!
# Cech Obstruction
-/

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Scheme.Modules

variable {Y : Scheme.{u}}

/-- The section obtained by applying an automorphism of the unit sheaf on an open subscheme to its
unit section and transporting it to the original open. -/
def unitAutSection (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W :
      Scheme.{u}).ringCatSheaf) :
    Γ(Y, W) :=
  W.topIso.hom ((e.hom.val.app (op ⊤)).hom (1 : (W : Scheme.{u}).presheaf.obj (op ⊤)))

/-- A choice of a trivialisation of a sheaf of modules on each member of an ordered affine cover. -/
abbrev CechTrivialisation (𝒱 : Y.OrderedAffineCover) (𝓜 : Y.Modules) : Type u :=
  ∀ a : 𝒱.ι, (Scheme.Modules.pullback (𝒱.U a).ι).obj 𝓜 ≅ SheafOfModules.unit ((𝒱.U a :
    Scheme.{u})).ringCatSheaf

namespace CechTrivialisation

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules}

/-- Restrict a chosen cover trivialisation to a smaller open subscheme using the pullback
composition and unit isomorphisms. -/
def restrict (τ : CechTrivialisation 𝒱 𝓜) {a : 𝒱.ι} {W : Y.Opens} (h : W ≤ 𝒱.U a) :
    (Scheme.Modules.pullback W.ι).obj 𝓜 ≅ SheafOfModules.unit ((W : Scheme.{u})).ringCatSheaf :=
  ((Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).app 𝓜).symm ≪≫
    ((Scheme.Modules.pullbackComp (Y.homOfLE h) (𝒱.U a).ι).app 𝓜).symm ≪≫
    (Scheme.Modules.pullback (Y.homOfLE h)).mapIso (τ a) ≪≫
    Scheme.Modules.pullbackUnitIso (Y.homOfLE h)

/-- The section representing the transition automorphism between the two restricted
trivialisations on a cover overlap. -/
def transition (τ : CechTrivialisation 𝒱 𝓜) (s : 𝒱.Idx 1) : Γ(Y, 𝒱.inter s) :=
  unitAutSection (𝒱.inter s) ((τ.restrict (𝒱.inter_le s 0)).symm ≪≫ τ.restrict (𝒱.inter_le s 1))

/-- Pull back a cover trivialisation along an affine morphism to the inverse-image ordered cover. -/
def comap (τ : CechTrivialisation 𝒱 𝓜) {Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsAffineHom h] :
    CechTrivialisation (𝒱.comap h) ((Scheme.Modules.pullback h).obj 𝓜) := fun a =>
  ((Scheme.Modules.pullbackComp (h ⁻¹ᵁ 𝒱.U a).ι h).app 𝓜) ≪≫
    ((Scheme.Modules.pullbackCongr (morphismRestrict_ι h (𝒱.U a)).symm).app 𝓜) ≪≫
    ((Scheme.Modules.pullbackComp (h ∣_ 𝒱.U a) (𝒱.U a).ι).app 𝓜).symm ≪≫
    (Scheme.Modules.pullback (h ∣_ 𝒱.U a)).mapIso (τ a) ≪≫
    Scheme.Modules.pullbackUnitIso (h ∣_ 𝒱.U a)

end CechTrivialisation

end Scheme.Modules

namespace SmallExtension

open Scheme.TwoAffineOpenCover

variable {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
variable (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ιJ : V →ₗ[B₁] B₁)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
variable {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X)

/-- Express a section using the small-extension ideal map and require its fibre readings against
dual vectors to equal the corresponding restricted coefficient sums. -/
def IsFibreReading (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (δ : Γ(X, U))
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W) : Prop :=
  letI := algebraOfHom f U
  ∃ (n : ℕ) (v : Fin n → V) (s : Fin n → Γ(X, U)),
    (∑ j, algebraMap B₁ (X.presheaf.obj (op U)) (ιJ (v j)) * s j) = δ ∧
      ∀ ξ : Module.Dual k V,
        w ξ = ∑ j, ξ (v j) • (OModulePresheaf.unit fk).res hW
          (show (OModulePresheaf.unit fk).obj (i ⁻¹ᵁ U) from (i.app U).hom (s j))

variable {X₀ : Scheme.{u}} (g : X₀ ⟶ X) [IsAffineHom g] [IsAffineHom i]
variable (𝒰 : X.OrderedAffineCover)

/-- The assertion that a degree-two fibre cochain reads the failure of lifted invertible
transition sections to satisfy the cocycle equation. -/
def IsPicObstructionCocycle (𝓛₀ : X₀.Modules)
    (c : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2) : Prop :=
  ∃ (τ : Scheme.Modules.CechTrivialisation (𝒰.comap g) 𝓛₀)
    (u u' : ∀ s : 𝒰.Idx 1, Γ(X, 𝒰.inter s)),
    (∀ s : 𝒰.Idx 1,
      (X₀.presheaf.map (homOfLE (𝒰.comap_inter_le g s)).op).hom ((g.app (𝒰.inter s)).hom (u s)) =
        τ.transition s) ∧
    (∀ s : 𝒰.Idx 1, u s * u' s = 1) ∧
    ∀ r : 𝒰.Idx 2,
      IsFibreReading V ιJ f fk i (𝒰.inter r) ((𝒰.comap i).inter r) (𝒰.comap_inter_le i r)
        ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (u (𝒰.face r 2)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (u (𝒰.face r 0)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u' (𝒰.face r 1)) - 1)
        ((LinearMap.proj (R := k)
          (φ := fun t : (𝒰.comap i).Idx 2 =>
            (OModulePresheaf.unit fk).obj ((𝒰.comap i).inter t)) r).comp c)

/-- The assertion that a degree-one fibre cochain reads the transition sections relative to chosen
local units compatible with a pullback trivialisation. -/
def IsPicDeformationCocycle (M : X.Modules)
    (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1) : Prop :=
  ∃ (τ : Scheme.Modules.CechTrivialisation 𝒰 M) (e e' : ∀ a : 𝒰.ι, Γ(X, 𝒰.U a)),
    (∀ a : 𝒰.ι, e a * e' a = 1) ∧
    (∀ a : 𝒰.ι,
      (g.app (𝒰.U a)).hom (e a) =
        Scheme.Modules.unitAutSection ((𝒰.comap g).U a)
          ((τ.comap g a).symm ≪≫
            ((Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso φ₀ ≪≫
              Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι))) ∧
    ∀ s : 𝒰.Idx 1,
      IsFibreReading V ιJ f fk i (𝒰.inter s) ((𝒰.comap i).inter s) (𝒰.comap_inter_le i s)
        (τ.transition s *
            (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (e' (s.1 0)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (e (s.1 1)) - 1)
        ((LinearMap.proj (R := k)
          (φ := fun t : (𝒰.comap i).Idx 1 =>
            (OModulePresheaf.unit fk).obj ((𝒰.comap i).inter t)) s).comp w)

end SmallExtension

end AlgebraicGeometry

end
