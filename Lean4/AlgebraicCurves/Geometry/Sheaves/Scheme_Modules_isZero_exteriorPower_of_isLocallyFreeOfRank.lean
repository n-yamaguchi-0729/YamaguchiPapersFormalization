/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_exteriorPower_free_iso_unit
import AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj

/-!
# Vanishing of exterior powers above the rank

Exterior powers of a locally free module sheaf vanish in degrees greater than its rank.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank
attribute [-simp] PresheafOfModules.pushforwardCongr_inv_app_app_apply
    PresheafOfModules.pushforwardNatTrans_app_app_apply
    PresheafOfModules.pushforwardCongr_hom_app_app_apply

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

namespace exteriorPower
open _root_.exteriorPower
open _root_.exteriorPower

lemma isEmpty_powersetCard_fin_of_lt {n m : ℕ} (h : n < m) : IsEmpty (Set.powersetCard (Fin n) m) :=
  ⟨fun s => by
    have h1 := Set.powersetCard.card_eq s
    have h2 : (s : Finset (Fin n)).card ≤ n := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (s : Finset (Fin n))
    omega⟩

lemma subsingleton_pi_of_lt (A : Type u) [CommRing A] {n m : ℕ} (h : n < m) :
    Subsingleton (⋀[A]^m (Fin n → A)) := by
  have := isEmpty_powersetCard_fin_of_lt h
  exact ((Pi.basisFun A (Fin n)).exteriorPower m).repr.toEquiv.subsingleton

end exteriorPower

namespace PresheafOfModules
open _root_.PresheafOfModules
open _root_.PresheafOfModules

variable {C : Type*} [Category C] (R : Cᵒᵖ ⥤ CommRingCat.{u})

lemma isZero_of_subsingleton {S : Cᵒᵖ ⥤ RingCat.{u}} (P : PresheafOfModules.{u} S)
    (h : ∀ X : Cᵒᵖ, Subsingleton (P.obj X)) : IsZero P := by
  rw [IsZero.iff_id_eq_zero]
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact (h X).elim _ _

lemma isZero_exteriorPower_piPow {n m : ℕ} (h : n < m) :
    IsZero ((exteriorPowerFunctor R m).obj ((open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
        Scheme_Modules_nonempty_exteriorPower_free_iso_unit.PresheafOfModules.piPow R n))) :=
  isZero_of_subsingleton _ (fun X => exteriorPower.subsingleton_pi_of_lt (R.obj X) h)

end PresheafOfModules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open TopologicalSpace

variable (X : Scheme.{u})

lemma isZero_exteriorPower_free_of_lt {n m : ℕ} (h : n < m) :
    IsZero ((exteriorPower X m).obj (SheafOfModules.free.{u} (ULift.{u} (Fin n)))) := by
  refine IsZero.of_iso ?_ ((exteriorPower X m).mapIso
    (open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
      open Scheme_Modules_nonempty_exteriorPower_free_iso_unit.AlgebraicGeometry.Scheme.Modules in
        freeIsoPiPow X n))
  change IsZero ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    ((PresheafOfModules.exteriorPowerFunctor X.sheaf.obj m).obj ((open
      _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
        Scheme_Modules_nonempty_exteriorPower_free_iso_unit.PresheafOfModules.piPow X.sheaf.obj
          n))))
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_isZero
    (PresheafOfModules.isZero_exteriorPower_piPow X.sheaf.obj h)

variable {X}

theorem isZero_exteriorPower_of_isLocallyFreeOfRank {n m : ℕ} {M : X.Modules}
    (hM : IsLocallyFreeOfRank n M) (h : n < m) : IsZero ((exteriorPower X m).obj M) := by
  refine isZero_of_forall_exists_isZero_pullback_obj _ (fun x => ?_)
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM.exists_trivialization x
  obtain ⟨e₁⟩ := nonempty_pullback_exteriorPower_iso_exteriorPower_pullback m U M
  exact ⟨U, hxU, (isZero_exteriorPower_free_of_lt (U : Scheme.{u}) h).of_iso
    (e₁ ≪≫ (exteriorPower (U : Scheme.{u}) m).mapIso e)⟩

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry in
open Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank.AlgebraicGeometry.Scheme in
theorem _root_.AlgebraicGeometry.Scheme.Modules.isZero_exteriorPower_of_isLocallyFreeOfRank
    {X : Scheme.{u}} {n m : ℕ} {M : X.Modules}
    (hM : Scheme.Modules.IsLocallyFreeOfRank n M) (h : n < m) :
    Limits.IsZero ((Scheme.Modules.exteriorPower X m).obj M) :=
  Modules.isZero_exteriorPower_of_isLocallyFreeOfRank hM h
end Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
