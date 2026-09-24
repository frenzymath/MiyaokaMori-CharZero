import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineGenericCoordinates

/-! # Stalk frames of a line bundle

Local frames of a line bundle, for Stacks 02OZ (`Stacks02oz`).

A `StalkFrame L` is an open `U`, a section `q ∈ Γ(U, L)` and, for every `x ∈ U`, an `O_{X,x}`-linear
equivalence `coord x : L_x ≃ O_{X,x}` with `coord x (germ_x q) = 1` (so `germ_x q` is a basis of the
free rank-one module `L_x`, and `coord x` gives the coordinate in this basis).

* `StalkFrame.eq_coord_smul`: `m = coord x m • germ_x q`; `StalkFrame.eq_zero_of_smul_germ_eq_zero`:
  `c • germ_x q = 0 → c = 0` (`germ_x q` is a regular element of `L_x`).
* `StalkFrame.restrict`: a frame restricts to any smaller open.
* `StalkFrame.isUnit_coord`: for two frames at `y`, the coordinate of the generator of one in the other is a
  unit (`germ q' = c • germ q`, `germ q = d • germ q'` give `(cd - 1) • germ q' = 0`, so `cd = 1`).
* `exists_stalkFrame`: every point has a frame, from a trivialization `L|_U ≅ O_U`:
  `q` is the section corresponding to `1`, and `coord` is `lineStalkEquivOfTrivialization`, whose value on germs is the germ of the coordinate section
  (`lineStalkEquivOfTrivialization_germ`). The frame lives on `U.ι ''ᵁ ⊤` (`= U` as a set).

Source: Stacks 01CR (invertible modules are locally free of rank 1).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A local frame of a line bundle: a generator `q` over `U` together with coordinate maps on stalks. -/
structure StalkFrame (L : X.Modules) where
  /-- the open set -/
  U : X.Opens
  /-- the generating section -/
  q : Γ(L, U)
  /-- coordinates in the basis `germ_x q` -/
  coord : ∀ (x : X), x ∈ U → (L.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x)
  coord_germ : ∀ (x : X) (hx : x ∈ U), coord x hx (L.presheaf.germ U x hx q) = 1

namespace StalkFrame

variable {L : X.Modules}

theorem eq_coord_smul (fr : StalkFrame L) {x : X} (hx : x ∈ fr.U) (m : L.presheaf.stalk x) :
    m = fr.coord x hx m • L.presheaf.germ fr.U x hx fr.q := by
  apply (fr.coord x hx).injective
  rw [LinearEquiv.map_smul, fr.coord_germ, smul_eq_mul, mul_one]

theorem eq_zero_of_smul_germ_eq_zero (fr : StalkFrame L) {x : X} (hx : x ∈ fr.U) {c : X.presheaf.stalk x}
    (h : c • L.presheaf.germ fr.U x hx fr.q = 0) : c = 0 := by
  have := congrArg (fr.coord x hx) h
  rw [LinearEquiv.map_smul, fr.coord_germ, smul_eq_mul, mul_one, map_zero] at this
  exact this

/-- Restriction of a frame to a smaller open. -/
def restrict (fr : StalkFrame L) (V : X.Opens) (hV : V ≤ fr.U) : StalkFrame L where
  U := V
  q := L.presheaf.map (homOfLE hV).op fr.q
  coord x hx := fr.coord x (hV hx)
  coord_germ x hx := by
    rw [L.presheaf.germ_res_apply]
    exact fr.coord_germ x (hV hx)

@[simp] theorem restrict_U (fr : StalkFrame L) (V : X.Opens) (hV : V ≤ fr.U) : (fr.restrict V hV).U = V := rfl

theorem restrict_germ (fr : StalkFrame L) (V : X.Opens) (hV : V ≤ fr.U) {x : X} (hx : x ∈ V) :
    L.presheaf.germ V x hx (fr.restrict V hV).q = L.presheaf.germ fr.U x (hV hx) fr.q :=
  L.presheaf.germ_res_apply _ x hx fr.q

/-- The coordinate of the generator of one frame in another frame is a unit. -/
theorem isUnit_coord (fr fr' : StalkFrame L) {y : X} (hy : y ∈ fr.U) (hy' : y ∈ fr'.U) :
    IsUnit (fr.coord y hy (L.presheaf.germ fr'.U y hy' fr'.q)) := by
  set c := fr.coord y hy (L.presheaf.germ fr'.U y hy' fr'.q) with hc
  set d := fr'.coord y hy' (L.presheaf.germ fr.U y hy fr.q) with hd
  have h1 : L.presheaf.germ fr'.U y hy' fr'.q = c • L.presheaf.germ fr.U y hy fr.q :=
    fr.eq_coord_smul hy _
  have h2 : L.presheaf.germ fr.U y hy fr.q = d • L.presheaf.germ fr'.U y hy' fr'.q :=
    fr'.eq_coord_smul hy' _
  have h3 : (c * d - 1) • L.presheaf.germ fr'.U y hy' fr'.q = 0 := by
    rw [sub_smul, one_smul, mul_smul, ← h2, ← h1, sub_self]
  have h4 := fr'.eq_zero_of_smul_germ_eq_zero hy' h3
  exact IsUnit.of_mul_eq_one d (sub_eq_zero.mp h4)

end StalkFrame

/-- Every point of a line bundle's base has a frame (see the module docstring). -/
theorem exists_stalkFrame (L : X.Modules) [L.IsLineBundle] (x : X) : ∃ fr : StalkFrame L, x ∈ fr.U := by
  obtain ⟨t, hx⟩ := IsLineBundle.exists_trivialization L x
  set U := t.carrier with hUdef
  let eM : L.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)) :=
    t.iso ≪≫ (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme).symm
  let e : L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
    eM ≪≫ AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme
  let q₀ : Γ(L.restrict U.ι, ⊤) := e.inv.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤))
  have hq₀ : e.hom.val.app (op ⊤) q₀ = (1 : Γ(U.toScheme, ⊤)) := by
    have h := ((SheafOfModules.evaluation U.toScheme.ringCatSheaf (op ⊤)).mapIso e).inv_hom_id_apply
      (1 : Γ(U.toScheme, ⊤))
    exact h
  have hmem : ∀ z : X, z ∈ U.ι ''ᵁ ⊤ → z ∈ U := fun z hz => by
    rwa [AlgebraicGeometry.Scheme.Opens.ι_image_top] at hz
  refine ⟨StalkFrame.mk (U.ι ''ᵁ ⊤) q₀
      (fun z hz =>
        AlgebraicGeometry.Divisors.LineGenericCoordinates.lineStalkEquivOfTrivialization X L U ⟨z, hmem z hz⟩ eM)
      (fun z hz => ?_), ?_⟩
  · have h := AlgebraicGeometry.Divisors.LineGenericCoordinates.lineStalkEquivOfTrivialization_germ X L U
      ⟨z, hmem z hz⟩ eM ⊤ trivial q₀
    refine h.trans ?_
    change X.presheaf.germ (U.ι ''ᵁ ⊤) z _ (e.hom.val.app (op ⊤) q₀) = 1
    rw [hq₀]
    exact map_one _
  · show x ∈ U.ι ''ᵁ ⊤
    rw [AlgebraicGeometry.Scheme.Opens.ι_image_top]
    exact hx

end AlgebraicGeometry.Scheme.Modules

end
