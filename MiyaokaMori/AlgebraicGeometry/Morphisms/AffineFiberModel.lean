import MiyaokaMori.Prelude

/-! # Affine local model of a fibre

Let `p : X → Y` be a morphism of schemes, `U ⊆ Y` an affine open such that `W = p⁻¹U` is affine,
`z ∈ U`, and `𝔭 ⊂ Γ(Y,U)` the prime ideal corresponding to `z`. Then
(1) `𝔮 ↦ fromSpec 𝔮` is a bijection `{𝔮 ∈ Spec Γ(X,W) | 𝔮 ∩ Γ(Y,U) = 𝔭} ≃ p⁻¹{z}` (`fiberEquiv`);
(2) for `p x = z`, the stalk map `O_{Y,z} ≅ O_{Y,p x} → O_{X,x}` sends the germ `germ_z(r)` to
`germ_x(p^♯ r)` for `r ∈ Γ(Y,U)` (`stalkMapOfEq_germ`);
(3) for `p x = z`, the degree `[κ(x) : κ(z)]` of the residue field extension induced by the stalk
map of (2) equals Mathlib's `p.residueDegree x` (`finrank_residueField_stalkMapOfEq`).

Proof sketch.
1. (1): if `x ∈ p⁻¹{z}` then `x ∈ W`, and `IsAffineOpen.comap_primeIdealOf_appLE` gives
   `primeIdealOf(x) ∩ Γ(Y,U) = primeIdealOf(p x) = 𝔭`. Conversely, for `x = fromSpec 𝔮 ∈ W` one has
   `primeIdealOf(x) = 𝔮` (`fromSpec` is an open immersion, hence injective), so
   `primeIdealOf(p x) = 𝔭 = primeIdealOf(z)`; applying `fromSpec` to both sides gives `p x = z`.
2. (2), (3): substitute the equation `p x = z`; then `stalkCongr` becomes the identity, (2) is
   `Scheme.Hom.germ_stalkMap_apply`, and (3) holds by definition.

Reference: the proof of Stacks Project, Tag 02RT (points of an affine local model correspond to
prime ideals).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The stalk map `O_{Y,z} ≅ O_{Y,p x} → O_{X,x}` for `p x = z`. -/
def stalkMapOfEq {x : X} {z : Y} (hx : p.base x = z) : Y.presheaf.stalk z →+* X.presheaf.stalk x :=
  ((Y.presheaf.stalkCongr (Inseparable.of_eq hx.symm)).hom ≫ p.stalkMap x).hom

theorem stalkMapOfEq_germ {x : X} {z : Y} (hx : p.base x = z) (U : Y.Opens) (hz : z ∈ U)
    (r : Γ(Y, U)) :
    stalkMapOfEq p hx (Y.presheaf.germ U z hz r) =
      X.presheaf.germ (p ⁻¹ᵁ U) x (show p.base x ∈ U from hx ▸ hz) (p.app U r) := by
  subst hx
  simp only [stalkMapOfEq, TopCat.Presheaf.stalkCongr, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact Scheme.Hom.germ_stalkMap_apply p U x hz r

instance isLocalHom_stalkMapOfEq {x : X} {z : Y} (hx : p.base x = z) :
    IsLocalHom (stalkMapOfEq p hx) := by
  subst hx
  unfold stalkMapOfEq
  rw [CommRingCat.hom_comp]
  infer_instance

private theorem finrank_residueField_congr {A S : Type*} [CommRing A] [CommRing S] [IsLocalRing A]
    [IsLocalRing S] (f g : A →+* S) [IsLocalHom f] [IsLocalHom g] (h : f = g) :
    (letI := (IsLocalRing.ResidueField.map f).toAlgebra
     Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField S)) =
    (letI := (IsLocalRing.ResidueField.map g).toAlgebra
     Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField S)) := by
  subst h; rfl

theorem finrank_residueField_stalkMapOfEq {x : X} {z : Y} (hx : p.base x = z) :
    (letI := (IsLocalRing.ResidueField.map (stalkMapOfEq p hx)).toAlgebra
     Module.finrank (IsLocalRing.ResidueField (Y.presheaf.stalk z))
      (IsLocalRing.ResidueField (X.presheaf.stalk x))) = p.residueDegree x := by
  subst hx
  have h : stalkMapOfEq p rfl = (p.stalkMap x).hom := by
    ext a
    simp [stalkMapOfEq, TopCat.Presheaf.stalkCongr]
  exact (finrank_residueField_congr _ _ h).trans rfl

section Fiber

variable {U : Y.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen (p ⁻¹ᵁ U)) {z : Y} (hz : z ∈ U)

theorem fromSpec_mem_of_isAffineOpen {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W)
    (𝔮 : Spec Γ(X, W)) : hW.fromSpec 𝔮 ∈ W := by
  have : hW.fromSpec 𝔮 ∈ Set.range hW.fromSpec := ⟨𝔮, rfl⟩
  rwa [hW.range_fromSpec] at this

theorem primeIdealOf_fromSpec {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W)
    (𝔮 : Spec Γ(X, W)) :
    hW.primeIdealOf ⟨hW.fromSpec 𝔮, fromSpec_mem_of_isAffineOpen hW 𝔮⟩ = 𝔮 := by
  apply hW.fromSpec.isOpenEmbedding.injective
  exact hW.fromSpec_primeIdealOf _

/-- The ring homomorphism `Γ(Y,U) → Γ(X,p⁻¹U)` induced by `p`. -/
abbrev appPreimage (U : Y.Opens) : Γ(Y, U) →+* Γ(X, p ⁻¹ᵁ U) := (p.app U).hom

include hU in
theorem comap_primeIdealOf_app {x : X} (hx : x ∈ p ⁻¹ᵁ U) :
    (hW.primeIdealOf ⟨x, hx⟩).asIdeal.comap (appPreimage p U) =
      (hU.primeIdealOf ⟨p.base x, hx⟩).asIdeal := by
  have h := IsAffineOpen.comap_primeIdealOf_appLE (f := p) U hU (p ⁻¹ᵁ U) hW le_rfl hx
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact congr($(h).asIdeal)

theorem base_fromSpec_eq (𝔮 : Spec Γ(X, p ⁻¹ᵁ U))
    (h𝔮 : 𝔮.asIdeal.comap (appPreimage p U) = (hU.primeIdealOf ⟨z, hz⟩).asIdeal) :
    p.base (hW.fromSpec 𝔮) = z := by
  have hx := fromSpec_mem_of_isAffineOpen hW 𝔮
  have h1 := comap_primeIdealOf_app p hU hW hx
  rw [primeIdealOf_fromSpec hW 𝔮, h𝔮] at h1
  have h2 : hU.primeIdealOf ⟨z, hz⟩ = hU.primeIdealOf ⟨p.base (hW.fromSpec 𝔮), hx⟩ :=
    PrimeSpectrum.ext h1
  have h3 := hU.fromSpec_primeIdealOf ⟨z, hz⟩
  rw [h2, hU.fromSpec_primeIdealOf] at h3
  exact h3

/-- The bijection `{𝔮 | 𝔮 ∩ Γ(Y,U) = 𝔭_z} ≃ p⁻¹{z}`, `𝔮 ↦ fromSpec 𝔮`. -/
def fiberEquiv :
    {𝔮 : PrimeSpectrum Γ(X, p ⁻¹ᵁ U) //
      𝔮.asIdeal.comap (appPreimage p U) = (hU.primeIdealOf ⟨z, hz⟩).asIdeal} ≃
    {x : X // p.base x = z} where
  toFun 𝔮 := ⟨hW.fromSpec 𝔮.1, base_fromSpec_eq p hU hW hz 𝔮.1 𝔮.2⟩
  invFun x := ⟨hW.primeIdealOf ⟨x.1, show p.base x.1 ∈ U by rw [x.2]; exact hz⟩, by
    obtain ⟨x, rfl⟩ := x
    exact comap_primeIdealOf_app p hU hW _⟩
  left_inv 𝔮 := Subtype.ext (primeIdealOf_fromSpec hW 𝔮.1)
  right_inv x := Subtype.ext (hW.fromSpec_primeIdealOf _)

theorem fiberEquiv_apply (𝔮) : (fiberEquiv p hU hW hz 𝔮).1 = hW.fromSpec 𝔮.1 := rfl

end Fiber

end AlgebraicGeometry

end
