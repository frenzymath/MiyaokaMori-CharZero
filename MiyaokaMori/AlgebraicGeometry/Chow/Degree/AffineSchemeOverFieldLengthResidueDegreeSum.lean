import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreePushforward
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.AffineResidueFieldBase

/-! # Lengths and residue degrees on an affine scheme finite over a field

Let `X` be an affine scheme with `p : X ⟶ Spec k` (`k` a field) such that `Γ(X, O_X)` is a finite
`k`-algebra. Then `Σ_{x ∈ X} length(O_{X,x}) · [κ(x) : k] = dim_k Γ(X, O_X)` (Stacks 00KZ + the local
case of 02M0).

Source: step 4 of the proof of Stacks 02RH (decomposition of Artinian rings 00KZ + Algebra 02M0). The
proof is steps 5–7 of `EulerCharZeroDimDegree.lean`, without the `X.Over (Spec k)` instance and with an
arbitrary structure morphism `p`.

This module does not import `EulerCharZeroDimDegree` (that would create an import cycle through
`Stacks02rh`); the purely algebraic lemma `Module.finrank_eq_length_toNat_mul_finrank_residueField`
(the local case of Stacks 02M0) that it needs is reproduced here as a `private` lemma
(`finrank_eq_length_toNat_mul_finrank_residueField_aux`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- **Local algebra of a finite-dimensional local algebra** (Stacks 02M0 for a local ring; private copy of
`Module.finrank_eq_length_toNat_mul_finrank_residueField` from `EulerCharZeroDimDegree.lean`,
duplicated here to avoid the import cycle described in the module docstring). Let `R` be a local ring that is a finite
`k`-algebra (`k` a field) and let `κ` be a field with `k → R → κ` a scalar tower such that `R → κ` is surjective with
kernel the maximal ideal (so `κ` is the residue field of `R`). Then `dim_k R = length_R(R) · [κ : k]`.
Proof: `length_k R = dim_k R` (`Module.length_eq_finrank`); `length_k R = length_R R · length_{κ_k} κ_R`
(`IsLocalRing.length_restrictScalars`); `length_{κ_k} κ_R = dim_{κ_k} κ_R = dim_k κ_R` because `k ≅ κ_k`; and
`κ_R ≃ₐ[k] κ` by the first isomorphism theorem. `length_R R` is finite because `R` is Artinian and Noetherian. -/
private theorem finrank_eq_length_toNat_mul_finrank_residueField_aux (k R : Type u) [Field k]
    [CommRing R] [IsLocalRing R] [Algebra k R] [Module.Finite k R]
    (κ : Type u) [Field κ] [Algebra R κ] [Algebra k κ] [IsScalarTower k R κ]
    (hκ : Function.Surjective (algebraMap R κ))
    (hker : RingHom.ker (algebraMap R κ) = IsLocalRing.maximalIdeal R) :
    Module.finrank k R = (Module.length R R).toNat * Module.finrank k κ := by
  have hArt : IsArtinianRing R := isArtinian_of_tower k inferInstance
  have hNoe : IsNoetherianRing R := isNoetherian_of_tower k inferInstance
  have hfin : Module.length R R ≠ ⊤ := Module.length_ne_top
  have h1 : Module.length k R = Module.finrank k R := Module.length_eq_finrank k R
  have h2 : Module.length k R = Module.length R R *
      Module.length (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField R) :=
    IsLocalRing.length_restrictScalars k R R
  have : Module.Finite (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField R) :=
    Module.Finite.of_restrictScalars_finite k _ _
  have h3 : Module.length (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField R) =
      Module.finrank (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField R) :=
    Module.length_eq_finrank _ _
  have h4 : Module.finrank k (IsLocalRing.ResidueField k) = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      ⟨(algebraMap k (IsLocalRing.ResidueField k)).injective, IsLocalRing.residue_surjective⟩
  have h5 : Module.finrank (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField R) =
      Module.finrank k (IsLocalRing.ResidueField R) := by
    have := Module.finrank_mul_finrank k (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField R)
    rw [h4, one_mul] at this
    exact this
  let e : IsLocalRing.ResidueField R ≃ₐ[k] κ :=
    (Ideal.quotientEquivAlgOfEq k hker).symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := IsScalarTower.toAlgHom k R κ) hκ)
  have h6 : Module.finrank k (IsLocalRing.ResidueField R) = Module.finrank k κ :=
    e.toLinearEquiv.finrank_eq
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.length R R = n := ⟨_, (ENat.natCast_toNat hfin).symm⟩
  rw [hn, ENat.toNat_natCast]
  have key : ((Module.finrank k R : ℕ) : ℕ∞) = ((n * Module.finrank k κ : ℕ) : ℕ∞) := by
    rw [← h1, h2, hn, h3, h5, h6, Nat.cast_mul]
  exact_mod_cast key

/-- The base map `k → κ(x)` of `AlgebraicGeometry.Intersection.pointBaseMap p x` factors as
`k → Γ(Spec k) → Γ(X, O_X) → O_{X,x} → κ(x)` (version of
`pointBaseMap_eq_structureRingHom_germ_residue` for an arbitrary morphism `p : X ⟶ Spec k`, without an
`Over` instance). Proof: `Spec` is fully faithful (`Spec.preimage_map`), `p = X.toSpecΓ ≫ Spec.map (φ)`
with `φ = (ΓSpecIso k).inv ≫ p.appTop` (`Scheme.toSpecΓ_naturality`), and
`X.fromSpecStalk x ≫ X.toSpecΓ = Spec.map (germ)` (`Scheme.fromSpecStalk_toSpecΓ`). -/
theorem pointBaseMap_eq_ΓSpecIso_inv_appTop_germ_residue {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    AlgebraicGeometry.Intersection.pointBaseMap p x =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop) ≫
        X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
  unfold AlgebraicGeometry.Intersection.pointBaseMap
  have hp : p = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  conv_lhs => rw [hp]
  rw [Scheme.fromSpecResidueField, Category.assoc, ← Category.assoc (X.fromSpecStalk x),
    Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp, ← Spec.map_comp, Spec.preimage_map,
    Category.assoc]

/-- **Length–degree sum over an affine scheme finite over a field** (Stacks 02RH, proof step 4;
Stacks 00KZ + Algebra 02M0). Let `k` be a field, `X` an affine scheme, `p : X ⟶ Spec k`, and assume that
the structure map `φ : k → Γ(X, O_X)` (namely `(ΓSpecIso k).inv ≫ p.appTop`) is finite. Then
`∑_{x ∈ X} length(O_{X,x}) · [κ(x) : κ(p x)] = dim_k Γ(X, O_X)`, the `k`-module structure on `Γ(X, O_X)` being
the one given by `φ`.

Proof. Write `A := Γ(X, O_X)`, a finite `k`-algebra, hence Artinian with finitely many primes.
(1) `dim_k A = Σ_{q ∈ Spec A} dim_k A_q` (Mathlib `IsArtinianRing.finrank_eq_sum_primeSpectrum`).
(2) Points of `X` correspond bijectively to primes of `A` via `IsAffineOpen.primeIdealOf` for `U = ⊤`
(`hU.isoSpec.hom.homeomorph.bijective`); in particular `X` is finite, so the `finsum` is a finite sum.
(3) For each `x`, `O_{X,x} ≅ A_{q(x)}` as `A`-algebras (`IsAffineOpen.isLocalization_stalk`), so
`dim_k A_{q(x)} = dim_k O_{X,x}`; `O_{X,x}` is a local finite `k`-algebra with residue field `κ(x)`, hence
`dim_k O_{X,x} = length(O_{X,x}) · dim_k κ(x)` (`finrank_eq_length_toNat_mul_finrank_residueField_aux`,
Stacks 02M0 for a local ring), where `k → κ(x)` is `k → A → O_{X,x} → κ(x)`.
(4) `dim_k κ(x) = p.residueDegree x`: `residueFieldDegree p x` uses the `k`-structure `pointBaseMap p x`
on `κ(x)`, which factors as in (3) (`pointBaseMap_eq_ΓSpecIso_inv_appTop_germ_residue`), and equals Mathlib's
`p.residueDegree x` (`Scheme.Hom.residueFieldDegree_eq_residueDegree`).
Edge cases: `X = ∅` gives `0 = 0` (`A = 0`, empty sum); non-reduced points contribute their lengths;
`Module.finrank` is the true dimension since everything is finite-dimensional. -/
theorem Scheme.Hom.finsum_length_stalk_mul_residueDegree_eq_finrank_of_isAffine
    {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [IsAffine X]
    (hfin : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom.Finite) :
    ∑ᶠ x : X, (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat * p.residueDegree x
      = (letI := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom.toAlgebra
         Module.finrank k Γ(X, ⊤)) := by
  set φ : CommRingCat.of k ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop with hφ
  let _ : Algebra k Γ(X, ⊤) := φ.hom.toAlgebra
  have hfinA : Module.Finite k Γ(X, ⊤) := hfin
  -- Step 1: dim_k Γ(X, O_X) = Σ_{q ∈ Spec Γ} dim_k Γ_q (Artinian ring).
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower k inferInstance
  let _ : Fintype (PrimeSpectrum Γ(X, ⊤)) := Fintype.ofFinite _
  have hsum := IsArtinianRing.finrank_eq_sum_primeSpectrum Γ(X, ⊤) k
  -- Step 2: points of X ↔ primes of Γ(X, O_X); in particular X is finite.
  let hU := isAffineOpen_top X
  have hψ : Function.Bijective (fun x : X => hU.primeIdealOf ⟨x, trivial⟩) := by
    have hb := hU.isoSpec.hom.homeomorph.bijective
    constructor
    · intro x y hxy
      exact congrArg Subtype.val (hb.1 (a₁ := ⟨x, trivial⟩) (a₂ := ⟨y, trivial⟩) hxy)
    · intro q
      obtain ⟨⟨x, _⟩, hx⟩ := hb.2 q
      exact ⟨x, hx⟩
  let ψ : X ≃ PrimeSpectrum Γ(X, ⊤) := Equiv.ofBijective _ hψ
  have : Finite X := Finite.of_equiv _ ψ.symm
  let _ : Fintype X := Fintype.ofFinite X
  -- Step 3+4: per point, dim_k Γ_q = dim_k O_{X,x} = length(O_{X,x}) · [κ(x) : k].
  have hpt : ∀ x : X, Module.finrank k (Localization.AtPrime (ψ x).asIdeal)
      = (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat * p.residueDegree x := by
    intro x
    rw [← Scheme.Hom.residueFieldDegree_eq_residueDegree p x]
    let _ : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf (U := ⊤) ⟨x, trivial⟩
    have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (ψ x).asIdeal :=
      hU.isLocalization_stalk ⟨x, trivial⟩
    let _ : Algebra k (X.presheaf.stalk x) :=
      ((algebraMap Γ(X, ⊤) (X.presheaf.stalk x)).comp (algebraMap k Γ(X, ⊤))).toAlgebra
    have : IsScalarTower k Γ(X, ⊤) (X.presheaf.stalk x) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let e : X.presheaf.stalk x ≃ₐ[Γ(X, ⊤)] Localization.AtPrime (ψ x).asIdeal :=
      IsLocalization.algEquiv (ψ x).asIdeal.primeCompl _ _
    let e' := e.restrictScalars k
    have h1 : Module.finrank k (Localization.AtPrime (ψ x).asIdeal)
        = Module.finrank k (X.presheaf.stalk x) := e'.toLinearEquiv.finrank_eq.symm
    have : Module.Finite k (Localization.AtPrime (ψ x).asIdeal) :=
      Module.Finite.of_surjective (IsScalarTower.toAlgHom k Γ(X, ⊤) _).toLinearMap
        (IsArtinianRing.localization_surjective (ψ x).asIdeal.primeCompl _)
    have : Module.Finite k (X.presheaf.stalk x) := Module.Finite.equiv e'.symm.toLinearEquiv
    let _ : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
    let _ : Algebra k (X.residueField x) :=
      (AlgebraicGeometry.Intersection.pointBaseMap p x).hom.toAlgebra
    have : IsScalarTower k (X.presheaf.stalk x) (X.residueField x) :=
      IsScalarTower.of_algebraMap_eq (fun c => by
        show (AlgebraicGeometry.Intersection.pointBaseMap p x).hom c =
          (X.residue x).hom ((X.presheaf.germ ⊤ x trivial).hom (φ.hom c))
        rw [pointBaseMap_eq_ΓSpecIso_inv_appTop_germ_residue]
        rfl)
    have hsurj : Function.Surjective (algebraMap (X.presheaf.stalk x) (X.residueField x)) :=
      IsLocalRing.residue_surjective
    have hker : RingHom.ker (algebraMap (X.presheaf.stalk x) (X.residueField x)) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := IsLocalRing.ker_residue
    rw [h1, finrank_eq_length_toNat_mul_finrank_residueField_aux k (X.presheaf.stalk x)
      (X.residueField x) hsurj hker]
    rfl
  -- Assemble.
  show _ = Module.finrank k Γ(X, ⊤)
  rw [finsum_eq_sum_of_fintype, hsum,
    ← Fintype.sum_equiv ψ (fun x => Module.finrank k (Localization.AtPrime (ψ x).asIdeal))
      (fun q => Module.finrank k (Localization.AtPrime q.asIdeal)) (fun _ => rfl)]
  exact Finset.sum_congr rfl (fun x _ => (hpt x).symm)

end AlgebraicGeometry

end
