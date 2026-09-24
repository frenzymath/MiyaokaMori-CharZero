import MiyaokaMori.Prelude

/-! # Extending a derivation to localizations and to sections of the structure sheaf

Let `R → A` be a homomorphism of commutative rings, `N` an `A`-module and `D : A → N` an
`R`-derivation.
1. For every submonoid `S` of `A`, `D` extends uniquely to an `R`-derivation
   `D_S : S⁻¹A → S⁻¹N` (`Derivation.localizedModule`) with `D_S(a/1) = D(a)/1` and the quotient
   rule `D_S(a/s) = (s·Da − a·Ds)/s²`; in particular `D_S` vanishes on elements of the form
   `φ(r)/φ(r')`.
2. For an open `U ⊆ Spec A`, applying `D_𝔭` pointwise to a section `s ∈ O(U)` (a compatible
   family of elements of the local rings `A_𝔭`) gives an additive map `O(U) → Ñ(U)`
   (`StructureSheaf.derivationSections`) satisfying the Leibniz rule, commuting with restriction,
   sending the image of `a ∈ A` to the image of `D(a)`, and vanishing on sections pulled back
   from `Spec R` along `Spec(φ)`.

Proof sketch. (1) `D` corresponds to an `A`-linear map `l : Ω_{A/R} → N`
(`Derivation.liftKaehlerDifferential`); `Ω_{A/R} → Ω_{S⁻¹A/R}` is the localization at `S`
(`KaehlerDifferential.isLocalizedModule_map`), so `Ω_{A/R} → N → S⁻¹N` extends uniquely to a
`S⁻¹A`-linear map `l_S : Ω_{S⁻¹A/R} → S⁻¹N`; put `D_S = l_S ∘ d`. Then
`D_S(a/1) = l(da)/1 = D(a)/1`, and the quotient rule follows from the Leibniz rule applied to
`(a/s)·(s/1) = a/1`, `s` being invertible on `S⁻¹N`. (2) A section is locally `a/g`, so
`𝔭 ↦ D_𝔭(s(𝔭))` is locally `(g·Da − a·Dg)/g²`, again a local fraction; the remaining properties
hold pointwise, using `StructureSheaf.comap_apply` and `Localization.localRingHom_mk'` for the
sections pulled back from `Spec R`.

References: Stacks 01UO, 00RT (extension of derivations along localization).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

namespace Derivation

variable {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup N] [Module A N]
  [Module R N] [IsScalarTower R A N]

/-- The `S⁻¹A`-linear map `Ω_{S⁻¹A/R} → S⁻¹N` extending `Ω_{A/R} → N → S⁻¹N`. -/
def localizedModuleAux (D : Derivation R A N) (S : Submonoid A) :
    Ω[Localization S⁄R] →ₗ[Localization S] LocalizedModule S N :=
  LinearMap.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.lift S (KaehlerDifferential.map R R A (Localization S))
      ((LocalizedModule.mkLinearMap S N).comp D.liftKaehlerDifferential)
      (fun s => IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S N) s))

def localizedModule (D : Derivation R A N) (S : Submonoid A) :
    Derivation R (Localization S) (LocalizedModule S N) :=
  (D.localizedModuleAux S).compDer (KaehlerDifferential.D R (Localization S))

theorem localizedModule_algebraMap (D : Derivation R A N) (S : Submonoid A) (a : A) :
    D.localizedModule S (algebraMap A (Localization S) a) = LocalizedModule.mk (D a) 1 := by
  simp [localizedModule, localizedModuleAux]
  rw [← KaehlerDifferential.map_D R R A (Localization S), IsLocalizedModule.lift_apply]
  simp

/-- The quotient rule `D_S(a/s) = (s·Da − a·Ds)/s²`. -/
theorem localizedModule_mk (D : Derivation R A N) (S : Submonoid A) (a : A) (s : S) :
    D.localizedModule S (Localization.mk a s) =
      LocalizedModule.mk ((s : A) • D a - a • D (s : A)) (s * s) := by
  have h1 : Localization.mk a s * algebraMap A (Localization S) s = algebraMap A (Localization S) a := by
    rw [Localization.mk_eq_mk']; exact IsLocalization.mk'_spec _ a s
  have h2 := congrArg (D.localizedModule S) h1
  rw [leibniz, localizedModule_algebraMap, localizedModule_algebraMap, LocalizedModule.mk_smul_mk,
    algebraMap_smul] at h2
  have hu : IsUnit (algebraMap A (Module.End A (LocalizedModule S N)) s) :=
    IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S N) s
  rw [Module.End.isUnit_iff] at hu
  apply hu.injective
  change (s : A) • (D.localizedModule S (Localization.mk a s)) = (s : A) • LocalizedModule.mk ((s : A) • D a - a • D (s : A)) (s * s)
  rw [eq_sub_of_add_eq' h2, LocalizedModule.smul'_mk, mul_one,
    sub_eq_add_neg, ← LocalizedModule.mk_neg, LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, one_mul, smul_add, smul_neg, smul_sub, mul_smul]
  module

/-- `D_S` vanishes on quotients of elements of `R`. -/
theorem localizedModule_mk_algebraMap (D : Derivation R A N) (S : Submonoid A) (r r' : R)
    (h : algebraMap R A r' ∈ S) :
    D.localizedModule S (Localization.mk (algebraMap R A r) ⟨algebraMap R A r', h⟩) = 0 := by
  rw [localizedModule_mk]
  simp

end Derivation

namespace AlgebraicGeometry.StructureSheaf

open TopologicalSpace Opposite

variable {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup N] [Module A N]
  [Module R N] [IsScalarTower R A N]

set_option backward.isDefEq.respectTransparency.types false in
/-- The derivation acting pointwise on sections of the structure sheaf. -/
def derivationSections (D : Derivation R A N) (U : Opens (PrimeSpectrum.Top A)) :
    (structureSheafInType A A).obj.obj (op U) →+ (structureSheafInType A N).obj.obj (op U) where
  toFun s := ⟨fun x => D.localizedModule x.1.asIdeal.primeCompl (s.1 x), by
    intro x
    obtain ⟨V, hxV, i, a, g, h⟩ := s.2 x
    refine ⟨V, hxV, i, g • D a - a • D g, g * g, fun y => ?_⟩
    obtain ⟨hg, hy⟩ := h y
    refine ⟨y.1.asIdeal.primeCompl.mul_mem hg hg, ?_⟩
    exact (congrArg (D.localizedModule y.1.asIdeal.primeCompl) hy).trans
      (D.localizedModule_mk y.1.asIdeal.primeCompl a ⟨g, hg⟩)⟩
  map_zero' := Subtype.ext <| funext fun x => map_zero _
  map_add' s t := Subtype.ext <| funext fun x => map_add _ _ _

set_option backward.isDefEq.respectTransparency.types false in
theorem derivationSections_algebraMap (D : Derivation R A N) (U : Opens (PrimeSpectrum.Top A)) (a : A) :
    derivationSections D U (algebraMap A _ a) = toOpenₗ A N U (D a) :=
  Subtype.ext <| funext fun x => D.localizedModule_algebraMap x.1.asIdeal.primeCompl a

set_option backward.isDefEq.respectTransparency.types false in
theorem derivationSections_mul (D : Derivation R A N) (U : Opens (PrimeSpectrum.Top A))
    (s t : (structureSheafInType A A).obj.obj (op U)) :
    derivationSections D U (s * t) = s • derivationSections D U t + t • derivationSections D U s :=
  Subtype.ext <| funext fun x => (D.localizedModule x.1.asIdeal.primeCompl).leibniz _ _

theorem derivationSections_res (D : Derivation R A N) (U V : Opens (PrimeSpectrum.Top A)) (i : V ⟶ U)
    (s : (structureSheafInType A A).obj.obj (op U)) :
    derivationSections D V ((structureSheafInType A A).obj.map i.op s) =
      (structureSheafInType A N).obj.map i.op (derivationSections D U s) := rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem derivationSections_comap (D : Derivation R A N) (V : Opens (PrimeSpectrum.Top R))
    (U : Opens (PrimeSpectrum.Top A)) (hUV : U.1 ⊆ PrimeSpectrum.comap (algebraMap R A) ⁻¹' V.1)
    (r : (structureSheafInType R R).obj.obj (op V)) :
    derivationSections D U (comap (algebraMap R A) V U hUV r) = 0 := by
  refine Subtype.ext <| funext fun x => ?_
  change D.localizedModule x.1.asIdeal.primeCompl ((comap (algebraMap R A) V U hUV r).1 x) = 0
  rw [comap_apply]
  generalize r.1 ⟨PrimeSpectrum.comap (algebraMap R A) x.1, hUV x.2⟩ = z
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq
    (PrimeSpectrum.comap (algebraMap R A) x.1).asIdeal.primeCompl z
  rw [Localization.localRingHom_mk', ← Localization.mk_eq_mk']
  exact D.localizedModule_mk_algebraMap _ a b _

end AlgebraicGeometry.StructureSheaf

