import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.TameSymbol
import MiyaokaMori.RingTheory.KeyLemma.DedekindValuationRingEquiv

/-! # Invariance of the tame symbol under compatible isomorphisms

`Ring.tameSymbol A hfin f g ∈ κ(A)` (`TameSymbol.lean`) is built from the data `(A, K, algebraMap A K)`
only: the integral closure `Ã ⊆ K`, its height-one spectrum, the `v`-adic valuations on `K`, the
residue fields of the valuation rings and the norms down to `κ(A)`. Hence a pair of ring isomorphisms
`e : A ≃ A'`, `ψ : K ≃ K'` with `ψ ∘ algebraMap = algebraMap ∘ e` transports it:
`κ(e)(∂_A(f, g)) = ∂_{A'}(ψ f, ψ g)`. Likewise finiteness of the normalization is transported.

Source: Stacks 0EAQ/0EAR (the recipe only depends on `(A ⊂ K)` up to isomorphism); this is the
"tame symbol is invariant under compatible isomorphisms" step in the vanishing of the tame-cycle sum of
the key formula.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

namespace Ring.TameSymbol

variable {A A' K K' : Type u} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A']
  [Field K] [Algebra A K] [IsFractionRing A K] [Field K'] [Algebra A' K'] [IsFractionRing A' K']

/-- The inverse pair `(e⁻¹, ψ⁻¹)` is again compatible. -/
theorem symm_compat (e : A ≃+* A') (ψ : K ≃+* K')
    (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (e a)) (a' : A') :
    ψ.symm (algebraMap A' K' a') = algebraMap A K (e.symm a') := by
  rw [← e.apply_symm_apply a', ← hψ, ψ.symm_apply_apply, e.symm_apply_apply]

/-- Integrality is transported along compatible isomorphisms: if `x` is integral over `A` then `ψ x`
is integral over `A'` (apply `ψ` to a monic equation and move the coefficients with `e`). -/
theorem isIntegral_map_of_ringEquiv (e : A ≃+* A') (ψ : K ≃+* K')
    (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (e a)) {x : K}
    (hx : IsIntegral A x) : IsIntegral A' (ψ x) := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map (e : A →+* A'), hp.map (e : A →+* A'), ?_⟩
  have hcomp : (algebraMap A' K').comp (e : A →+* A') = (ψ : K →+* K').comp (algebraMap A K) := by
    ext a; simp [hψ]
  rw [Polynomial.eval₂_map, hcomp]
  have h := Polynomial.hom_eval₂ p (algebraMap A K) (ψ : K →+* K') x
  rw [hpx, map_zero] at h
  exact h.symm

/-- `ψ` restricted to the integral closures. -/
def integralClosureEquiv (e : A ≃+* A') (ψ : K ≃+* K')
    (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (e a)) :
    integralClosure A K ≃+* integralClosure A' K' where
  toFun x := ⟨ψ x, isIntegral_map_of_ringEquiv e ψ hψ x.2⟩
  invFun y := ⟨ψ.symm y, isIntegral_map_of_ringEquiv e.symm ψ.symm (symm_compat e ψ hψ) y.2⟩
  left_inv x := Subtype.ext (ψ.symm_apply_apply x)
  right_inv y := Subtype.ext (ψ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul ψ (x : K) (y : K))
  map_add' x y := Subtype.ext (map_add ψ (x : K) (y : K))

@[simp] theorem coe_integralClosureEquiv (e : A ≃+* A') (ψ : K ≃+* K')
    (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (e a)) (x : integralClosure A K) :
    (integralClosureEquiv e ψ hψ x : K') = ψ x := rfl

theorem integralClosureEquiv_smul (e : A ≃+* A') (ψ : K ≃+* K')
    (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (e a)) (a : A) (x : integralClosure A K) :
    integralClosureEquiv e ψ hψ (a • x) = e a • integralClosureEquiv e ψ hψ x := by
  apply Subtype.ext
  change ψ ((a • x : integralClosure A K) : K) =
    ((e a • integralClosureEquiv e ψ hψ x : integralClosure A' K') : K')
  rw [Subalgebra.coe_smul, Subalgebra.coe_smul, Algebra.smul_def, Algebra.smul_def, map_mul, hψ]
  rfl

/-- **Transport of "finite normalization" along compatible isomorphisms.**

`e : A ≃+* A'`, `ψ : K ≃+* K'` with `ψ (algebraMap A K a) = algebraMap A' K' (e a)`; if the integral
closure `Ã` of `A` in `K` is a finite `A`-module, then the integral closure of `A'` in `K'` is a finite
`A'`-module. Proof: `ψ` restricts to `Θ : Ã ≃+* Ã'` (`integralClosureEquiv`) with `Θ (a • x) = e a • Θ x`;
so a finite generating set `s` of `Ã` over `A` maps to the generating set `Θ(s)` of `Ã'` over `A'`
(induction on the span). Source: Stacks 0EAQ/0EAR context. -/
theorem moduleFinite_integralClosure_of_ringEquiv (e : A ≃+* A') (ψ : K ≃+* K')
    (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (e a))
    (hfin : Module.Finite A (integralClosure A K)) :
    Module.Finite A' (integralClosure A' K') := by
  classical
  set Θ := integralClosureEquiv e ψ hψ with hΘ
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨⟨s.image Θ, ?_⟩⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := Θ.surjective y
  have hx : x ∈ Submodule.span A (s : Set (integralClosure A K)) := hs ▸ Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ => Θ x ∈ Submodule.span A' ((s.image Θ : Finset _) :
    Set (integralClosure A' K'))) ?_ ?_ ?_ ?_ hx
  · intro x hxs
    exact Submodule.subset_span (by rw [Finset.coe_image]; exact Set.mem_image_of_mem _ hxs)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [hΘ, integralClosureEquiv_smul]
    exact Submodule.smul_mem _ _ hx

/-! ## Transport of the local factors -/

section LocalFactor

variable (e : A ≃+* A') (ψ : K ≃+* K') (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (e a))
  [IsDedekindDomain (integralClosure A K)] [IsFractionRing (integralClosure A K) K]
  [IsDedekindDomain (integralClosure A' K')] [IsFractionRing (integralClosure A' K') K']

/-- The height-one primes of `Ã` and `Ã'` correspond under `Θ`. -/
def heightOneSpectrumEquiv :
    IsDedekindDomain.HeightOneSpectrum (integralClosure A K) ≃
      IsDedekindDomain.HeightOneSpectrum (integralClosure A' K') :=
  IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv (integralClosureEquiv e ψ hψ)

/-- The adic valuations correspond: `v'(ψ x) = v(x)`. -/
theorem valuation_heightOneSpectrumEquiv (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K))
    (x : K) :
    (heightOneSpectrumEquiv e ψ hψ v).valuation K' (ψ x) = v.valuation K x :=
  IsDedekindDomain.HeightOneSpectrum.valuation_equivOfRingEquiv (integralClosureEquiv e ψ hψ) ψ
    (fun _ => rfl) v x

/-- `ψ` restricted to the valuation rings `O_v → O_{v'}`. -/
def valuationSubringEquiv (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K)) :
    (v.valuation K).valuationSubring ≃+*
      ((heightOneSpectrumEquiv e ψ hψ v).valuation K').valuationSubring where
  toFun x := ⟨ψ x, by
    rw [Valuation.mem_valuationSubring_iff, valuation_heightOneSpectrumEquiv]; exact x.2⟩
  invFun y := ⟨ψ.symm y, by
    rw [Valuation.mem_valuationSubring_iff, ← valuation_heightOneSpectrumEquiv e ψ hψ v,
      ψ.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext (ψ.symm_apply_apply x)
  right_inv y := Subtype.ext (ψ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul ψ (x : K) (y : K))
  map_add' x y := Subtype.ext (map_add ψ (x : K) (y : K))

@[simp] theorem coe_valuationSubringEquiv (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K))
    (x : (v.valuation K).valuationSubring) :
    (valuationSubringEquiv e ψ hψ v x : K') = ψ x := rfl

/-- `ordv` only depends on the value of the valuation. -/
theorem ordv_congr {val : Valuation K (WithZero (Multiplicative ℤ))}
    {val' : Valuation K' (WithZero (Multiplicative ℤ))} {x : Kˣ} {x' : K'ˣ}
    (h : val' (x' : K') = val (x : K)) : ordv val' x' = ordv val x := by
  unfold ordv
  rw [neg_inj]
  have : WithZero.unzero ((Valuation.ne_zero_iff val').mpr x'.ne_zero) =
      WithZero.unzero ((Valuation.ne_zero_iff val).mpr x.ne_zero) :=
    WithZero.coe_injective (by rw [WithZero.coe_unzero, WithZero.coe_unzero, h])
  exact congrArg Multiplicative.toAdd this

theorem ordv_heightOneSpectrumEquiv (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K))
    (x : Kˣ) :
    ordv ((heightOneSpectrumEquiv e ψ hψ v).valuation K') (Units.map (ψ : K →* K') x) =
      ordv (v.valuation K) x :=
  ordv_congr (by rw [Units.coe_map, MonoidHom.coe_coe, valuation_heightOneSpectrumEquiv])

/-- `ψ` maps `u(f, g) = (-1)^{ab} f^b / g^a` to the corresponding element for `ψ f, ψ g`. -/
theorem valuationSubringEquiv_symbolElt (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K))
    (f g : Kˣ) :
    valuationSubringEquiv e ψ hψ v (symbolElt (v.valuation K) f g) =
      symbolElt ((heightOneSpectrumEquiv e ψ hψ v).valuation K')
        (Units.map (ψ : K →* K') f) (Units.map (ψ : K →* K') g) := by
  apply Subtype.ext
  rw [coe_valuationSubringEquiv]
  change ψ ((-1 : K) ^ (ordv (v.valuation K) f * ordv (v.valuation K) g) * (f : K) ^ (ordv (v.valuation K) g) /
      (g : K) ^ (ordv (v.valuation K) f)) = _
  rw [map_div₀, map_mul, map_zpow₀, map_zpow₀, map_zpow₀, map_neg, map_one]
  simp only [symbolElt, ordv_heightOneSpectrumEquiv, Units.coe_map, MonoidHom.coe_coe]

variable [IsLocalRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A'] [Ring.KrullDimLE 1 A']

/-- Compatibility of the structure maps `A → O_v`, `A' → O_{v'}`. -/
theorem toValuationSubring_comp (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K)) :
    (toValuationSubring A' (heightOneSpectrumEquiv e ψ hψ v)).comp (e : A →+* A') =
      (valuationSubringEquiv e ψ hψ v : _ →+* _).comp (toValuationSubring A v) := by
  ext a
  exact (hψ a).symm

/-- **Transport of the local factor `Norm_{κ(v)/κ}(u(f, g) mod 𝔪_v)` along `(e, ψ)`.** -/
theorem mapEquiv_localFactor (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K))
    (f g : Kˣ) :
    IsLocalRing.ResidueField.mapEquiv e (localFactor A v f g) =
      localFactor A' (heightOneSpectrumEquiv e ψ hψ v)
        (Units.map (ψ : K →* K') f) (Units.map (ψ : K →* K') g) := by
  set v' := heightOneSpectrumEquiv e ψ hψ v with hv'
  set Ψ := valuationSubringEquiv e ψ hψ v with hΨ
  haveI : IsLocalHom (toValuationSubring A v) := isLocalHom_toValuationSubring A v
  haveI : IsLocalHom (toValuationSubring A' v') := isLocalHom_toValuationSubring A' v'
  letI : Algebra (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField (v.valuation K).valuationSubring) :=
    (IsLocalRing.ResidueField.map (toValuationSubring A v)).toAlgebra
  letI : Algebra (IsLocalRing.ResidueField A')
      (IsLocalRing.ResidueField (v'.valuation K').valuationSubring) :=
    (IsLocalRing.ResidueField.map (toValuationSubring A' v')).toAlgebra
  have he : (algebraMap (IsLocalRing.ResidueField A')
        (IsLocalRing.ResidueField (v'.valuation K').valuationSubring)).comp
        (IsLocalRing.ResidueField.mapEquiv e : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField A') =
      (IsLocalRing.ResidueField.mapEquiv Ψ : _ →+* _).comp
        (algebraMap (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (v.valuation K).valuationSubring)) := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, RingHom.coe_coe,
      IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    exact congrArg _ (RingHom.congr_fun (toValuationSubring_comp e ψ hψ v) a)
  show IsLocalRing.ResidueField.mapEquiv e
      (Algebra.norm (IsLocalRing.ResidueField A)
        (IsLocalRing.residue (v.valuation K).valuationSubring (symbolElt (v.valuation K) f g))) =
    Algebra.norm (IsLocalRing.ResidueField A')
      (IsLocalRing.residue (v'.valuation K').valuationSubring
        (symbolElt (v'.valuation K') (Units.map (ψ : K →* K') f) (Units.map (ψ : K →* K') g)))
  rw [Algebra.norm_eq_of_equiv_equiv (IsLocalRing.ResidueField.mapEquiv e)
    (IsLocalRing.ResidueField.mapEquiv Ψ) he, RingEquiv.apply_symm_apply,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  congr 2
  exact valuationSubringEquiv_symbolElt e ψ hψ v f g

end LocalFactor

variable [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [IsLocalRing A'] [IsNoetherianRing A'] [Ring.KrullDimLE 1 A']

/-- **Invariance of the tame symbol under compatible isomorphisms (Stacks 0EAQ/0EAR: `∂_A` depends
only on `A ⊂ K` up to isomorphism).**

`A, A'` one-dimensional Noetherian local domains with fraction fields `K, K'`; `e : A ≃+* A'`,
`ψ : K ≃+* K'` with `ψ ∘ algebraMap A K = algebraMap A' K' ∘ e`; `hfin`, `hfin'` the finiteness of the
normalizations. Then `κ(e) (∂_A(f, g)) = ∂_{A'}(ψ f, ψ g)`.

Proof: `ψ` restricts to `Θ : Ã ≃+* Ã'` (`integralClosureEquiv`), inducing `v ↦ v'` on height-one primes
(`heightOneSpectrumEquiv`) with `v'(ψ x) = v(x)` (`valuation_heightOneSpectrumEquiv`, via
`intValuation_equivOfRingEquiv`: `Ideal.map Θ` preserves multiplicities), hence `O_v ≃ O_{v'}`,
`κ(O_v) ≃ κ(O_{v'})`, `u(f,g) ↦ u(ψ f, ψ g)`, and norms are invariant under compatible isomorphisms
(`Algebra.norm_eq_of_equiv_equiv`): `κ(e)(localFactor A v f g) = localFactor A' v' (ψ f) (ψ g)`
(`mapEquiv_localFactor`). Finally `κ(e)` commutes with the finite product over `v`
(`MonoidHom.map_finprod_of_injective`) and we re-index along `v ↦ v'` (`finprod_comp_equiv`). -/
theorem tameSymbol_ringEquiv (e : A ≃+* A') (ψ : K ≃+* K')
    (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (e a))
    (hfin : Module.Finite A (integralClosure A K))
    (hfin' : Module.Finite A' (integralClosure A' K')) (f g : Kˣ) :
    IsLocalRing.ResidueField.mapEquiv e (Ring.tameSymbol A hfin f g) =
      Ring.tameSymbol A' hfin' (Units.map (ψ : K →* K') f) (Units.map (ψ : K →* K') g) := by
  letI : IsDedekindDomain (integralClosure A K) := isDedekindDomain_integralClosure A K hfin
  letI : IsFractionRing (integralClosure A K) K := isFractionRing_integralClosure A K
  letI : IsDedekindDomain (integralClosure A' K') := isDedekindDomain_integralClosure A' K' hfin'
  letI : IsFractionRing (integralClosure A' K') K' := isFractionRing_integralClosure A' K'
  unfold Ring.tameSymbol Ring.tameSymbolAt
  rw [map_finprod (IsLocalRing.ResidueField.mapEquiv e) (f := fun v => localFactor A v f g)
      (finite_mulSupport_localFactor A f g),
    ← finprod_comp_equiv (heightOneSpectrumEquiv e ψ hψ)
      (f := fun v' => localFactor A' v' (Units.map (ψ : K →* K') f) (Units.map (ψ : K →* K') g))]
  exact finprod_congr fun v => mapEquiv_localFactor e ψ hψ v f g

end Ring.TameSymbol

end
