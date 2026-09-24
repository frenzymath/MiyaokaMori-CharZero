import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.FiberPolynomialExtensionDegreeFiberSectionsPolynomialCoordinateChange
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomial
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial

/-! # Sections of bounded ξ-degree in the frame coordinate of a fibre

The geometric half of `totalSpace_fiber_sections_polynomial`: in the coordinate on the fiber
`Tot(L)_y ≅ A¹_k` given by a local frame of `L`, sections of `p^*M` of ξ-degree `≤ r₀` restrict to
polynomials of degree `≤ r₀` (after trivializing the restricted line bundle). (In the paper: "homogenizing
in the fiber coordinate gives homogeneous coordinates of a common degree at most `r_0`".)

`totalSpace_fiber_sections_polynomial` is stated for an *arbitrary* isomorphism `α : Tot(L)_y ≅ A¹_k` and is
assembled from this result (*some* coordinate `α₀` in which the restrictions are polynomials of degree `≤ r₀`)
and the algebra of `FiberPolynomialExtensionDegreeFiberSectionsPolynomialCoordinateChange` (any ring
automorphism of `k[t]` preserves the degree, so the degree bound holds in every coordinate).

`totalSpace_fiber_sections_polynomial_exists_coordinate` is assembled from
`totalSpace_fiber_xiMonomial_exists_ringEquiv` (*some* ring isomorphism `φ : k[t] ≃+* Γ(Tot(L)_y, O)` and
trivialization `τ` on the fiber in which every monomial `c·ξ^q` restricts to a constant times `t^q`) and
glue in this module:
* `exists_iso_affineLine_of_ringEquiv`: for an affine scheme `F`, a ring isomorphism
  `φ : k[t] ≃+* Γ(F, O)` comes from an isomorphism `α₀ : F ≅ A¹_k` with
  `α₀^*(affineLinePolynomial k f) = φ f` (Hartshorne II.2.3 / Stacks 01I1: `Spec` is fully faithful on
  affine schemes; built from `F.isoSpec`, `Spec.map` and `AffineSpace.SpecIso`);
* `totalSpace_fiber_isAffine`: `Tot(L)_y` is affine (base change of the affine morphism `p`;
  `IsAffineHom` is stable under base change, and the target `Spec κ(y)` is affine);
* additivity of restriction along `p.fiberι y` (`sectionPullbackAlong_sum`) and of `τ`
  (`Hom.app_top_sum'`), the finite expansion `P = Σ_q c_q ξ^q` (`eq_sum_xiMonomial`), the
  ring-homomorphism property of `f ↦ α₀^*(f)` (`fiberCoordinate`), and `deg (Σ_{q ≤ r₀} a_q t^q) ≤ r₀`
  (`Polynomial.degree_sum_le`, `degree_C_mul_X_pow_le`, `xiDegree_lt_iff`).
All the geometry lives in `totalSpace_fiber_xiMonomial_exists_ringEquiv`, whose statement mentions neither
the tuple, nor `r₀`, nor degrees, nor `A¹_k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `uniqueAlgEquiv k (ULift (Fin 1))` inverts `aeval (X ⟨0⟩) : k[t] → k[X_{ULift (Fin 1)}]`
(both are `k`-algebra maps sending `t ↦ X ⟨0⟩ ↦ t`; `Polynomial.algHom_ext`). -/
theorem MvPolynomial.uniqueAlgEquiv_aeval_X_ulift {k : Type u} [Field k] (f : Polynomial k) :
    MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))
      (Polynomial.aeval (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k) f) = f := by
  have h : (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).toAlgHom.comp
      (Polynomial.aeval (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k)) =
        AlgHom.id k (Polynomial k) := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, Polynomial.aeval_X, AlgHom.id_apply]
    exact MvPolynomial.eval₂_X _ _ _
  exact congrArg (fun g : Polynomial k →ₐ[k] Polynomial k => g f) h

/-- **Chart from a coordinate ring isomorphism** (Hartshorne II.2.3, Stacks 01I1: `Spec` is fully
faithful on affine schemes). If `F` is affine and `φ : k[t] ≃+* Γ(F, O)`, then there is an isomorphism
`α : F ≅ A¹_k` with `α^*(affineLinePolynomial k f) = φ f` for every `f ∈ k[t]`.

Proof: `α := F.isoSpec ≪≫ Spec(ι) ≪≫ (AffineSpace.SpecIso).symm`, where
`ι : k[X_{ULift (Fin 1)}] ≅ Γ(F, O)` is `φ ∘ uniqueAlgEquiv`. On global sections: `SpecIso.inv.appTop`
cancels the `SpecIso.hom.appTop` inside `affineLinePolynomial`; `(Spec.map ι).appTop` is `ι` conjugated
by `ΓSpecIso` (`ΓSpecIso_inv_naturality`); `F.isoSpec.hom.appTop = (ΓSpecIso Γ(F, ⊤)).hom`
(`toSpecΓ_appTop`) cancels the remaining `ΓSpecIso.inv`; finally `ι (aeval (X ⟨0⟩) f) = φ f`
(`uniqueAlgEquiv_aeval_X_ulift`). -/
theorem exists_iso_affineLine_of_ringEquiv {k : Type u} [Field k] {F : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsAffine F] (φ : Polynomial k ≃+* Γ(F, ⊤)) :
    ∃ α : F ≅ AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)),
      ∀ f : Polynomial k, α.hom.appTop.hom (affineLinePolynomial k f) = φ f := by
  let ψ : MvPolynomial (ULift.{u} (Fin 1)) k ≃+* Γ(F, ⊤) :=
    (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).toRingEquiv.trans φ
  let ι : CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k) ≅ Γ(F, ⊤) := ψ.toCommRingCatIso
  let e := AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)
  refine ⟨F.isoSpec ≪≫ AlgebraicGeometry.Scheme.Spec.mapIso ι.op ≪≫ e.symm, fun f => ?_⟩
  have hA : ∀ y, e.inv.appTop.hom (e.hom.appTop.hom y) = y := fun y => by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← AlgebraicGeometry.Scheme.Hom.comp_appTop,
      Iso.inv_hom_id, AlgebraicGeometry.Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply]
  have hB : ∀ z, (AlgebraicGeometry.Spec.map ι.hom).appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k))).inv.hom z) =
      (AlgebraicGeometry.Scheme.ΓSpecIso Γ(F, ⊤)).inv.hom (ι.hom.hom z) := fun z => by
    have h := congrArg (fun g => g.hom z) (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality ι.hom)
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h.symm
  have hC : ∀ w, F.isoSpec.hom.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(F, ⊤)).inv.hom w) = w :=
    fun w => by
    rw [AlgebraicGeometry.Scheme.isoSpec_hom, AlgebraicGeometry.Scheme.toSpecΓ_appTop,
      ← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_apply]
  have hD : ι.hom.hom (Polynomial.aeval (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k) f) = φ f := by
    change ψ _ = φ f
    simp only [ψ, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv]
    rw [MvPolynomial.uniqueAlgEquiv_aeval_X_ulift]
  change (F.isoSpec.hom ≫ AlgebraicGeometry.Spec.map ι.hom ≫ e.inv).appTop.hom
    (e.hom.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k))).inv.hom
        (Polynomial.aeval (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k) f))) = φ f
  rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, AlgebraicGeometry.Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply, hA, hB, hC, hD]

/-- The scheme-theoretic fiber `Tot(L)_y = p.fiber y` is affine: `p` is affine (relative `Spec`,
`relativeSpec_isAffineHom`), affineness is stable under base change (Mathlib
`isAffineHom_isStableUnderBaseChange`), and the target `Spec κ(y)` of the base change is affine. -/
theorem totalSpace_fiber_isAffine {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) (y : C.toScheme) :
    AlgebraicGeometry.IsAffine ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y) := by
  have : AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom :=
    AlgebraicGeometry.Scheme.relativeSpec_isAffineHom _
  exact inferInstanceAs (AlgebraicGeometry.IsAffine (pullback
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (C.toScheme.fromSpecResidueField y)))

/-- Restriction of global sections along `g` is additive: `g^*(Σ s_i) = Σ g^*(s_i)`
(`sectionPullbackAlong g` is the `⊤`-component of the unit `M → g_* g^* M` of the pullback–pushforward
adjunction, a module map). Stated at the variable level so that the kernel never has to compare
concrete schemes. -/
theorem sectionPullbackAlong_sum {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) {M : Y.Modules}
    {ι : Type*} (s : Finset ι) (f : ι → (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong g (∑ i ∈ s, f i) = ∑ i ∈ s, sectionPullbackAlong g (f i) :=
  map_sum (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤).hom f s

/-- A morphism of `O_X`-modules is additive on global sections, in the `φ.app ⊤` spelling
(`AlgebraicGeometry.Scheme.Modules.app_top_sum` in `TotSectionsPolynomial` is the same fact in the
`(φ.val.app (op ⊤)).hom` spelling; `rw` does not identify the two). -/
theorem AlgebraicGeometry.Scheme.Modules.Hom.app_top_sum' {X : AlgebraicGeometry.Scheme.{u}}
    {A B : X.Modules} (φ : A ⟶ B) {ι : Type*} (s : Finset ι)
    (x : ι → (A.val.obj (Opposite.op ⊤) : Type u)) :
    φ.app ⊤ (∑ i ∈ s, x i) = ∑ i ∈ s, φ.app ⊤ (x i) :=
  map_sum (φ.app ⊤).hom x s

/-- **Sections of bounded ξ-degree are polynomials in a frame coordinate of the fibre.**
Assembled from `totalSpace_fiber_xiMonomial_exists_ringEquiv`.

Setting: `L`, `M` line bundles on the smooth projective curve `C` over `k = k̄`, `p : Tot(L) → C`,
`P ℓ ∈ Γ(Tot(L), p^*M)` (`ℓ = 0, …, N`) with ξ-degree `≤ r₀` (`hP`), `y` a closed point of `C`.
Claim: there are an isomorphism `α₀ : Tot(L)_y ≅ A¹_k` (`Tot(L)_y := p.fiber y`, the scheme-theoretic
fiber), polynomials `Q ℓ ∈ k[t]` of degree `≤ r₀` and a trivialization
`τ : (p.fiberι y)^*(p^*M) ≅ O_{Tot(L)_y}` such that the restriction of `P ℓ` to the fiber, read through
`τ`, is the function `α₀^*(Q ℓ)` (`affineLinePolynomial k (Q ℓ)` pulled back along `α₀.hom`).
Nothing is claimed about `α₀` being a `k`-morphism (the frame coordinate constructed in `totalSpace_fiber_xiMonomial_exists_ringEquiv` is
one, but the user does not need it: see the module docstring).

Proof (as formalized below):
1. `totalSpace_fiber_xiMonomial_exists_ringEquiv`:
   `φ : k[t] ≃+* Γ(Tot(L)_y, O)`, `τ`, and for every `q` and `c ∈ Γ(C, M ⊗ L^{-q})` a constant
   `a q c ∈ k` with `τ ((p.fiberι y)^*(xiMonomial L M q c)) = φ (a q c · t^q)`. (`choose` turns the
   `∃ a` into a function `a`.) `Tot(L)_y` is affine (`totalSpace_fiber_isAffine`), so
   `exists_iso_affineLine_of_ringEquiv` turns `φ` into `α₀ : Tot(L)_y ≅ A¹_k` with
   `α₀^*(affineLinePolynomial k f) = φ f`.
2. Expansion. `P ℓ = Σ_{q ∈ S_ℓ} xiMonomial L M q (c_{ℓ,q})` with `c_{ℓ,q} := xiCoefficient L M (P ℓ) q`
   and `S_ℓ` the (finite) support of `q ↦ c_{ℓ,q}` (`eq_sum_xiMonomial`, `xiCoefficient_finite_support`).
   Put `Q ℓ := Σ_{q ∈ S_ℓ} C (a q c_{ℓ,q}) · X^q`.
3. Degree. For `q ∈ S_ℓ`, `c_{ℓ,q} ≠ 0`, so `q ≤ r₀` by `hP ℓ` (`xiDegree_lt_iff`); hence
   `deg (C a · X^q) ≤ q ≤ r₀` (`degree_C_mul_X_pow_le`) and `deg (Q ℓ) ≤ r₀` (`degree_sum_le`, `sup_le`).
4. Equation. Restriction along `p.fiberι y` and `τ` are additive (`sectionPullbackAlong_sum`,
   `Hom.app_top_sum'`), so `τ ((p.fiberι y)^*(P ℓ)) = Σ_{q ∈ S_ℓ} τ ((p.fiberι y)^*(xiMonomial q c_{ℓ,q}))
   = Σ_{q ∈ S_ℓ} α₀^*(a q c_{ℓ,q} · t^q) = α₀^*(Q ℓ)`, the last step because `f ↦ α₀^*(f)` is the ring
   homomorphism `fiberCoordinate α₀ : k[t] →+* Γ(Tot(L)_y, O)` (`map_sum`).

Edge cases: `r₀ = 0` (all `Q ℓ` constant); `P ℓ = 0` (`S_ℓ = ∅`, `Q ℓ = 0`, degree `⊥ ≤ r₀`); `N = 0`
(one section). `hy` is only passed to `totalSpace_fiber_xiMonomial_exists_ringEquiv` (it needs `κ(y) = k`). -/
theorem totalSpace_fiber_sections_polynomial_exists_coordinate {k : Type u} [Field k] [IsAlgClosed k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) {N r₀ : ℕ}
    (P : Fin (N + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hP : ∀ ℓ, xiDegree L M (P ℓ) ≤ (r₀ : WithBot ℕ))
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    ∃ (α₀ : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y ≅
        AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)))
      (Q : Fin (N + 1) → Polynomial k), (∀ ℓ, (Q ℓ).degree ≤ (r₀ : WithBot ℕ)) ∧
      ∃ τ : (AlgebraicGeometry.Scheme.Modules.pullback
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y)).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback
              (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) ≅
          SheafOfModules.unit ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y).ringCatSheaf,
        ∀ ℓ, τ.hom.app ⊤ (sectionPullbackAlong
            ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y) (P ℓ)) =
          α₀.hom.appTop.hom (affineLinePolynomial k (Q ℓ)) := by
  obtain ⟨φ, τ, h⟩ := totalSpace_fiber_xiMonomial_exists_ringEquiv L M y hy
  have := totalSpace_fiber_isAffine L y
  obtain ⟨α₀, hα₀⟩ := exists_iso_affineLine_of_ringEquiv φ
  choose a ha using h
  refine ⟨α₀, fun ℓ => ∑ q ∈ (xiCoefficient_finite_support L M (P ℓ)).toFinset,
      Polynomial.C (a q (xiCoefficient L M (P ℓ) q)) * Polynomial.X ^ q, fun ℓ => ?_, τ, fun ℓ => ?_⟩
  · refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun q hq => ?_)
    have hne : xiCoefficient L M (P ℓ) q ≠ 0 :=
      (xiCoefficient_finite_support L M (P ℓ)).mem_toFinset.mp hq
    have hqr : q ≤ r₀ := by
      by_contra hn
      exact hne ((xiDegree_lt_iff L M (P ℓ) r₀).mp (hP ℓ) q (Nat.lt_of_not_ge hn))
    exact (Polynomial.degree_C_mul_X_pow_le q _).trans (WithBot.coe_le_coe.mpr hqr)
  · have hsum := congrArg (fun s => τ.hom.app ⊤ (sectionPullbackAlong
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y) s)) (eq_sum_xiMonomial L M (P ℓ))
    refine hsum.trans ?_
    rw [sectionPullbackAlong_sum]
    refine (AlgebraicGeometry.Scheme.Modules.Hom.app_top_sum' τ.hom _ _).trans ?_
    refine (Finset.sum_congr rfl (fun q _ => (ha q (xiCoefficient L M (P ℓ) q)).trans
      (hα₀ _).symm)).trans ?_
    exact (map_sum (fiberCoordinate α₀) _ _).symm

end
