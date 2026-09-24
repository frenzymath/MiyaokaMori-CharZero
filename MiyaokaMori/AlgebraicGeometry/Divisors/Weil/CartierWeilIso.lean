import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorLocalData
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.Divisor
import MiyaokaMori.RingTheory.RegularLocalRing.RegularLocalRingUfd
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyQcqs
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks056s
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.OrdZeroStalkUnit
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorOfLocalDataUnits
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.PrimeDivisorLocalEquation

/-! # The Cartier–Weil isomorphism

On a smooth (locally factorial) variety, Cartier divisors correspond bijectively to Weil divisors: `D ↦ [D]`
is a group isomorphism `CDiv(X) ≅ Div(X)` (Hartshorne II.6.11).

Hypotheses (Hartshorne II.6.11): `X` integral, separated, Noetherian and locally factorial.
`SmoothProjectiveVariety k` satisfies all of these: the `Variety` fields give integral (`integral`), separated
(`separated`) and of finite type over `k` (`finiteType`; over a field this gives locally Noetherian and
quasi-compact, hence Noetherian), and the `smooth` field gives locally factorial through "smooth implies
regular" (Stacks 056S) and "regular local rings are UFDs" (Hartshorne Remark 6.11.1A, Matsumura Th. 48;
Auslander–Buchsbaum). The bijectivity is split, following Hartshorne's proof, into injectivity and
surjectivity; neither uses algebraic Hartogs (II.6.3A) but the route through affine opens and local rings
that are UFDs (`OrdZeroStalkUnit`, `CartierDivisorOfLocalDataUnits`, `PrimeDivisorLocalEquation`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The finiteness in step 2 of Hartshorne II.6.11: the Weil cycle of `D` has nonzero coefficient at only finitely
many prime divisors. The underlying cycle of `weilCycle` has locally finite support; the variety is
quasi-compact (`Variety.compactSpace`), so `AlgebraicGeometry.Intersection.cycle_finiteSupport` gives finite support;
the support on the subtype of prime divisors is its preimage under the injective `Subtype.val`. This is
Hartshorne's "The sum is finite because `X` is noetherian!". -/
theorem cartierToWeilHom_support_finite {k : Type u} [Field k] (X : SmoothProjectiveVariety k)
    (D : CartierDivisor X.toVariety) :
    (Function.support (fun Z : {Z : X.toScheme // X.toScheme.IsPrimeDivisor Z} =>
      (CartierDivisor.weilCycle X.toVariety D :
        AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) Z.1)).Finite := by
  letI : CompactSpace X.toScheme := Variety.compactSpace X.toVariety
  have h := AlgebraicGeometry.Intersection.cycle_finiteSupport
    (CartierDivisor.weilCycle X.toVariety D : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ)
  exact Set.Finite.preimage Subtype.val_injective.injOn h

/-- The finitely supported coefficient function `Z ↦ [D](Z)`. -/
noncomputable def cartierToWeilFinsupp {k : Type u} [Field k] (X : SmoothProjectiveVariety k)
    (D : CartierDivisor X.toVariety) :
    {Z : X.toScheme // X.toScheme.IsPrimeDivisor Z} →₀ ℤ :=
  Finsupp.ofSupportFinite
    (fun Z : {Z : X.toScheme // X.toScheme.IsPrimeDivisor Z} =>
      (CartierDivisor.weilCycle X.toVariety D :
        AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) Z.1)
    (cartierToWeilHom_support_finite X D)

@[simp]
theorem cartierToWeilFinsupp_apply {k : Type u} [Field k] (X : SmoothProjectiveVariety k)
    (D : CartierDivisor X.toVariety) (Z : {Z : X.toScheme // X.toScheme.IsPrimeDivisor Z}) :
    cartierToWeilFinsupp X D Z =
      (CartierDivisor.weilCycle X.toVariety D :
        AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) Z.1 := rfl

theorem cartierToWeilFinsupp_zero {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    cartierToWeilFinsupp X 0 = 0 := by
  have h0 : CartierDivisor.weilCycle X.toVariety 0 = 0 := by
    have h := CartierDivisor.weilCycle_add X.toVariety 0 0
    rw [add_zero] at h
    exact (add_left_cancel (a := CartierDivisor.weilCycle X.toVariety 0)
      (b := 0) (c := CartierDivisor.weilCycle X.toVariety 0)
      (by rw [add_zero]; exact h)).symm
  ext Z
  rw [cartierToWeilFinsupp_apply, h0]
  simp

theorem cartierToWeilFinsupp_add {k : Type u} [Field k] (X : SmoothProjectiveVariety k)
    (D E : CartierDivisor X.toVariety) :
    cartierToWeilFinsupp X (D + E) = cartierToWeilFinsupp X D + cartierToWeilFinsupp X E := by
  ext Z
  rw [cartierToWeilFinsupp_apply, CartierDivisor.weilCycle_add]
  simp

/-- The underlying function of `D ↦ Σ_Z [D](Z)·Z`. -/
noncomputable def cartierToWeilFun {k : Type u} [Field k] (X : SmoothProjectiveVariety k)
    (D : CartierDivisor X.toVariety) : X.toScheme.WeilDivisor :=
  (FreeAbelianGroup.equivFinsupp _).symm (cartierToWeilFinsupp X D)

/-- The coefficient formula: the coefficient of `cartierToWeilFun` at a prime divisor `Z` is the coefficient of
`weilCycle` at `Z` (`FreeAbelianGroup.coeff x = Finsupp.applyAddHom x ∘ toFinsupp` and
`toFinsupp (toFreeAbelianGroup f) = f`, `FreeAbelianGroup.toFinsupp_toFreeAbelianGroup`). -/
theorem cartierToWeilFun_coeff {k : Type u} [Field k] (X : SmoothProjectiveVariety k)
    (D : CartierDivisor X.toVariety) (Z : X.toScheme) (hZ : X.toScheme.IsPrimeDivisor Z) :
    FreeAbelianGroup.coeff (⟨Z, hZ⟩ : {Z : X.toScheme // X.toScheme.IsPrimeDivisor Z})
        (cartierToWeilFun X D) =
      (CartierDivisor.weilCycle X.toVariety D :
        AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) Z := by
  show ((FreeAbelianGroup.toFinsupp (cartierToWeilFun X D)) ⟨Z, hZ⟩) = _
  rw [cartierToWeilFun, FreeAbelianGroup.equivFinsupp_symm_apply,
    FreeAbelianGroup.toFinsupp_toFreeAbelianGroup]
  rfl

theorem cartierToWeilFun_zero {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    cartierToWeilFun X 0 = 0 := by
  rw [cartierToWeilFun, cartierToWeilFinsupp_zero]
  exact map_zero _

theorem cartierToWeilFun_add {k : Type u} [Field k] (X : SmoothProjectiveVariety k)
    (D E : CartierDivisor X.toVariety) :
    cartierToWeilFun X (D + E) = cartierToWeilFun X D + cartierToWeilFun X E := by
  rw [cartierToWeilFun, cartierToWeilFinsupp_add]
  exact map_add _ _ _

/-- The forward map `D ↦ Σ_Z [D](Z)·Z`: the coefficient at a prime divisor `Z` is the value at `Z` of the Weil
cycle `CartierDivisor.weilCycle` (the `ord_Z` of a local equation); the Weil divisor group is the free
abelian group on prime divisors, obtained from the finitely supported function through Mathlib's
`FreeAbelianGroup.equivFinsupp`. -/

noncomputable def cartierToWeilHom {k : Type*} [Field k] (X : SmoothProjectiveVariety k) :
    CartierDivisor X.toVariety →+ X.toScheme.WeilDivisor where
  toFun D := cartierToWeilFun X D
  map_zero' := cartierToWeilFun_zero X
  map_add' := cartierToWeilFun_add X

@[simp]
theorem cartierToWeilHom_apply {k : Type u} [Field k] (X : SmoothProjectiveVariety k)
    (D : CartierDivisor X.toVariety) : cartierToWeilHom X D = cartierToWeilFun X D := rfl

/-- Injectivity (step 3 of Hartshorne II.6.11), without algebraic Hartogs.

Source: Hartshorne, *Algebraic Geometry*, Prop. II.6.11, end of the first paragraph of the proof. Hartshorne
uses II.6.3A (algebraic Hartogs); here the route is "affine opens and local rings that are UFDs"
(`OrdZeroStalkUnit` and the unit criterion for locally factorial rings).

Proof: suppose `cartierToWeilHom X D = 0`. Take local equation data `{(U_i, f_i)}` of `D`
(`cartierDivisor_exists_localData`). By `cartierToWeilFun_coeff` and `weilCycle_ofLocalData`,
`ord_Z(f_i) = 0` for every prime divisor `Z ∈ U_i`. `X` smooth implies regular (Stacks 056S), so the local
rings are UFDs (regular local rings are UFDs). For every `x ∈ U_i`,
`exists_units_stalk_algebraMap_eq_of_forall_ord_eq_zero` gives `f_i ∈ O_{X,x}^×` (on an affine
neighbourhood `V` of `x`, `O_{X,x} = Γ(V)_𝔪`, `f_i` is a unit at every height-one prime of `Γ(V)`, and in a
UFD a reduced fraction whose numerator and denominator have no prime factors is a unit). Then
`ofLocalData_eq_zero_of_forall_units` gives `D = 0` (`f_i` is the germ of an element of `Γ(U_i, O)^×`, which
is `1` in the quotient sheaf `𝒦^*/O^*`). Conclude by `injective_iff_map_eq_zero`. -/
theorem cartierToWeilHom_injective {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    Function.Injective (cartierToWeilHom X) := by
  rw [injective_iff_map_eq_zero]
  intro D hD
  obtain ⟨ι, U, f, hUf, hDf⟩ := cartierDivisor_exists_localData X.toVariety D
  -- all coefficients vanish: at a prime divisor Z, [D](Z) is the coefficient of cartierToWeilHom D, which is 0
  have hcoeff : ∀ z : X.toScheme, Order.coheight z = 1 →
      (CartierDivisor.weilCycle X.toVariety D :
        AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) z = 0 := by
    intro z hz
    have hz' : X.toScheme.IsPrimeDivisor z := hz
    rw [← cartierToWeilFun_coeff X D z hz', ← cartierToWeilHom_apply, hD]
    exact map_zero _
  -- smooth implies regular implies the local rings are UFDs
  have hreg : X.toScheme.IsRegular :=
    AlgebraicGeometry.isRegular_of_smoothOver X.toScheme X.smooth
  have hufd : ∀ x : X.toScheme, UniqueFactorizationMonoid (X.toScheme.presheaf.stalk x) :=
    fun x => by
      have := hreg.isRegularLocalRing_stalk x
      exact IsRegularLocalRing.uniqueFactorizationMonoid _
  rw [hDf]
  apply CartierDivisor.ofLocalData_eq_zero_of_forall_units U f hUf
  intro i x hx
  apply AlgebraicGeometry.Scheme.exists_units_stalk_algebraMap_eq_of_forall_ord_eq_zero hufd
    (U i) hx (f i).ne_zero
  intro z hz hzc
  have h0 := hcoeff z hzc
  rw [hDf, CartierDivisor.weilCycle_ofLocalData X.toVariety U f hUf i z hz] at h0
  exact h0

/-- The core of step 4 of Hartshorne II.6.11 (surjectivity on generators): every prime divisor `Z` is the Weil
cycle of some Cartier divisor `D` (`[D](Z) = 1`, `0` at the other prime divisors).

Source: Hartshorne, *Algebraic Geometry*, Prop. II.6.11, second paragraph of the proof ("Conversely, let `D`
be a Weil divisor…"), with II.6.2 (height-one primes of a UFD are principal, Stacks 0AFT).

Proof: for every point `x`: if `Z ⤳ x`, `exists_functionField_ord_eq_ite` (`PrimeDivisorLocalEquation`)
gives `g_x ∈ K(X)^×` and an open neighbourhood `U_x` with `ord_z(g_x) = [z = Z]` at the prime divisors `z`
of `U_x`; otherwise take `U_x := X ∖ closure{Z}` and `g_x := 1`. `{(U_x, g_x)}` is Cartier local data: at the
prime divisors of `U_x ∩ U_y`, `ord(g_x/g_y) = 0`, so `g_x/g_y` is stalkwise a unit by
`exists_units_stalk_algebraMap_eq_of_forall_ord_eq_zero` (`OrdZeroStalkUnit`). Put `D := ofLocalData U g`;
`weilCycle_ofLocalData` gives `[D](z) = ord_z(g_z) = [z = Z]`. -/
theorem exists_cartierDivisor_weilCycle_eq_single {k : Type u} [Field k]
    (X : SmoothProjectiveVariety k) (Z : X.toScheme) (hZ : X.toScheme.IsPrimeDivisor Z) :
    ∃ D : CartierDivisor X.toVariety, ∀ z : X.toScheme, Order.coheight z = 1 →
      (z = Z → (CartierDivisor.weilCycle X.toVariety D :
        AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) z = 1) ∧
      (z ≠ Z → (CartierDivisor.weilCycle X.toVariety D :
        AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) z = 0) := by
  have hreg : X.toScheme.IsRegular :=
    AlgebraicGeometry.isRegular_of_smoothOver X.toScheme X.smooth
  have hufd : ∀ x : X.toScheme, UniqueFactorizationMonoid (X.toScheme.presheaf.stalk x) :=
    fun x => by
      have := hreg.isRegularLocalRing_stalk x
      exact IsRegularLocalRing.uniqueFactorizationMonoid _
  have hZc : Order.coheight Z = 1 := hZ
  -- the local equation at each point
  have hloc : ∀ x : X.toScheme, ∃ g : X.toScheme.functionField, g ≠ 0 ∧
      ∃ U : X.toScheme.Opens, x ∈ U ∧ ∀ z ∈ U, Order.coheight z = 1 →
        (z = Z → X.toScheme.ord g z = 1) ∧ (z ≠ Z → X.toScheme.ord g z = 0) := by
    intro x
    by_cases hZx : Z ⤳ x
    · exact AlgebraicGeometry.Scheme.exists_functionField_ord_eq_ite hufd hZc hZx
    · refine ⟨1, one_ne_zero,
        ⟨(closure ({Z} : Set X.toScheme))ᶜ, isClosed_closure.isOpen_compl⟩, ?_, ?_⟩
      · exact fun hx => hZx (specializes_iff_mem_closure.mpr hx)
      · intro z hz hzc
        refine ⟨fun hzZ => ?_, fun _ => AlgebraicGeometry.Scheme.ord_one_eq_zero z⟩
        exact absurd (hzZ ▸ subset_closure rfl : z ∈ closure ({Z} : Set X.toScheme)) hz
  choose g hg U hxU hord using hloc
  let f : X.toScheme → (X.toScheme.functionField)ˣ := fun x => Units.mk0 (g x) (hg x)
  have hratio : ∀ (x y w : X.toScheme), w ∈ U x → w ∈ U y →
      ((f x / f y : (X.toScheme.functionField)ˣ) : X.toScheme.functionField) ∈
        Set.range (fun v : (X.toScheme.presheaf.stalk w)ˣ =>
          algebraMap (X.toScheme.presheaf.stalk w) X.toScheme.functionField v) := by
    intro x y w hwx hwy
    obtain ⟨v, hv⟩ :=
      AlgebraicGeometry.Scheme.exists_units_stalk_algebraMap_eq_of_forall_ord_eq_zero hufd
        (U x ⊓ U y) (⟨hwx, hwy⟩ : w ∈ U x ⊓ U y) (f := g x / g y) (div_ne_zero (hg x) (hg y))
        (by
          intro z hz hzc
          rw [AlgebraicGeometry.Scheme.ord_div_eq_sub (hg x) (hg y)]
          by_cases hzZ : z = Z
          · rw [(hord x z hz.1 hzc).1 hzZ, (hord y z hz.2 hzc).1 hzZ, sub_self]
          · rw [(hord x z hz.1 hzc).2 hzZ, (hord y z hz.2 hzc).2 hzZ, sub_self])
    refine ⟨v, ?_⟩
    show algebraMap (X.toScheme.presheaf.stalk w) X.toScheme.functionField (v : X.toScheme.presheaf.stalk w) = _
    rw [hv]
    simp [f]
  have hUf : CartierDivisor.IsLocalData U f := by
    refine ⟨?_, ?_⟩
    · exact top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩
    · intro x y w hw
      exact ⟨hratio x y w hw.1 hw.2, hratio y x w hw.2 hw.1⟩
  refine ⟨CartierDivisor.ofLocalData U f, fun z hzc => ?_⟩
  rw [CartierDivisor.weilCycle_ofLocalData X.toVariety U f hUf z z (hxU z)]
  exact hord z z (hxU z) hzc

/-- Surjectivity (step 4 of Hartshorne II.6.11; second paragraph of the proof).

Proof: `Div(X)` is the free abelian group on prime divisors, so a homomorphism onto it is surjective as soon
as every generator `[Z]` is in the image: `exists_cartierDivisor_weilCycle_eq_single` gives `D_Z` whose Weil
cycle is `1` at `Z` and `0` at the other prime divisors, and comparing coefficients (`cartierToWeilFun_coeff`)
gives `cartierToWeilHom X D_Z = FreeAbelianGroup.of Z`. With `φ := FreeAbelianGroup.lift (Z ↦ D_Z)`,
`cartierToWeilHom ∘ φ` is the identity on generators, hence the identity, so `W = cartierToWeilHom (φ W)`. -/
theorem cartierToWeilHom_surjective {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    Function.Surjective (cartierToWeilHom X) := by
  classical
  have hgen : ∀ Z : {Z : X.toScheme // X.toScheme.IsPrimeDivisor Z},
      ∃ D : CartierDivisor X.toVariety, cartierToWeilHom X D = FreeAbelianGroup.of Z := by
    intro Z
    obtain ⟨D, hD⟩ := exists_cartierDivisor_weilCycle_eq_single X Z.1 Z.2
    refine ⟨D, ?_⟩
    apply (FreeAbelianGroup.equivFinsupp _).injective
    ext W
    have hL : (FreeAbelianGroup.equivFinsupp _ (cartierToWeilHom X D)) W =
        (CartierDivisor.weilCycle X.toVariety D :
          AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) W.1 :=
      cartierToWeilFun_coeff X D W.1 W.2
    have hR : (FreeAbelianGroup.equivFinsupp _ (FreeAbelianGroup.of Z)) W =
        if Z = W then 1 else 0 := by
      rw [FreeAbelianGroup.equivFinsupp_apply, FreeAbelianGroup.toFinsupp_of, Finsupp.single_apply]
    rw [hL, hR]
    by_cases hW : Z = W
    · rw [if_pos hW]
      exact (hD W.1 W.2).1 (congrArg Subtype.val hW.symm)
    · rw [if_neg hW]
      exact (hD W.1 W.2).2 (fun h => hW (Subtype.ext h.symm))
  choose D hD using hgen
  let φ : X.toScheme.WeilDivisor →+ CartierDivisor X.toVariety := FreeAbelianGroup.lift D
  have hφ : (cartierToWeilHom X).comp φ = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro Z
    show cartierToWeilHom X (FreeAbelianGroup.lift D (FreeAbelianGroup.of Z)) = FreeAbelianGroup.of Z
    rw [FreeAbelianGroup.lift_apply_of, hD]
  intro W
  refine ⟨φ W, ?_⟩
  have := congrArg (fun ψ : X.toScheme.WeilDivisor →+ X.toScheme.WeilDivisor => ψ W) hφ
  simpa using this

/-- On a smooth (locally factorial) variety, `D ↦ [D]` is bijective (Hartshorne II.6.11). -/
theorem cartierToWeilHom_bijective {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    Function.Bijective (cartierToWeilHom X) :=
  ⟨cartierToWeilHom_injective X, cartierToWeilHom_surjective X⟩

/-- The Cartier–Weil isomorphism `CDiv(X) ≅ Div(X)`; the inverse is given by `AddEquiv.ofBijective`. -/
noncomputable def cartierWeilEquiv {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    CartierDivisor X.toVariety ≃+ X.toScheme.WeilDivisor :=
  AddEquiv.ofBijective (cartierToWeilHom X) (cartierToWeilHom_bijective X)

theorem cartierWeilEquiv_apply {k : Type u} [Field k] (X : SmoothProjectiveVariety k)
    (D : CartierDivisor X.toVariety) (Z : X.toScheme) (hZ : X.toScheme.IsPrimeDivisor Z) :
    FreeAbelianGroup.coeff (⟨Z, hZ⟩ : {Z : X.toScheme // X.toScheme.IsPrimeDivisor Z}) (cartierWeilEquiv X D) =
      (CartierDivisor.weilCycle X.toVariety D : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) Z := by
  show FreeAbelianGroup.coeff _ (cartierToWeilHom X D) = _
  exact cartierToWeilFun_coeff X D Z hZ

end
