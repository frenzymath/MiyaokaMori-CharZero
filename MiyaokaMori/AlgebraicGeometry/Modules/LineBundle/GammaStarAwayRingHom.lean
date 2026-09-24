import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.GammaStarComponent

/-! # The ring map from the localized section ring to functions on a nonvanishing locus

**The ring map `Γ_*(X, L)_{(x)} → Γ(U, O_X)`, `a/x^n ↦ a · x^{-n}`** (Stacks 01PZ, the sentence
"the ring map `S_{(s)} → Γ(X_s, O_X)` sending `a/s^n` to `a ⊗ s^{-n}`").

Let `x ∈ Γ_*(X, L)_m` be homogeneous with section `x_m := gammaStarComponent L x m ∈ Γ(X, L^{⊗m})`,
and let `U ≤ X_{x_m}` be an open on which `x_m` does not vanish. Every power `x^k` restricts to a
frame of `L^{⊗km}` on `U` (`nonvanishingLocus_le_nonvanishingLocus_pow`), so for a homogeneous
fraction `c = num/den` (`den ∈ powers x`, both of degree `deg`) the coordinate

  `awayToSectionsAux c := coord_{den|_U}(num|_U) ∈ Γ(X, U)`,   i.e. the unique `φ` with `φ • den|_U = num|_U`,

is defined. It descends to `HomogeneousLocalization.Away 𝒜 x` and is a ring homomorphism
`awayToSections L hx hU : Away 𝒜 x →+* Γ(X, U)`. All ring-hom laws are proved from the
characterizing equation `φ • den = num` together with `coord` uniqueness, using
`gammaStarComponent_mul` (components of products are graded products) and the bilinearity of the
graded product `sectionsGMul` (`sectionsGMul_smul_smul`, module `Stacks01q1_GammaStarComponent`).

Main statements:
* `awayToSections_mk_smul` / `awayToSections_mk_unique`: `ψ(a/x^n) • x^n|_U = a|_U`, and this
  determines `ψ(a/x^n)`;
* `awayToSections_res`: compatibility with restriction `U' ≤ U`;
* `awayToSections_awayMap`: compatibility with `awayMap : Away 𝒜 x → Away 𝒜 (x * t)` on
  `U' ≤ X_{xt}` (the transition maps of the charts of Stacks 01PZ agree on overlaps).

Edge cases: if `x = 0` (or `x^k = 0`) then `U = ⊥` and `Γ(X, U)` is a singleton, so all statements
are trivially true; no positivity of the degree is needed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-! ## Generic frame helpers -/

/-- Multiplication by a frame is injective on functions. -/
theorem IsFrame.smul_injective {M : X.Modules} {U : X.Opens} {e : Γ(M, U)} (hf : IsFrame M U e) :
    Function.Injective (fun r : Γ(X, U) => r • e) := by
  have h := (hf U le_rfl).1
  rwa [res_self] at h

/-- A frame `e` on `U` with `e = 0` forces `Γ(X, U)` to be a singleton. -/
theorem IsFrame.subsingleton_of_eq_zero {M : X.Modules} {U : X.Opens} {e : Γ(M, U)}
    (hf : IsFrame M U e) (he : e = 0) : Subsingleton Γ(X, U) := by
  refine ⟨fun r r' => hf.smul_injective ?_⟩
  show r • e = r' • e
  rw [he, smul_zero, smul_zero]

theorem res_add (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (a b : Γ(M, W)) :
    M.res h (a + b) = M.res h a + M.res h b :=
  map_add _ a b

theorem res_zero (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) :
    M.res h (0 : Γ(M, W)) = 0 :=
  map_zero _

variable (L : X.Modules) [L.IsLineBundle]

/-- `X_{x_m} ≤ X_{(x^n)_{n•m}}` for a homogeneous `x` of degree `m`. -/
theorem nonvanishingLocus_le_nonvanishingLocus_pow {x : AlgebraicGeometry.Scheme.Modules.gammaStar L}
    {m : ℕ} (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m) ≤
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (n • m)).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (x ^ n) (n • m)) := by
  have h := nonvanishingLocus_le_nonvanishingLocus_pow_gammaStarOf L m
    (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m) n
  rwa [gammaStarOf_gammaStarComponent L hx] at h

/-- `X_{(x^n)_{n•m}} = X_{x_m}` for `n > 0`. -/
theorem nonvanishingLocus_pow {x : AlgebraicGeometry.Scheme.Modules.gammaStar L}
    {m : ℕ} (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m) {n : ℕ} (hn : 0 < n) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L (n • m)).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (x ^ n) (n • m)) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m) := by
  have h := nonvanishingLocus_pow_gammaStarOf L m
    (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m) hn
  rwa [gammaStarOf_gammaStarComponent L hx] at h

/-- Elements of `powers x` restrict to frames on any `U ≤ X_{x_m}`. -/
theorem isFrame_res_of_mem_powers {x : AlgebraicGeometry.Scheme.Modules.gammaStar L} {m : ℕ}
    (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m) {U : X.Opens}
    (hU : U ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m))
    {y : AlgebraicGeometry.Scheme.Modules.gammaStar L} {k : ℕ}
    (hy : y ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L k) (hyx : y ∈ Submonoid.powers x) :
    IsFrame (AlgebraicGeometry.Scheme.Modules.tensorPow L k) U
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L k).res le_top
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L y k)) := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hyx
  apply isFrame_res_of_le_nonvanishingLocus
  rw [nonvanishingLocus_gammaStarComponent_congr L hy (SetLike.pow_mem_graded n hx)]
  exact hU.trans (nonvanishingLocus_le_nonvanishingLocus_pow L hx n)

/-- The frame `(x^n)|_U` on `U ≤ X_{x_m}`. -/
theorem isFrame_res_pow {x : AlgebraicGeometry.Scheme.Modules.gammaStar L} {m : ℕ}
    (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m) {U : X.Opens}
    (hU : U ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m)) (n : ℕ) :
    IsFrame (AlgebraicGeometry.Scheme.Modules.tensorPow L (n • m)) U
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n • m)).res le_top
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (x ^ n) (n • m))) :=
  isFrame_res_of_le_nonvanishingLocus _ _ (hU.trans (nonvanishingLocus_le_nonvanishingLocus_pow L hx n))

/-! ## The map on homogeneous fractions -/

section

variable {x : AlgebraicGeometry.Scheme.Modules.gammaStar L} {m : ℕ}
  (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m) {U : X.Opens}
  (hU : U ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
    (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m))

/-- `num/den ↦ coord_{den|_U}(num|_U)`. -/
def awayToSectionsAux
    (c : HomogeneousLocalization.NumDenSameDeg (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
      (Submonoid.powers x)) : Γ(X, U) :=
  (isFrame_res_of_mem_powers L hx hU c.den.2 c.den_mem).coord le_rfl
    ((AlgebraicGeometry.Scheme.Modules.tensorPow L c.deg).res le_top
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c.num c.deg))

/-- The characterizing equation `φ • den|_U = num|_U`. -/
theorem awayToSectionsAux_smul
    (c : HomogeneousLocalization.NumDenSameDeg (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
      (Submonoid.powers x)) :
    awayToSectionsAux L hx hU c • (AlgebraicGeometry.Scheme.Modules.tensorPow L c.deg).res (le_top : U ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c.den c.deg) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L c.deg).res le_top
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c.num c.deg) := by
  have h := (isFrame_res_of_mem_powers L hx hU c.den.2 c.den_mem).coord_smul_frame le_rfl
    ((AlgebraicGeometry.Scheme.Modules.tensorPow L c.deg).res le_top
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c.num c.deg))
  rwa [res_self] at h

theorem awayToSectionsAux_unique
    (c : HomogeneousLocalization.NumDenSameDeg (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
      (Submonoid.powers x)) (r : Γ(X, U))
    (hr : r • (AlgebraicGeometry.Scheme.Modules.tensorPow L c.deg).res (le_top : U ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c.den c.deg) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L c.deg).res le_top
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c.num c.deg)) :
    awayToSectionsAux L hx hU c = r := by
  apply (isFrame_res_of_mem_powers L hx hU c.den.2 c.den_mem).coord_unique
  rwa [res_self]

/-- Scalars pull out of the graded product (left factor). -/
theorem sectionsGMul_smul_left (V : X.Opens) {p q : ℕ} (α : Γ(X, V))
    (a : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L p, V))
    (b : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L q, V)) :
    (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul V (α • a) b =
      @HSMul.hSMul Γ(X, V) Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (p + q), V)
        Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (p + q), V) _ α
        ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul V a b) := by
  have h := sectionsGMul_smul_smul L V α 1 a b
  rwa [one_smul, mul_one] at h

/-- Scalars pull out of the graded product (right factor). -/
theorem sectionsGMul_smul_right (V : X.Opens) {p q : ℕ} (β : Γ(X, V))
    (a : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L p, V))
    (b : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L q, V)) :
    (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul V a (β • b) =
      @HSMul.hSMul Γ(X, V) Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (p + q), V)
        Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (p + q), V) _ β
        ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul V a b) := by
  have h := sectionsGMul_smul_smul L V 1 β a b
  rwa [one_smul, one_mul] at h

/-- Restriction of the component of a product is the graded product of the restricted
components. -/
theorem res_gammaStarComponent_mul {y z : AlgebraicGeometry.Scheme.Modules.gammaStar L} {p q : ℕ}
    (hy : y ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L p)
    (hz : z ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L q) (V : X.Opens) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L (p + q)).res (le_top : V ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (y * z) (p + q)) =
      (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul V
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L p).res le_top
          (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L y p))
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L q).res le_top
          (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L z q)) := by
  rw [gammaStarComponent_mul L hy hz, res_sectionsGMul]

/-- Well-definedness on the quotient: equal fractions have equal coordinates. -/
theorem awayToSectionsAux_eq_of_embedding_eq
    (c c' : HomogeneousLocalization.NumDenSameDeg (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
      (Submonoid.powers x))
    (h : HomogeneousLocalization.NumDenSameDeg.embedding _ _ c =
      HomogeneousLocalization.NumDenSameDeg.embedding _ _ c') :
    awayToSectionsAux L hx hU c = awayToSectionsAux L hx hU c' := by
  unfold HomogeneousLocalization.NumDenSameDeg.embedding at h
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h
  obtain ⟨⟨u, hu⟩, hc⟩ := h
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hu
  simp only at hc
  -- `hc : x^k * (den' * num) = x^k * (den * num')`
  set α := awayToSectionsAux L hx hU c with hα
  set β := awayToSectionsAux L hx hU c' with hβ
  have hα' := awayToSectionsAux_smul L hx hU c
  have hβ' := awayToSectionsAux_smul L hx hU c'
  rw [← hα] at hα'
  rw [← hβ] at hβ'
  have hk := SetLike.pow_mem_graded k hx
  have hden := c.den.2
  have hden' := c'.den.2
  have hnum := c.num.2
  have hnum' := c'.num.2
  -- take the `(k•m + (deg' + deg))`-component of `hc`, restricted to `U`
  have hc' := congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorPow L (k • m + (c'.deg + c.deg))).res
    (le_top : U ≤ ⊤) (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L z (k • m + (c'.deg + c.deg)))) hc
  rw [mul_comm (c.den : AlgebraicGeometry.Scheme.Modules.gammaStar L) c'.num,
    res_gammaStarComponent_mul L hk (SetLike.mul_mem_graded hden' hnum),
    res_gammaStarComponent_mul L hk (SetLike.mul_mem_graded hnum' hden),
    res_gammaStarComponent_mul L hden' hnum, res_gammaStarComponent_mul L hnum' hden,
    ← hα', ← hβ', sectionsGMul_smul_right, sectionsGMul_smul_left] at hc'
  set P : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (c'.deg + c.deg), U) :=
    (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul U
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L c'.deg).res le_top
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c'.den c'.deg))
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L c.deg).res le_top
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c.den c.deg)) with hP
  have e1 := sectionsGMul_smul_right L U α
    ((AlgebraicGeometry.Scheme.Modules.tensorPow L (k • m)).res le_top
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (x ^ k) (k • m))) P
  have e2 := sectionsGMul_smul_right L U β
    ((AlgebraicGeometry.Scheme.Modules.tensorPow L (k • m)).res le_top
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (x ^ k) (k • m))) P
  rw [e1, e2] at hc'
  -- the frame `x^k · (den' · den)` on `U`
  have hF : IsFrame (AlgebraicGeometry.Scheme.Modules.tensorPow L (k • m + (c'.deg + c.deg))) U
      ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul U
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L (k • m)).res le_top
          (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (x ^ k) (k • m)))
        ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul U
          ((AlgebraicGeometry.Scheme.Modules.tensorPow L c'.deg).res le_top
            (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c'.den c'.deg))
          ((AlgebraicGeometry.Scheme.Modules.tensorPow L c.deg).res le_top
            (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c.den c.deg)))) := by
    have h1 := isFrame_res_sectionsGMul L (isFrame_res_pow L hx hU k)
      (isFrame_res_sectionsGMul L (isFrame_res_of_mem_powers L hx hU hden' c'.den_mem)
        (isFrame_res_of_mem_powers L hx hU hden c.den_mem))
    have e3 := res_sectionsGMul L (U := U)
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (x ^ k) (k • m))
      ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul ⊤
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c'.den c'.deg)
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c.den c.deg) :
        Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (c'.deg + c.deg), ⊤))
    have e4 := res_sectionsGMul L (U := U)
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c'.den c'.deg)
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L c.den c.deg)
    rw [e3, e4] at h1
    exact h1
  exact hF.smul_injective hc'

end

/-! ## The ring homomorphism -/

variable {x : AlgebraicGeometry.Scheme.Modules.gammaStar L} {m : ℕ}
  (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m) {U : X.Opens}
  (hU : U ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
    (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m))

/-- **The ring map `Γ_*(X, L)_{(x)} → Γ(U, O_X)`, `a/x^n ↦ a · x^{-n}`** (Stacks 01PZ). -/
def awayToSections :
    HomogeneousLocalization.Away (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x →+* Γ(X, U) where
  toFun := Quotient.lift (awayToSectionsAux L hx hU) (awayToSectionsAux_eq_of_embedding_eq L hx hU)
  map_one' := by
    show awayToSectionsAux L hx hU 1 = 1
    apply awayToSectionsAux_unique
    rw [one_smul]
    rfl
  map_mul' := by
    intro a b
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective a
    obtain ⟨c', rfl⟩ := HomogeneousLocalization.mk_surjective b
    rw [← HomogeneousLocalization.mk_mul]
    show awayToSectionsAux L hx hU (c * c') =
      awayToSectionsAux L hx hU c * awayToSectionsAux L hx hU c'
    apply awayToSectionsAux_unique
    show (awayToSectionsAux L hx hU c * awayToSectionsAux L hx hU c') •
        (AlgebraicGeometry.Scheme.Modules.tensorPow L (c.deg + c'.deg)).res le_top
          (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (c.den * c'.den) (c.deg + c'.deg)) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (c.deg + c'.deg)).res le_top
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (c.num * c'.num) (c.deg + c'.deg))
    rw [res_gammaStarComponent_mul L c.den.2 c'.den.2, res_gammaStarComponent_mul L c.num.2 c'.num.2,
      ← sectionsGMul_smul_smul, awayToSectionsAux_smul, awayToSectionsAux_smul]
  map_zero' := by
    show awayToSectionsAux L hx hU 0 = 0
    apply awayToSectionsAux_unique
    show (0 : Γ(X, U)) • _ = (AlgebraicGeometry.Scheme.Modules.tensorPow L 0).res le_top
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L 0 0)
    rw [zero_smul, gammaStarComponent_zero, res_zero]
  map_add' := by
    intro a b
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective a
    obtain ⟨c', rfl⟩ := HomogeneousLocalization.mk_surjective b
    rw [← HomogeneousLocalization.mk_add]
    show awayToSectionsAux L hx hU (c + c') =
      awayToSectionsAux L hx hU c + awayToSectionsAux L hx hU c'
    apply awayToSectionsAux_unique
    show (awayToSectionsAux L hx hU c + awayToSectionsAux L hx hU c') •
        (AlgebraicGeometry.Scheme.Modules.tensorPow L (c.deg + c'.deg)).res le_top
          (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (c.den * c'.den) (c.deg + c'.deg)) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (c.deg + c'.deg)).res le_top
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (c.den * c'.num + c'.den * c.num)
          (c.deg + c'.deg))
    rw [gammaStarComponent_add, res_add,
      mul_comm (c'.den : AlgebraicGeometry.Scheme.Modules.gammaStar L) c.num,
      res_gammaStarComponent_mul L c.den.2 c'.den.2, res_gammaStarComponent_mul L c.den.2 c'.num.2,
      res_gammaStarComponent_mul L c.num.2 c'.den.2, ← awayToSectionsAux_smul L hx hU c,
      ← awayToSectionsAux_smul L hx hU c', sectionsGMul_smul_right, sectionsGMul_smul_left]
    erw [add_smul]
    exact add_comm _ _

theorem awayToSections_mk
    (c : HomogeneousLocalization.NumDenSameDeg (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
      (Submonoid.powers x)) :
    awayToSections L hx hU (HomogeneousLocalization.mk c) = awayToSectionsAux L hx hU c := rfl

/-- `ψ(a/x^n) • x^n|_U = a|_U`. -/
theorem awayToSections_mk_smul (n : ℕ) (a : AlgebraicGeometry.Scheme.Modules.gammaStar L)
    (ha : a ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L (n • m)) :
    awayToSections L hx hU (HomogeneousLocalization.Away.mk _ hx n a ha) •
        (AlgebraicGeometry.Scheme.Modules.tensorPow L (n • m)).res (le_top : U ≤ ⊤)
          (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (x ^ n) (n • m)) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (n • m)).res le_top
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L a (n • m)) :=
  awayToSectionsAux_smul L hx hU _

/-- `ψ(a/x^n)` is the unique function `r` with `r • x^n|_U = a|_U`. -/
theorem awayToSections_mk_unique (n : ℕ) (a : AlgebraicGeometry.Scheme.Modules.gammaStar L)
    (ha : a ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L (n • m)) (r : Γ(X, U))
    (hr : r • (AlgebraicGeometry.Scheme.Modules.tensorPow L (n • m)).res (le_top : U ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (x ^ n) (n • m)) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (n • m)).res le_top
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L a (n • m))) :
    awayToSections L hx hU (HomogeneousLocalization.Away.mk _ hx n a ha) = r :=
  awayToSectionsAux_unique L hx hU _ r hr

/-- Compatibility with restriction to a smaller open `U' ≤ U`. -/
theorem awayToSections_res {U' : X.Opens} (h : U' ≤ U)
    (z : HomogeneousLocalization.Away (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x) :
    X.presheaf.map (CategoryTheory.homOfLE h).op (awayToSections L hx hU z) =
      awayToSections L hx (h.trans hU) z := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rw [awayToSections_mk, awayToSections_mk]
  symm
  apply awayToSectionsAux_unique
  have h1 := congrArg ((AlgebraicGeometry.Scheme.Modules.tensorPow L c.deg).res h)
    (awayToSectionsAux_smul L hx hU c)
  rwa [res_smul, res_res, res_res] at h1

/-- The graded product of homogeneous sections and the section of the product agree. -/
theorem res_gammaStarComponent_mul' {y z : AlgebraicGeometry.Scheme.Modules.gammaStar L} {p q : ℕ}
    (hy : y ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L p)
    (hz : z ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L q) (V : X.Opens) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L (p + q)).res (le_top : V ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (y * z) (p + q)) =
      (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGMul V
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L p).res le_top
          (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L y p))
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L q).res le_top
          (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L z q)) :=
  res_gammaStarComponent_mul L hy hz V

/-- Transport of the characterizing equation along an equality of degrees. -/
theorem smul_res_gammaStarComponent_congr {K K' : ℕ} (hK : K = K')
    (y a : AlgebraicGeometry.Scheme.Modules.gammaStar L) (V : X.Opens) (r : Γ(X, V)) :
    (r • (AlgebraicGeometry.Scheme.Modules.tensorPow L K).res (le_top : V ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L y K) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L K).res le_top
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L a K)) ↔
    (r • (AlgebraicGeometry.Scheme.Modules.tensorPow L K').res (le_top : V ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L y K') =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L K').res le_top
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L a K')) := by
  subst hK; rfl

include hx in
/-- `X_{(xt)_{m+e}} = X_{x_m} ⊓ X_{t_e}`. -/
theorem nonvanishingLocus_mul {t : AlgebraicGeometry.Scheme.Modules.gammaStar L} {e : ℕ}
    (ht : t ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L e) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L (m + e)).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (x * t) (m + e)) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
          (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m) ⊓
        (AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus
          (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L t e) := by
  rw [gammaStarComponent_mul L hx ht, nonvanishingLocus_sectionsGMul]

omit hU in
/-- **Compatibility with `awayMap`** (the transition maps of the charts of Stacks 01PZ): for
`y = x * t` with `t` homogeneous of degree `e` and `U' ≤ X_{y_{m+e}}`,
`ψ_y(awayMap z) = ψ_x(z)` on `U'`. -/
theorem awayToSections_awayMap {t : AlgebraicGeometry.Scheme.Modules.gammaStar L} {e : ℕ}
    (ht : t ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L e)
    {y : AlgebraicGeometry.Scheme.Modules.gammaStar L} (hy : y = x * t) {U' : X.Opens}
    (hU' : U' ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L (m + e)).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L y (m + e)))
    (hU'x : U' ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m))
    (z : HomogeneousLocalization.Away (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x) :
    awayToSections L (hy ▸ SetLike.mul_mem_graded hx ht) hU'
        (HomogeneousLocalization.awayMap _ ht hy z) =
      awayToSections L hx hU'x z := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hx z
  rw [HomogeneousLocalization.awayMap_mk]
  apply awayToSections_mk_unique
  rw [smul_res_gammaStarComponent_congr L (nsmul_add m e n) _ _ U']
  subst hy
  rw [mul_pow, res_gammaStarComponent_mul L (SetLike.pow_mem_graded n hx) (SetLike.pow_mem_graded n ht),
    res_gammaStarComponent_mul L ha (SetLike.pow_mem_graded n ht), ← sectionsGMul_smul_left,
    awayToSections_mk_smul]

end AlgebraicGeometry.Scheme.Modules

end
