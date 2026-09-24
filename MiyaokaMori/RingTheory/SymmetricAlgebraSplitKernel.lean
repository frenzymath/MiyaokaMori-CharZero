import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.SymmetricAlgebraSplitPolynomialModel

/-! # The kernel of "`T ↦ 0`" on `Sym(R·T ⊕ N)`, `N ≅ R`

Used for `totalSpace.mem_range_lSection_of_not_mem_basicOpen_oCoordinate` (the total space of a line
bundle is affine over the base; Stacks 01O4). Pure commutative algebra on top of
`SymmetricAlgebra.ModuleSplitting` (module `SymmetricAlgebraSplitPolynomialModel`,
`Sym_R(R·T ⊕ N) ≅ (Sym_R N)[X]`).

Setting: `D : ModuleSplitting R M N` (`M = R·T ⊕ N`), `C` an `R`-algebra with `algebraMap R C` bijective, and
`φ : Sym_R M →ₐ[R] C` with `φ(ι T) = 0` and `n ↦ φ(ι (s n))` a bijection `N → C`
(in the application: `M = Γ(W, (O ⊕ L)^∨)`, `N = Γ(W, L^∨)`, `C = Γ(W, O_W)`, `φ` the local piece of the `L`-section,
whose degree-one values on `L^∨` are the trivialization `e₂`).

**Statements.**
* `exists_generator`: `N = R·l` with `φ(ι (s l)) = 1` (`l` the preimage of `1`; every `n` is `r • l` for the `r` with
  `algebraMap r = φ(ι (s n))`, by injectivity).
* `eq_zero_of_mem_symmetricPiece_of_eq_zero`: `E := φ ∘ ofPolyCoeff : Sym_R N → C` is injective on every homogeneous
  piece `Sym^k N = R·(ι l)^k` (`E(algebraMap c · (ι l)^k) = algebraMap c`).
* `mem_span_ι_T_of_mem_symmetricPiece_of_eq_zero` (**the kernel lemma**): for `a ∈ Sym^k M` with `φ a = 0`,
  `a ∈ (ι T)`. Proof: `a = ofPoly p` with `p = toPoly a` homogeneous of degree `k`; `φ(ofPoly p) = Σ_j E(p_j) φ(ι T)^j
  = E(p_0)` (`Polynomial.hom_eval₂`, `eval₂_at_zero`), so `p_0 = 0` by the previous item and `p = X · divX p`
  (`Polynomial.X_mul_divX_add`), whence `a = ι T · ofPoly (divX p)`.

Edge cases: `R = 0` (everything is zero); `k = 0` (`a = algebraMap c`, `φ a = algebraMap c = 0` forces `c = 0`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w

open Polynomial

noncomputable section

namespace SymmetricAlgebra.ModuleSplitting

variable {R : Type u} {M : Type v} {N : Type w} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (D : ModuleSplitting R M N)
variable {C : Type*} [CommRing C] [Algebra R C] (φ : SymmetricAlgebra R M →ₐ[R] C)

/-- `N` is free of rank one on the preimage `l` of `1`: `φ(ι (s l)) = 1` and every `n` is `r • l`. -/
theorem exists_generator (hbij : Function.Bijective (algebraMap R C))
    (hev : Function.Bijective fun n : N => φ (SymmetricAlgebra.ι R M (D.s n))) :
    ∃ l : N, φ (SymmetricAlgebra.ι R M (D.s l)) = 1 ∧ ∀ n : N, ∃ r : R, n = r • l := by
  obtain ⟨l, hl₀⟩ := hev.2 1
  have hl : φ (SymmetricAlgebra.ι R M (D.s l)) = 1 := hl₀
  refine ⟨l, hl, fun n => ?_⟩
  obtain ⟨r, hr⟩ := hbij.2 (φ (SymmetricAlgebra.ι R M (D.s n)))
  refine ⟨r, hev.1 ?_⟩
  show φ (SymmetricAlgebra.ι R M (D.s n)) = φ (SymmetricAlgebra.ι R M (D.s (r • l)))
  rw [LinearMap.map_smul, LinearMap.map_smul, map_smul, hl, Algebra.smul_def, mul_one, hr]

/-- `φ ∘ ofPolyCoeff` is injective on every homogeneous piece of `Sym_R N`. -/
theorem eq_zero_of_mem_symmetricPiece_of_eq_zero (hbij : Function.Bijective (algebraMap R C))
    (hev : Function.Bijective fun n : N => φ (SymmetricAlgebra.ι R M (D.s n)))
    {k : ℕ} {b : SymmetricAlgebra R N} (hb : b ∈ MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece R N k)
    (h : φ (D.ofPolyCoeff b) = 0) : b = 0 := by
  obtain ⟨l, hl, hgen⟩ := exists_generator D φ hbij hev
  have hform : ∃ c : R, b = algebraMap R _ c * (SymmetricAlgebra.ι R N l) ^ k := by
    clear h
    change b ∈ (LinearMap.range (SymmetricAlgebra.ι R N)) ^ k at hb
    induction hb using Submodule.pow_induction_on_left' with
    | algebraMap r => exact ⟨r, by rw [pow_zero, mul_one]⟩
    | add x y i _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := hy
      exact ⟨c + c', by rw [map_add, add_mul]⟩
    | mem_mul m hm i x _ hx =>
      obtain ⟨m, rfl⟩ := hm
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨r, rfl⟩ := hgen m
      refine ⟨r * c, ?_⟩
      rw [LinearMap.map_smul, map_mul, pow_succ, Algebra.smul_def]
      ring
  obtain ⟨c, rfl⟩ := hform
  have hE : φ (D.ofPolyCoeff (algebraMap R _ c * (SymmetricAlgebra.ι R N l) ^ k)) = algebraMap R C c := by
    rw [map_mul, map_pow, AlgHom.commutes, ofPolyCoeff_ι, map_mul, map_pow, AlgHom.commutes, hl, one_pow, mul_one]
  rw [hE] at h
  have hc : c = 0 := hbij.1 (h.trans (map_zero _).symm)
  rw [hc, map_zero, zero_mul]

/-- **The kernel lemma**: `a ∈ Sym^k M` with `φ a = 0` lies in the ideal `(ι T)`. -/
theorem mem_span_ι_T_of_mem_symmetricPiece_of_eq_zero (hbij : Function.Bijective (algebraMap R C))
    (hev : Function.Bijective fun n : N => φ (SymmetricAlgebra.ι R M (D.s n)))
    (hT : φ (SymmetricAlgebra.ι R M D.T) = 0)
    {k : ℕ} {a : SymmetricAlgebra R M} (ha : a ∈ MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece R M k)
    (h : φ a = 0) : a ∈ Ideal.span {SymmetricAlgebra.ι R M D.T} := by
  set p := D.toPoly a with hp
  have hhom : IsHomogPoly k p := D.toPoly_mem_of_mem_symmetricPiece ha
  have ha' : D.ofPoly p = a :=
    congrArg (fun F : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M => F a) D.ofPoly_toPoly
  have hφ : φ (D.ofPoly p) = φ (D.ofPolyCoeff (p.coeff 0)) := by
    rw [ofPoly_apply]
    have h1 := Polynomial.hom_eval₂ p (D.ofPolyCoeff : SymmetricAlgebra R N →+* SymmetricAlgebra R M)
      (φ : SymmetricAlgebra R M →+* C) (SymmetricAlgebra.ι R M D.T)
    have h2 : (φ : SymmetricAlgebra R M →+* C) (SymmetricAlgebra.ι R M D.T) = 0 := hT
    rw [h2, Polynomial.eval₂_at_zero] at h1
    exact h1
  have h0 : p.coeff 0 = 0 :=
    D.eq_zero_of_mem_symmetricPiece_of_eq_zero φ hbij hev (hhom 0).1 (by rw [← hφ, ha']; exact h)
  have hpX : p = Polynomial.X * p.divX := by
    have := Polynomial.X_mul_divX_add p
    rw [h0, map_zero, add_zero] at this
    exact this.symm
  rw [← ha', hpX, map_mul, ofPoly_X]
  exact Ideal.mem_span_singleton.mpr (Dvd.intro _ rfl)

/-- There is an `n` with `φ(ι (s n)) = 1`. -/
theorem exists_ι_s_eq_one (hev : Function.Bijective fun n : N => φ (SymmetricAlgebra.ι R M (D.s n))) :
    ∃ n : N, φ (SymmetricAlgebra.ι R M (D.s n)) = 1 :=
  hev.2 1

end SymmetricAlgebra.ModuleSplitting

end
