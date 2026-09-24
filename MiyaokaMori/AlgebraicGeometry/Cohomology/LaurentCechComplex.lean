import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechAlternatingLocalizationAcyclic

/-! # The Laurent–Čech complex

Let `R` be a commutative ring, `S = R[T_0..T_N]`, `d ∈ ℤ`. We define the Laurent–Čech complex (the purely
algebraic complex in the proof of Stacks 01XT): for `I ⊆ {0..N}`, `T_I = ∏_{i∈I} T_i` (`prodX`),
`S_{T_I} = Localization.Away T_I` (`Loc`), `(S_{T_I})_d` = the `R`-submodule spanned by `a/T_I^j` with `a`
homogeneous of degree `j|I| + d` (`degPiece`), the restriction maps for `I ⊆ J` (`locRes`, `res`), the
cochains `Cochain R N d p = ∏_{σ : Fin (p+1) ↪o Fin (N+1)} (S_{T_σ})_d` with differential `δ` (an instance
of the abstract alternating differential `CechAltAlg.d`), and `δ ∘ δ = 0`.

Proof sketch:
1. `locRes`: `T_I` is invertible in `S_{T_J}` (`T_J = T_{J∖I}·T_I`), `IsLocalization.Away.liftAlgHom`.
2. `locRes_mk`: `a/T_I^j ↦ a·T_{J∖I}^j / T_J^j`; hence `locRes` preserves the degree-`d` piece
   (`locRes_mem_degPiece`, degree `i + j(|J|−|I|) = j|J| + d`).
3. Functoriality `locRes_comp` (`IsLocalization.ringHom_ext`) ⇒ `res_comp` ⇒ `δ_comp` (the abstract
   `CechAltAlg.d_comp_d`).

Encoding: the indices and face maps are **literally** those of `cechComplexAlt` / `CechAltAlg`
(`Fin (p+1) ↪o Fin (N+1)` and `face`), with the preorder `(Finset (Fin (N+1)))ᵒᵈ`; thus the comparison with
the Čech complex of `O(d)` needs only termwise isomorphisms compatible with restriction, the equality of
differentials is a short consequence (`ProjectiveSpaceOver.cechFamilyD_eq_δ`), and the homotopies of
`CechAltAlg.homotopyCochain` can be reused directly.

Source: the first paragraph of the proof of Stacks 01XT.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

namespace LaurentCech

variable (R : Type u) [CommRing R] (N : ℕ)

/-- `T_S = ∏_{i ∈ S} T_i ∈ R[T_0..T_N]`; equal to `1` for `S = ∅`. -/
def prodX (S : Finset (Fin (N + 1))) : MvPolynomial (Fin (N + 1)) R :=
  ∏ i ∈ S, MvPolynomial.X i

/-- `R[T]_{T_S}`. -/
abbrev Loc (S : Finset (Fin (N + 1))) : Type u := Localization.Away (prodX R N S)

variable {R N}

theorem prodX_isHomogeneous (S : Finset (Fin (N + 1))) :
    (prodX R N S).IsHomogeneous S.card := by
  have h := MvPolynomial.IsHomogeneous.prod S (fun i => (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R))
    (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X R i)
  simpa [prodX] using h

theorem prodX_sdiff_mul {S T : Finset (Fin (N + 1))} (h : S ⊆ T) :
    prodX R N (T \ S) * prodX R N S = prodX R N T :=
  Finset.prod_sdiff h

theorem isUnit_algebraMap_prodX {S T : Finset (Fin (N + 1))} (h : S ⊆ T) :
    IsUnit (algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R N T) (prodX R N S)) := by
  have hT : IsUnit (algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R N T) (prodX R N T)) :=
    IsLocalization.Away.algebraMap_isUnit (prodX R N T)
  have e : algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R N T) (prodX R N T) =
      algebraMap _ (Loc R N T) (prodX R N (T \ S)) * algebraMap _ (Loc R N T) (prodX R N S) := by
    rw [← map_mul, prodX_sdiff_mul h]
  rw [e] at hT
  exact isUnit_of_mul_isUnit_right hT

/-- The restriction map between localizations `R[T]_{T_S} → R[T]_{T_T}` (`S ⊆ T`), an `R`-algebra
homomorphism. -/
def locRes {S T : Finset (Fin (N + 1))} (h : S ⊆ T) : Loc R N S →ₐ[R] Loc R N T :=
  IsLocalization.Away.liftAlgHom (A := R) (x := prodX R N S)
    (f := IsScalarTower.toAlgHom R (MvPolynomial (Fin (N + 1)) R) (Loc R N T))
    (isUnit_algebraMap_prodX h)

theorem locRes_algebraMap {S T : Finset (Fin (N + 1))} (h : S ⊆ T)
    (a : MvPolynomial (Fin (N + 1)) R) :
    locRes h (algebraMap _ (Loc R N S) a) = algebraMap _ (Loc R N T) a := by
  show IsLocalization.Away.lift (prodX R N S) (isUnit_algebraMap_prodX h) _ = _
  rw [IsLocalization.Away.lift_eq]

variable (R N)

/-- `(R[T]_{T_S})_d`: the `R`-submodule spanned by `a / T_S^j` with `a` homogeneous of degree
`j·|S| + d`. -/
def degPiece (S : Finset (Fin (N + 1))) (d : ℤ) : Submodule R (Loc R N S) :=
  Submodule.span R {x | ∃ (j i : ℕ) (a : MvPolynomial (Fin (N + 1)) R),
    a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R i ∧ (i : ℤ) = j * S.card + d ∧
      x = Localization.mk a (⟨prodX R N S ^ j, j, rfl⟩ : Submonoid.powers (prodX R N S))}

variable {R N}

theorem locRes_mk {S T : Finset (Fin (N + 1))} (h : S ⊆ T)
    (a : MvPolynomial (Fin (N + 1)) R) (j : ℕ) :
    locRes h (Localization.mk a (⟨prodX R N S ^ j, j, rfl⟩ : Submonoid.powers (prodX R N S))) =
      Localization.mk (a * prodX R N (T \ S) ^ j)
        (⟨prodX R N T ^ j, j, rfl⟩ : Submonoid.powers (prodX R N T)) := by
  have hu := (isUnit_algebraMap_prodX (R := R) h).pow j
  rw [← map_pow] at hu
  apply hu.mul_left_injective
  show _ * _ = _ * _
  rw [Localization.mk_eq_mk', Localization.mk_eq_mk']
  have h1 : locRes h (IsLocalization.mk' (Loc R N S) a
        (⟨prodX R N S ^ j, j, rfl⟩ : Submonoid.powers (prodX R N S))) *
      algebraMap _ (Loc R N T) (prodX R N S ^ j) = algebraMap _ (Loc R N T) a := by
    rw [← locRes_algebraMap h (prodX R N S ^ j), ← map_mul]
    have := IsLocalization.mk'_spec (Loc R N S) a
      (⟨prodX R N S ^ j, j, rfl⟩ : Submonoid.powers (prodX R N S))
    rw [this, locRes_algebraMap]
  rw [h1, mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, eq_comm, IsLocalization.mk'_eq_iff_eq_mul,
    ← map_mul]
  congr 1
  show prodX R N S ^ j * (a * prodX R N (T \ S) ^ j) = a * prodX R N T ^ j
  rw [← prodX_sdiff_mul h, mul_pow]
  ring

theorem locRes_mem_degPiece {S T : Finset (Fin (N + 1))} (h : S ⊆ T) (d : ℤ)
    {x : Loc R N S} (hx : x ∈ degPiece R N S d) : locRes h x ∈ degPiece R N T d := by
  have : (degPiece R N S d).map (locRes h).toLinearMap ≤ degPiece R N T d := by
    rw [degPiece, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, i, a, ha, hi, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨j, i + j * (T \ S).card, a * prodX R N (T \ S) ^ j, ?_, ?_, locRes_mk h a j⟩
    · rw [MvPolynomial.mem_homogeneousSubmodule] at ha ⊢
      have := ha.mul ((prodX_isHomogeneous (R := R) (T \ S)).pow j)
      rwa [mul_comm (T \ S).card j] at this
    · have hc : (T \ S).card + S.card = T.card := Finset.card_sdiff_add_card_eq_card h
      push_cast
      rw [hi, ← hc]
      push_cast
      ring
  exact this (Submodule.mem_map_of_mem hx)

theorem locRes_comp {S T W : Finset (Fin (N + 1))} (h : S ⊆ T) (h' : T ⊆ W) (x : Loc R N S) :
    locRes h' (locRes h x) = locRes (h.trans h') x := by
  have key : ((locRes (R := R) h').toRingHom.comp (locRes h).toRingHom) =
      (locRes (h.trans h')).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (prodX R N S))
    ext a
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [locRes_algebraMap, locRes_algebraMap, locRes_algebraMap]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [locRes_algebraMap, locRes_algebraMap, locRes_algebraMap]
  exact congrArg (fun φ : Loc R N S →+* Loc R N W => φ x) key

/-! ## The complex: an instance of the abstract alternating Čech differential of `CechAltAlg` (same indices
and signs as `cechFamilyD`) -/

variable (R N)

/-- The index preorder `(Finset (Fin (N+1)))ᵒᵈ` (larger index set, smaller open). The index of the `p`-th
term: `σ ↦ {σ 0, …, σ p}`. -/
def V (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) : (Finset (Fin (N + 1)))ᵒᵈ :=
  OrderDual.toDual (Finset.univ.map σ.toEmbedding)

/-- The terms: `(R[T]_{T_S})_d`. -/
abbrev Term (d : ℤ) (S : (Finset (Fin (N + 1)))ᵒᵈ) : Type u :=
  degPiece R N (OrderDual.ofDual S) d

variable {R N}

/-- The restriction map `(R[T]_{T_S})_d → (R[T]_{T_T})_d` (`S ⊆ T`). -/
def res (d : ℤ) {v w : (Finset (Fin (N + 1)))ᵒᵈ} (h : w ≤ v) : Term R N d v →ₗ[R] Term R N d w :=
  (locRes (R := R) (S := OrderDual.ofDual v) (T := OrderDual.ofDual w) h).toLinearMap.restrict
    (fun _ hx => locRes_mem_degPiece h d hx)

theorem res_comp (d : ℤ) {u v w : (Finset (Fin (N + 1)))ᵒᵈ} (h : v ≤ u) (h' : w ≤ v)
    (x : Term R N d u) : res d h' (res d h x) = res d (h'.trans h) x :=
  Subtype.ext (locRes_comp (R := R) (S := OrderDual.ofDual u) (T := OrderDual.ofDual v)
    (W := OrderDual.ofDual w) h h' x.1)

variable (N) in
theorem hface (p : ℕ) (τ : Fin (p + 2) ↪o Fin (N + 1)) (k : Fin (p + 2)) :
    V N (p + 1) τ ≤ V N p (CechAltAlg.face τ k) := by
  show Finset.univ.map (CechAltAlg.face τ k).toEmbedding ⊆ Finset.univ.map τ.toEmbedding
  intro x hx
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
  exact Finset.mem_map.2 ⟨k.succAbove i, Finset.mem_univ _, rfl⟩

variable (R N)

/-- Laurent–Čech cochains: `C^p = ∏_{σ : Fin (p+1) ↪o Fin (N+1)} (R[T]_{T_σ})_d`. -/
abbrev Cochain (d : ℤ) (p : ℕ) : Type u := CechAltAlg.Cochain (V N) (Term R N d) p

/-- The Laurent–Čech differential (an instance of `CechAltAlg.d`): `(δ s)_τ = Σ_k (-1)^k res(s_{τ minus k})`. -/
def δ (d : ℤ) (p : ℕ) : Cochain R N d p →ₗ[R] Cochain R N d (p + 1) :=
  CechAltAlg.d (V N) (Term R N d) (fun h => res d h) (hface N) p

theorem δ_comp (d : ℤ) (p : ℕ) (s : Cochain R N d p) : δ R N d (p + 1) (δ R N d p s) = 0 :=
  CechAltAlg.d_comp_d (V N) (Term R N d) (fun h => res d h) (hface N)
    (fun h h' x => res_comp d h h' x) p s

/-- `S_d`: the homogeneous polynomials of degree `d` for `d ≥ 0`, and `0` for `d < 0`. -/
def polyPiece (d : ℤ) : Submodule R (MvPolynomial (Fin (N + 1)) R) :=
  if 0 ≤ d then MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R d.toNat else ⊥

end LaurentCech

end
