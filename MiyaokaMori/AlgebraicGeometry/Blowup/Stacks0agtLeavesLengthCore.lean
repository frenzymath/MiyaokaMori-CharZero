import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0agtLeavesQuotFamilies
import MiyaokaMori.RingTheory.Length.Stacks0agtLeavesQuotLength
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0agtLeavesStalkTwist
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0agtLeavesSkyscraper
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0agtLeavesExponentCore

/-! # The length inequality of Stacks 0AGT at the variable level

`X` locally Noetherian, `E` an invertible ideal sheaf with nonempty support, `I'` an ideal sheaf
whose support is a finite set `T` of closed points, `d ≥ 1`, `IX = E^d · I'`. Suppose the
`A`-module `Γ(X, O_X/IX)` (modelled by `IX.quotFamilies`) is a quotient of `A/I` (through a
surjective `φ : A → Γ(X, ⊤)` and a surjective `Γ(X, ⊤) → quotFamilies` killing `I`) and
`ℓ_A(A/I) < ∞`. Then

  `Σ_{x ∈ T} ℓ_{O_{X,x}}(O_{X,x}/I'_x) < ℓ_A(A/I)`.

Proof (Stacks 0AGT, second and third paragraphs, rearranged so that no sheaf cohomology and no
twisting sheaf `O_X(dE)` are needed):
`Σ_x ℓ(O_x/I'_x) = Σ_x ℓ_{O_x}(E^d_x/IX_x)` (`length_stalkPiece_pow_mul_eq`)
`≤ Σ_x ℓ_{Γ(X,⊤)}(E^d_x/IX_x) = ℓ_{Γ(X,⊤)}(Π_x E^d_x/IX_x)` (restriction of scalars, `length_pi`)
`≤ ℓ_{Γ(X,⊤)}(Γ(X, E^d/IX))` (the germ map is surjective: `subFamiliesGerm_surjective`)
`< ℓ_{Γ(X,⊤)}(Γ(X, O_X/IX))` (the section `1` is not in `E^d/IX`, as `E^d(U) ≠ ⊤` on a chart
meeting `E`; `Module.length_lt_of_notMem`)
`≤ ℓ_{Γ(X,⊤)}(Γ(X,⊤)/I·Γ(X,⊤)) ≤ ℓ_A(A/I)` (surjectivity hypotheses).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.IdealSheafData.QuotFamilies0agt

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The constant section `1` of `O_X/IX` is not a section of `E^d/IX` when `IX ≤ E^d`, `d ≥ 1`
and `E` has a point in its support. -/
theorem toQuotFamilies_one_notMem_subFamilies (E I' : X.IdealSheafData) (d : ℕ) (hd : 0 < d)
    {y : X} (hy : y ∈ E.support) :
    (E ^ d * I').toQuotFamilies 1 ∉ (E ^ d * I').subFamilies (E ^ d) := by
  intro hmem
  obtain ⟨U, hyU⟩ := X.exists_affineOpens_mem y
  have h := hmem U
  rw [toQuotFamilies_apply_coe, map_one] at h
  obtain ⟨k, hk, hk1⟩ := Submodule.mem_map.1 h
  rw [Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq] at hk1
  have hk1' : k - 1 ∈ (E ^ d).ideal U := by
    have : (E ^ d * I').ideal U ≤ (E ^ d).ideal U := by
      rw [ideal_mul, Pi.mul_apply]
      exact Ideal.mul_le_left
    exact this hk1
  have h1 : (1 : Γ(X, U)) ∈ (E ^ d).ideal U := by
    have := Submodule.sub_mem _ hk hk1'
    rwa [sub_sub_cancel] at this
  apply ideal_ne_top_of_mem_support E hy U hyU
  rw [Ideal.eq_top_iff_one]
  have hle : (E ^ d).ideal U ≤ E.ideal U := by
    rw [ideal_pow, Pi.pow_apply]
    exact Ideal.pow_le_self hd.ne'
  exact hle h1

/-- **Core of the length inequality of Stacks 0AGT** (variable level; see the module docstring). -/
theorem length_sum_lt_of_quotFamilies [AlgebraicGeometry.IsLocallyNoetherian X]
    (E I' : X.IdealSheafData) (hE : MiyaokaMori.Statement.IsInvertibleIdeal E) (d : ℕ) (hd : 0 < d)
    {y : X} (hy : y ∈ E.support) (T : Finset X) (hT : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hTsupp : (I'.support : Set X) = ↑T)
    (A : Type u) [CommRing A] (φ : A →+* Γ(X, ⊤)) (hφ : Function.Surjective φ) (I : Ideal A)
    (hfin : Module.length A (A ⧸ I) ≠ ⊤)
    (hsurj : Function.Surjective (E ^ d * I').toQuotFamilies)
    (hker : ∀ a ∈ I, (E ^ d * I').toQuotFamilies (φ a) = 0) :
    ∑ x : T, Module.length (X.presheaf.stalk x.1) (X.presheaf.stalk x.1 ⧸ I'.stalkIdeal x.1) <
      Module.length A (A ⧸ I) := by
  classical
  -- the germ map onto the stalk pieces is surjective (skyscraper decomposition)
  have hsupp : ∀ x : X, x ∉ T → (E ^ d).stalkIdeal x = (E ^ d * I').stalkIdeal x := by
    intro x hx
    have hx' : x ∉ I'.support := by
      intro h
      apply hx
      have : x ∈ (I'.support : Set X) := h
      rwa [hTsupp] at this
    rw [stalkIdeal_mul, I'.stalkIdeal_eq_top_of_notMem_support x hx', Ideal.mul_top]
  have hJK : E ^ d * I' ≤ E ^ d := fun U => by
    rw [ideal_mul, Pi.mul_apply]
    exact Ideal.mul_le_left
  have hgerm := (E ^ d * I').subFamiliesGerm_surjective (E ^ d) hJK T hT hsupp
  -- the two length bounds from the surjections
  have hR1 : Module.length Γ(X, ⊤) (E ^ d * I').quotFamilies ≤
      Module.length Γ(X, ⊤) (Γ(X, ⊤) ⧸ I.map φ) := by
    refine Module.length_le_length_quotient_of_surjective _ hsurj (I.map φ) ?_
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact hker a ha
  have hR2 := Module.length_quotient_map_le_of_surjective φ hφ I
  have hQfin : Module.length Γ(X, ⊤) (E ^ d * I').quotFamilies ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (hR1.trans hR2)
  calc ∑ x : T, Module.length (X.presheaf.stalk x.1) (X.presheaf.stalk x.1 ⧸ I'.stalkIdeal x.1)
      = ∑ x : T, Module.length (X.presheaf.stalk x.1) ((E ^ d * I').stalkPiece (E ^ d) x.1) :=
        Finset.sum_congr rfl fun x _ => (length_stalkPiece_pow_mul_eq hE I' d x.1).symm
    _ ≤ ∑ x : T, Module.length Γ(X, ⊤)
          (((E ^ d * I').stalkPiece (E ^ d) x.1).restrictScalars Γ(X, ⊤)) :=
        Finset.sum_le_sum fun x _ => length_stalkPiece_le_length_restrictScalars _ _ x.1
    _ = Module.length Γ(X, ⊤)
          (∀ x : T, ((E ^ d * I').stalkPiece (E ^ d) x.1).restrictScalars Γ(X, ⊤)) :=
        (Module.length_pi_of_fintype Γ(X, ⊤) _).symm
    _ ≤ Module.length Γ(X, ⊤) ((E ^ d * I').subFamilies (E ^ d)) :=
        Module.length_le_of_surjective _ hgerm
    _ < Module.length Γ(X, ⊤) (E ^ d * I').quotFamilies :=
        Module.length_lt_of_notMem _ hQfin (toQuotFamilies_one_notMem_subFamilies E I' d hd hy)
    _ ≤ Module.length Γ(X, ⊤) (Γ(X, ⊤) ⧸ I.map φ) := hR1
    _ ≤ Module.length A (A ⧸ I) := hR2

end AlgebraicGeometry.Scheme.IdealSheafData

end
