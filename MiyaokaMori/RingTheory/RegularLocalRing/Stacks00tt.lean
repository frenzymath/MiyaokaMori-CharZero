import MiyaokaMori.Prelude
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.LocalRing.Module
import MiyaokaMori.RingTheory.RegularLocalRing.RegularLocalRingQuotientOfInfSqLe

/-! # Stacks 00TT: smooth algebras over a field are regular

Stacks 00TT (the "Moreover" part): for a smooth algebra `S` over a field `k`, the localization at every prime is
a regular local ring.

Reference: Stacks 00TT (the only substantial input of the proof of 056S).

## Route

Instead of the route via base change to an algebraic closure, Stacks 00TS, and flat descent of regularity
00OF, we use the **Jacobian criterion** that Mathlib already has
(`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange`, Stacks 00TS's mechanism in
the form "for a presentation `0 → K → P → S → 0` with `P` formally smooth and `Ω_{P/R}` finite free,
`S` is formally smooth iff `κ ⊗ K → κ ⊗ Ω_{P/R}` is injective") together with the regularity of
localizations of polynomial rings over a field (Mathlib `MvPolynomial.isRegularRing_of_isRegularRing`).

Proof of the theorem:
1. `S` is smooth, hence of finite presentation: `S = A/I` with `A = k[x₁,…,xₙ]`, `I` finitely
   generated. Put `Q = π⁻¹(q) ⊆ A`, `B = A_Q`, `S_q = Localization.AtPrime q`. The induced map
   `f : B → S_q` is surjective with kernel `K = I·B` (finitely generated), so `S_q ≅ B/K`.
2. `B` is a regular local ring (localization of a polynomial ring over a field).
3. `B` is formally smooth over `k` with `Ω_{B/k}` finite free (localization of a polynomial ring;
   free because finite projective over a local ring), `S_q` is formally smooth over `k`
   (localization of a smooth algebra). The Jacobian criterion gives injectivity of
   `κ ⊗_B K → κ ⊗_B Ω_{B/k}`, `κ = B/m_B` (`Algebra.FormallySmooth.ker_inf_maximalIdeal_sq_le`
   below extracts from it `K ∩ m_B² ≤ m_B·K`: for `b ∈ K ∩ m_B²`, `1 ⊗ db = 0` in `κ ⊗ Ω`, so
   `1 ⊗ b = 0` in `κ ⊗ K = K/m_B K`).
4. `IsRegularLocalRing.quotient_of_inf_sq_le`
   (`MiyaokaMori.Stacks.Algebra.RegularLocalRingQuotientOfInfSqLe`): a regular local ring modulo
   an ideal `K` with `K ∩ m² ≤ mK` is regular. Transport along `B/K ≅ S_q`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open TensorProduct IsLocalRing

noncomputable section

section Jacobian

variable {P S : Type*} [CommRing P] [CommRing S] [Algebra P S] [IsLocalRing P] [IsLocalRing S]

/-- **Consequence of the Jacobian criterion.** Let `P → S` be a surjection of local rings
(`P`, `S` both formally smooth over `R`, `Ω_{P/R}` finite free, kernel `K` finitely generated).
Then `K ∩ m_P² ≤ m_P·K`, i.e. `K/m_P K → m_P/m_P²` is injective.

Proof: Mathlib's `Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange` (with the field
`κ = P/m_P`, made an `S`-algebra via `S ≅ P/K → P/m_P`) says `κ ⊗_P K → κ ⊗_P Ω_{P/R}`,
`1 ⊗ b ↦ 1 ⊗ db`, is injective. For `b ∈ K ∩ m_P²` write `b = Σ xᵢyᵢ` with `xᵢ, yᵢ ∈ m_P`; then
`1 ⊗ db = Σ (xᵢ·1) ⊗ dyᵢ + (yᵢ·1) ⊗ dxᵢ = 0` in `κ ⊗ Ω` since `xᵢ, yᵢ` act as `0` on `κ`.
Hence `1 ⊗ b = 0` in `κ ⊗_P K ≅ K/m_P K` (`TensorProduct.quotTensorEquivQuotSMul`), i.e.
`b ∈ m_P K`. -/
theorem Algebra.FormallySmooth.ker_inf_maximalIdeal_sq_le (R : Type*) [CommRing R]
    [Algebra R P] [Algebra R S] [IsScalarTower R P S]
    [Algebra.FormallySmooth R P] [Module.Free P (KaehlerDifferential R P)]
    [Module.Finite P (KaehlerDifferential R P)] [Algebra.FormallySmooth R S]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG) :
    RingHom.ker (algebraMap P S) ⊓ maximalIdeal P ^ 2 ≤ maximalIdeal P * RingHom.ker (algebraMap P S) := by
  classical
  set K := RingHom.ker (algebraMap P S) with hKdef
  have hKle : K ≤ maximalIdeal P := le_maximalIdeal (RingHom.ker_ne_top _)
  -- make `κ = P/m_P` an `S`-algebra through `S ≅ P/K → P/m_P`
  let g : S →+* ResidueField P :=
    (algebraMap P S).liftOfSurjective h₁ ⟨residue P, by rw [ker_residue]; exact hKle⟩
  have hg : ∀ x : P, g (algebraMap P S x) = residue P x := fun x =>
    RingHom.liftOfSurjective_comp_apply _ h₁ _ x
  let _ : Algebra S (ResidueField P) := g.toAlgebra
  have : IsScalarTower P S (ResidueField P) :=
    IsScalarTower.of_algebraMap_eq fun x => (hg x).symm
  have h₃ : maximalIdeal S ≤ RingHom.ker (algebraMap S (ResidueField P)) := by
    intro y hy
    obtain ⟨x, rfl⟩ := h₁ y
    rw [RingHom.mem_ker, RingHom.algebraMap_toAlgebra, hg, residue_eq_zero_iff]
    rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    exact fun hx => hy (hx.map (algebraMap P S))
  have hinj := (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange (R := R) (S := S)
    P (ResidueField P) h₁ h₂ h₃).mp inferInstance
  intro b hb
  obtain ⟨hbK, hbm⟩ := hb
  -- `1 ⊗ d b = 0` in `κ ⊗ Ω`
  have hD : (1 : ResidueField P) ⊗ₜ[P] KaehlerDifferential.D R P b = 0 := by
    rw [pow_two] at hbm
    refine Submodule.mul_induction_on hbm (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · have hx0 : x • (1 : ResidueField P) = 0 := by
        rw [Algebra.smul_def, mul_one]
        exact (residue_eq_zero_iff x).mpr hx
      have hy0 : y • (1 : ResidueField P) = 0 := by
        rw [Algebra.smul_def, mul_one]
        exact (residue_eq_zero_iff y).mpr hy
      rw [Derivation.leibniz, tmul_add, tmul_smul, tmul_smul, smul_tmul', smul_tmul', hx0, hy0,
        zero_tmul, zero_tmul, add_zero]
    · rw [map_add, tmul_add, hx, hy, add_zero]
  have h1 : (1 : ResidueField P) ⊗ₜ[P] (⟨b, hbK⟩ : K) = 0 := by
    apply hinj
    rw [map_zero, KaehlerDifferential.cotangentComplexBaseChange_tmul, one_smul,
      KaehlerDifferential.kerToTensor_apply]
    exact hD
  -- transport through `κ ⊗ K ≅ K / m_P K`
  have h2 : (⟨b, hbK⟩ : K) ∈ (maximalIdeal P • ⊤ : Submodule P K) := by
    have h1' : (Ideal.Quotient.mk (maximalIdeal P) 1 : P ⧸ maximalIdeal P) ⊗ₜ[P] (⟨b, hbK⟩ : K)
        = 0 := h1
    have h2' : (quotTensorEquivQuotSMul K (maximalIdeal P))
        ((Ideal.Quotient.mk (maximalIdeal P) 1 : P ⧸ maximalIdeal P) ⊗ₜ[P] (⟨b, hbK⟩ : K)) = 0 := by
      rw [h1', map_zero]
    rw [quotTensorEquivQuotSMul_mk_tmul, one_smul] at h2'
    exact (Submodule.Quotient.mk_eq_zero _).mp h2'
  have h3 := Submodule.mem_map_of_mem (f := K.subtype) h2
  rw [Submodule.map_smul'', Submodule.map_subtype_top, Ideal.smul_eq_mul] at h3
  exact h3

end Jacobian

/-- **Stacks 00TT (Moreover part).** `S` smooth over a field `k`, `q ⊆ S` prime; then `S_q` is a
regular local ring. Route in the module docstring. -/
theorem Algebra.Smooth.isRegularLocalRing_localization {k S : Type u} [Field k] [CommRing S]
    [Algebra k S] [Algebra.Smooth k S] (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  classical
  -- Step 1: presentation `S = k[x₁,…,xₙ]/I`
  obtain ⟨n, π, hπ⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := k) (S := S)).mp inferInstance
  have hIfg : (RingHom.ker π.toRingHom).FG := Algebra.FinitePresentation.ker_fG_of_surjective π hπ
  set A := MvPolynomial (Fin n) k
  set Q : Ideal A := Ideal.comap π.toRingHom q with hQ
  have : Q.IsPrime := Ideal.IsPrime.comap _
  set B := Localization.AtPrime Q
  set Sq := Localization.AtPrime q
  let f : B →+* Sq := Localization.localRingHom Q q π.toRingHom hQ
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
    obtain ⟨a, rfl⟩ := hπ s
    obtain ⟨b, hb⟩ := hπ (t : S)
    have hbQ : b ∈ Q.primeCompl := by
      show b ∉ Q
      rw [hQ, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hb]
      exact t.2
    refine ⟨IsLocalization.mk' B a ⟨b, hbQ⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hb
  have hker : RingHom.ker f = (RingHom.ker π.toRingHom).map (algebraMap A B) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
      rw [RingHom.mem_ker, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
      obtain ⟨⟨m, hm⟩, hmx⟩ := hx
      obtain ⟨c, rfl⟩ := hπ m
      have hcQ : c ∈ Q.primeCompl := by
        show c ∉ Q
        rw [hQ, Ideal.mem_comap]
        exact hm
      rw [IsLocalization.mk'_mem_map_algebraMap_iff]
      refine ⟨c, hcQ, ?_⟩
      rw [RingHom.mem_ker, map_mul]
      exact hmx
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, Localization.localRingHom_to_map,
        RingHom.mem_ker.mp ha, map_zero]
  have hkerFG : (RingHom.ker f).FG := hker ▸ hIfg.map _
  -- Step 3: instances for the Jacobian criterion
  let _ : Algebra B Sq := f.toAlgebra
  have : IsScalarTower k B Sq := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap k Sq x = f (algebraMap k B x)
    rw [IsScalarTower.algebraMap_apply k A B x, Localization.localRingHom_to_map,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, π.commutes, IsScalarTower.algebraMap_apply k S Sq x]
  have : Module.Free B (KaehlerDifferential k B) := Module.free_of_flat_of_isLocalRing
  have hinf := Algebra.FormallySmooth.ker_inf_maximalIdeal_sq_le k (P := B) (S := Sq) hf hkerFG
  -- Step 4: `B/ker f` is regular, and `S_q ≅ B/ker f`
  have hinf' : RingHom.ker f ⊓ maximalIdeal B ^ 2 ≤ maximalIdeal B * RingHom.ker f := hinf
  have hreg : IsRegularLocalRing (B ⧸ RingHom.ker f) :=
    IsRegularLocalRing.quotient_of_inf_sq_le (RingHom.ker f) (RingHom.ker_ne_top _) hinf'
  exact IsRegularLocalRing.of_ringEquiv (R := B ⧸ RingHom.ker f)
    (RingHom.quotientKerEquivOfSurjective hf)

end
