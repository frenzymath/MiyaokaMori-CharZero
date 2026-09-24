import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks00ot
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks00p1

/-! # Dimension at a point is preserved by field extension (Stacks 00P4)

Stacks 00P4: let `k` be a field, `S` a finitely generated `k`-algebra, `K/k` a field extension and
`q_K ∈ Spec (K ⊗_k S)` a prime lying over `q ∈ Spec S`. Then
`dim_q Spec S = dim_{q_K} Spec (K ⊗_k S)` (the global version is Stacks 00P3).

The proof follows Stacks:

* `localDim_mvPolynomial_eq`: the local dimension of a polynomial ring at any point is `n`;
* `stacks_00P2`: under a surjection of finitely generated `k`-algebras, "difference of local
  dimensions = difference of heights" (Stacks 00P2);
* `exists_mvPolynomial_surjective_baseChange`: the presentation `S = k[x]/I` base changes to
  `K ⊗_k S = K[x]/(K ⊗ I)`;
* `ker_le_map_ker_of_baseChange`: `ker π_K ⊆ (ker π)·K[x]` (right exactness of the tensor product,
  `Algebra.TensorProduct.lTensor_ker`);
* `height_add_height_eq_of_baseChange`: the two flat vertical arrows have the same height
  difference (the step of the original proof using Stacks 00ON);
* `stacks_00P4` assembles the above.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- In `WithBot ℕ∞`, adding a **finite** value can be cancelled. -/
private lemma withBot_enat_add_right_cancel {x y : WithBot ℕ∞} {m : ℕ∞} (hm : m ≠ ⊤)
    (h : x + (m : WithBot ℕ∞) = y + (m : WithBot ℕ∞)) : x = y := by
  induction x using WithBot.recBotCoe with
  | bot =>
    induction y using WithBot.recBotCoe with
    | bot => rfl
    | coe b => exact absurd h.symm (by simp)
  | coe a =>
    induction y using WithBot.recBotCoe with
    | bot => simp at h
    | coe b =>
      have h' : a + m = b + m := by exact_mod_cast h
      exact congrArg _ (WithTop.add_right_cancel hm h')

/-- **The local dimension of a polynomial ring at any point is `n`.**

Source: the last step of the proof of Stacks 00P4 (`dim_{x'} X' = n`), using Stacks 00OT (1) = (2)
and `MvPolynomial.ringKrullDim_of_isNoetherianRing`.

Proof: `k[x_1,…,x_n]` is a domain, so `Spec` is irreducible and its unique irreducible component is
the whole space; by 00OT the local dimension at `p` is the supremum of the dimensions of the
components through `p`, i.e. the dimension of the whole space
`= ringKrullDim k[x_1,…,x_n] = ringKrullDim k + n = n`. -/
theorem localDim_mvPolynomial_eq (k : Type u) [Field k] (n : ℕ)
    (p : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    (⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial (Fin n) k)) | p ∈ U},
        topologicalKrullDim U) = (n : WithBot ℕ∞) := by
  have hdim : topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin n) k)) = (n : WithBot ℕ∞) := by
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have huniv : topologicalKrullDim (Set.univ : Set (PrimeSpectrum (MvPolynomial (Fin n) k)))
      = (n : WithBot ℕ∞) := by
    rw [← hdim]
    exact (Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq
  rw [(stacks_00OT (k := k) (MvPolynomial (Fin n) k) p).1]
  refine le_antisymm (iSup₂_le fun Z _ => ?_) ?_
  · exact le_trans (topologicalKrullDim_subspace_le _ _) hdim.le
  · refine le_trans huniv.ge (le_iSup₂ (f := fun (Z : Set (PrimeSpectrum (MvPolynomial (Fin n) k)))
      (_ : Z ∈ {Z ∈ irreducibleComponents (PrimeSpectrum (MvPolynomial (Fin n) k)) | p ∈ Z}) =>
      topologicalKrullDim Z) Set.univ ⟨?_, trivial⟩)
    rw [irreducibleComponents_eq_singleton]
    rfl

/-- **Stacks 00P2**: let `k` be a field, `φ : S' ↠ S` a surjection of finitely generated
`k`-algebras, `q ⊆ S` a prime and `q' = φ⁻¹(q)`. Then
`dim_{q'} Spec S' − dim_q Spec S = ht q' − ht q`, written here **without subtraction** as
`dim_{q'} + ht q = dim_q + ht q'`.

Source: Stacks 00P2, whose proof is "immediate from 00P1".

Proof: by Stacks 00P1, `dim_{q'} Spec S' = ht q' + trdeg_k κ(q')` and
`dim_q Spec S = ht q + trdeg_k κ(q)`. Since `φ` is surjective with `q' = φ⁻¹(q)` there is a
`k`-algebra isomorphism `S'/q' ≅ S/q`, and passing to fraction fields `κ(q') ≅ κ(q)`
(`Ideal.ResidueField` is the fraction field of `R ⧸ I`,
`instance : IsFractionRing (R ⧸ I) I.ResidueField`), so both transcendence degrees agree. Add
the two equations. -/
theorem stacks_00P2 {k : Type u} [Field k] {S' S : Type u} [CommRing S'] [CommRing S]
    [Algebra k S'] [Algebra k S] [Algebra.FiniteType k S'] (φ : S' →ₐ[k] S)
    (hφ : Function.Surjective φ) (q : PrimeSpectrum S) :
    (⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum S') |
        PrimeSpectrum.comap φ.toRingHom q ∈ U}, topologicalKrullDim U)
        + ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) =
      (⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum S) | q ∈ U}, topologicalKrullDim U)
        + (((PrimeSpectrum.comap φ.toRingHom q).asIdeal.height : ℕ∞) : WithBot ℕ∞) := by
  have : Algebra.FiniteType k S := Algebra.FiniteType.of_surjective φ hφ
  -- κ(q') ≅ κ(q)
  have hker : RingHom.ker ((Ideal.Quotient.mkₐ k q.asIdeal).comp φ).toRingHom =
      (PrimeSpectrum.comap φ.toRingHom q).asIdeal := by
    rw [show ((Ideal.Quotient.mkₐ k q.asIdeal).comp φ).toRingHom
          = (Ideal.Quotient.mk q.asIdeal).comp (φ : S' →+* S) from rfl,
      RingHom.ker_eq_comap_bot, ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rfl
  have hsurj : Function.Surjective ((Ideal.Quotient.mkₐ k q.asIdeal).comp φ) :=
    Ideal.Quotient.mk_surjective.comp hφ
  have e0 : (S' ⧸ (PrimeSpectrum.comap φ.toRingHom q).asIdeal) ≃ₐ[k] (S ⧸ q.asIdeal) :=
    (Ideal.quotientEquivAlgOfEq k hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  have etrdeg : Algebra.trdeg k (PrimeSpectrum.comap φ.toRingHom q).asIdeal.ResidueField
      = Algebra.trdeg k q.asIdeal.ResidueField :=
    (IsFractionRing.fieldEquivOfAlgEquiv k _ _ e0).trdeg_eq
  rw [stacks_00P1 (k := k) S' (PrimeSpectrum.comap φ.toRingHom q), stacks_00P1 (k := k) S q,
    IsLocalization.AtPrime.ringKrullDim_eq_height
      (PrimeSpectrum.comap φ.toRingHom q).asIdeal
      (Localization.AtPrime (PrimeSpectrum.comap φ.toRingHom q).asIdeal),
    IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
      (Localization.AtPrime q.asIdeal), etrdeg]
  abel

/-- **Base change of the presentation `S = k[x_1,…,x_n]/I` to `K ⊗_k S = K[x_1,…,x_n]/(K ⊗_k I)`.**

Source: the first sentence of the proof of Stacks 00P4.

Proof: `S` is a finitely generated `k`-algebra; take a surjection `π : k[x_1,…,x_n] ↠ S`. Let
`π_K : K[x_1,…,x_n] → K ⊗_k S` be the `K`-algebra map sending `X i` to `1 ⊗ π(X i)`.
`π_K ∘ (extension of coefficients)` and `includeRight ∘ π` are ring maps agreeing on constants
and on the `X i`, hence equal; so the image of `π_K` contains every `1 ⊗ s` (`s ∈ S`), and being
a `K`-subalgebra it contains every `a ⊗ s`; since these generate the tensor product, `π_K` is
surjective. -/
theorem exists_mvPolynomial_surjective_baseChange (k : Type u) [Field k] (K : Type u) [Field K]
    [Algebra k K] (S : Type u) [CommRing S] [Algebra k S] [Algebra.FiniteType k S] :
    ∃ (n : ℕ) (π : MvPolynomial (Fin n) k →ₐ[k] S)
      (πK : MvPolynomial (Fin n) K →ₐ[K] TensorProduct k K S),
      Function.Surjective π ∧ Function.Surjective πK ∧
      ∀ x : MvPolynomial (Fin n) k,
        πK (MvPolynomial.map (algebraMap k K) x) =
          Algebra.TensorProduct.includeRight (π x) := by
  obtain ⟨n, π, hπ⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := k) (S := S)).mp inferInstance
  set πK : MvPolynomial (Fin n) K →ₐ[K] TensorProduct k K S :=
    MvPolynomial.aeval (fun i => Algebra.TensorProduct.includeRight (π (MvPolynomial.X i)))
    with hπKdef
  have key : ∀ x : MvPolynomial (Fin n) k,
      πK (MvPolynomial.map (algebraMap k K) x) =
        Algebra.TensorProduct.includeRight (π x) := by
    have hring : ((πK : MvPolynomial (Fin n) K →+* TensorProduct k K S)).comp
        (MvPolynomial.map (algebraMap k K)) =
        (Algebra.TensorProduct.includeRight : S →ₐ[k] TensorProduct k K S).toRingHom.comp
          (π : MvPolynomial (Fin n) k →+* S) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, MvPolynomial.map_C, hπKdef,
          AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.algHom_C,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply]
        rw [Algebra.algebraMap_eq_smul_one (R := k) (A := K) r,
          Algebra.algebraMap_eq_smul_one (R := k) (A := S) r]
        simp only [Algebra.algebraMap_self, RingHom.id_apply]
        exact TensorProduct.smul_tmul r 1 1
      · intro i
        simp [hπKdef]
    exact fun x => RingHom.congr_fun hring x
  refine ⟨n, π, πK, hπ, ?_, key⟩
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a s =>
      obtain ⟨x, rfl⟩ := hπ s
      refine ⟨MvPolynomial.C a * MvPolynomial.map (algebraMap k K) x, ?_⟩
      rw [map_mul, key x]
      simp [hπKdef, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  | add z w hz hw =>
      obtain ⟨u, rfl⟩ := hz
      obtain ⟨v, rfl⟩ := hw
      exact ⟨u + v, map_add _ _ _⟩

/-- **The kernel of the base-changed surjection lies in the extension of the original kernel**: if
`π : k[x] ↠ S` and `π_K : K[x] → K ⊗_k S` are compatible
(`π_K ∘ (extension of coefficients) = includeRight ∘ π`), then `ker π_K ⊆ (ker π)·K[x]`.

Source: the content of "`K ⊗_k S = K[x]/(K ⊗_k I)`" in the proof of Stacks 00P4; on the Mathlib
side this is right exactness of the tensor product, `Algebra.TensorProduct.lTensor_ker`
(`ker (id_K ⊗ π) = (ker π)·(K ⊗_k k[x])`).

Proof: let `e := MvPolynomial.algebraTensorAlgEquiv k K : K ⊗_k k[x] ≅ K[x]`. On `a ⊗ y`,
`π_K (e (a ⊗ y)) = a • π_K (f y) = a • (1 ⊗ π y) = a ⊗ π y = (id ⊗ π)(a ⊗ y)`, so
`π_K ∘ e = id_K ⊗ π`. If `π_K y = 0` then `e⁻¹ y ∈ ker (id_K ⊗ π) = (ker π)·(K ⊗ k[x])` by right
exactness, and since `e` sends `1 ⊗ x` to `f x`, `y = e (e⁻¹ y) ∈ (ker π)·K[x]`. -/
theorem ker_le_map_ker_of_baseChange
    {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
    {S : Type u} [CommRing S] [Algebra k S] {n : ℕ}
    (π : MvPolynomial (Fin n) k →ₐ[k] S)
    (πK : MvPolynomial (Fin n) K →ₐ[K] TensorProduct k K S)
    (hπ : Function.Surjective π)
    (hcomm : ∀ x : MvPolynomial (Fin n) k,
      πK (MvPolynomial.map (algebraMap k K) x) = Algebra.TensorProduct.includeRight (π x)) :
    RingHom.ker πK.toRingHom ≤
      (RingHom.ker π.toRingHom).map (MvPolynomial.map (algebraMap k K)) := by
  set e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) k K with he
  have hcomp : ∀ z : TensorProduct k K (MvPolynomial (Fin n) k),
      πK (e z) = Algebra.TensorProduct.map (AlgHom.id k K) π z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      rw [he, MvPolynomial.algebraTensorAlgEquiv_tmul, map_smul, hcomm,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add z w hz hw => simp only [map_add, hz, hw]
  intro y hy
  have h1 : e.symm y ∈ RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k K) π) := by
    rw [RingHom.mem_ker, ← hcomp, AlgEquiv.apply_symm_apply]
    exact hy
  rw [Algebra.TensorProduct.lTensor_ker π hπ] at h1
  have h3 : (RingHom.ker π).map (Algebra.TensorProduct.includeRight :
      MvPolynomial (Fin n) k →ₐ[k] TensorProduct k K (MvPolynomial (Fin n) k)) ≤
      Ideal.comap (e : TensorProduct k K (MvPolynomial (Fin n) k) →+* MvPolynomial (Fin n) K)
        ((RingHom.ker π.toRingHom).map (MvPolynomial.map (algebraMap k K))) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change e (Algebra.TensorProduct.includeRight x) ∈ _
    rw [Algebra.TensorProduct.includeRight_apply, he, MvPolynomial.algebraTensorAlgEquiv_tmul,
      one_smul]
    exact Ideal.mem_map_of_mem _ hx
  have h4 := h3 h1
  rw [Ideal.mem_comap] at h4
  simpa using h4

/-- **The main step of Stacks 00P4: base change preserves the difference of heights.**

Statement: let `π : k[x_1..x_n] ↠ S` and `π_K : K[x_1..x_n] ↠ K ⊗_k S` be the compatible
surjections constructed above, `q ⊆ K ⊗_k S` a prime, `p = q ∩ S`, `q' = π_K⁻¹(q)` and
`p' = π⁻¹(p)`. Then `ht q + ht p' = ht q' + ht p` (i.e. `ht q − ht p = ht q' − ht p'`).

Source: the middle of the proof of Stacks 00P4 (the commutative square of four Noetherian local
rings).

Proof:
1. The vertical arrows `S → K ⊗_k S` and `k[x] → K[x]` are **flat**: `K` is free as a `k`-module,
   so `− ⊗_k K` is exact, and flatness is stable under base change. Flat implies going-down
   (Stacks 00HS; `Algebra.HasGoingDown.of_flat`).
2. Both targets are Noetherian: `K ⊗_k S` is a finitely generated `K`-algebra
   (`Algebra.FiniteType.baseChange`), and `K[x_1..x_n]` is a polynomial ring.
3. By Stacks 00ON (`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`):
   `ht q = ht p + ht (image of q in (K ⊗_k S)/p·(K ⊗_k S))` and
   `ht q' = ht p' + ht (image of q' in K[x]/p'·K[x])`.
4. **The two fibre rings agree**: `(K ⊗_k S)/p(K ⊗_k S) ≅ K ⊗_k (S/p)` (right exactness) and
   `K[x]/p'K[x] ≅ K ⊗_k (k[x]/p')`; since `π` is surjective with `p' = π⁻¹(p)` there is a
   `k`-algebra isomorphism `k[x]/p' ≅ S/p`, and tensoring with `K ⊗_k −` gives a ring isomorphism
   `K[x]/p'K[x] ≅ (K ⊗_k S)/p(K ⊗_k S)` sending the image of `q'` to the image of `q` (by the
   compatibility `hcomm` of `π_K` and `π`). By `RingEquiv.height_comap` the two fibre heights agree.
5. Subtracting (in `ℕ∞`, heights of primes in a Noetherian ring being finite) gives
   `ht q + ht p' = ht q' + ht p`.

Step 4 in Lean (avoiding explicit tensor products):
(a) `π_K (p'·K[x]) = p·(K ⊗_k S)` (`Ideal.map_map`, compatibility, `Ideal.map_comap_of_surjective`),
    so `π_K⁻¹(p·(K ⊗_k S)) = p'·K[x] ⊔ ker π_K = p'·K[x]` because
    `ker π_K ⊆ (ker π)·K[x] ⊆ p'·K[x]` (`ker_le_map_ker_of_baseChange`);
(b) `φ := mk ∘ π_K : K[x] ↠ (K ⊗_k S)/p(K ⊗_k S)` is surjective with `ker φ = p'·K[x]`, so
    `RingHom.quotientKerEquivOfSurjective` gives `K[x]/p'K[x] ≅ (K ⊗_k S)/p(K ⊗_k S)` with
    `mk y ↦ mk (π_K y)`; `Ideal.mem_quotient_iff_mem` checks elementwise that the preimage of the
    image of `q'` is exactly the image of `q`, and `RingEquiv.height_comap` finishes.
Flatness: on the `S → K ⊗_k S` side use `Algebra.TensorProduct.commRight`
(`K ⊗_k S ≃ₐ[S] S ⊗_k K`) to reduce to `Module.Flat.baseChange`; on the `k[x] → K[x]` side use
`MvPolynomial.algebraTensorAlgEquiv` and `Algebra.TensorProduct.comm`. The two `Algebra`
structures (`rightAlgebra`, `algebraMvPolynomial`) are only local instances (`let`). -/
theorem height_add_height_eq_of_baseChange
    {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
    {S : Type u} [CommRing S] [Algebra k S] [Algebra.FiniteType k S] {n : ℕ}
    (π : MvPolynomial (Fin n) k →ₐ[k] S)
    (πK : MvPolynomial (Fin n) K →ₐ[K] TensorProduct k K S)
    (hπ : Function.Surjective π) (hπK : Function.Surjective πK)
    (hcomm : ∀ x : MvPolynomial (Fin n) k,
      πK (MvPolynomial.map (algebraMap k K) x) = Algebra.TensorProduct.includeRight (π x))
    (q : PrimeSpectrum (TensorProduct k K S)) :
    q.asIdeal.height +
        (PrimeSpectrum.comap π.toRingHom (PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight :
            S →ₐ[k] TensorProduct k K S).toRingHom q)).asIdeal.height =
      (PrimeSpectrum.comap πK.toRingHom q).asIdeal.height +
        (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight :
          S →ₐ[k] TensorProduct k K S).toRingHom q).asIdeal.height := by
  classical
  set incl : S →+* TensorProduct k K S :=
    (Algebra.TensorProduct.includeRight : S →ₐ[k] TensorProduct k K S).toRingHom with hincl
  set f : MvPolynomial (Fin n) k →+* MvPolynomial (Fin n) K := MvPolynomial.map (algebraMap k K)
    with hf
  set p : PrimeSpectrum S := PrimeSpectrum.comap incl q with hp
  set p' : PrimeSpectrum (MvPolynomial (Fin n) k) := PrimeSpectrum.comap π.toRingHom p with hp'
  set Q' : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom q with hQ'
  have hcomm' : πK.toRingHom.comp f = incl.comp π.toRingHom := RingHom.ext hcomm
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : IsNoetherianRing (TensorProduct k K S) :=
    Algebra.FiniteType.isNoetherianRing K (TensorProduct k K S)
  -- the vertical arrow `S → K ⊗_k S` (`rightAlgebra`, local instance only): flat ⇒ going-down, then 00ON
  let : Algebra S (TensorProduct k K S) := Algebra.TensorProduct.rightAlgebra
  have : Module.Flat S (TensorProduct k K S) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight k S K).symm.toLinearEquiv
  have : Algebra.HasGoingDown S (TensorProduct k K S) := Algebra.HasGoingDown.of_flat
  have : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have hA := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p.asIdeal q.asIdeal
  -- the vertical arrow `k[x] → K[x]` (`algebraMvPolynomial`, local instance only)
  let : Algebra (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) :=
    MvPolynomial.algebraMvPolynomial
  have : Module.Flat (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) := by
    have e : MvPolynomial (Fin n) K ≃ₐ[MvPolynomial (Fin n) k]
        TensorProduct k (MvPolynomial (Fin n) k) K :=
      AlgEquiv.ofRingEquiv (R := MvPolynomial (Fin n) k)
        (f := (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) k K).symm.toRingEquiv.trans
          (Algebra.TensorProduct.comm k K (MvPolynomial (Fin n) k)).toRingEquiv)
        (fun y => by
          change (Algebra.TensorProduct.comm k K (MvPolynomial (Fin n) k))
            ((MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) k K).symm
              (MvPolynomial.map (algebraMap k K) y)) = _
          rw [MvPolynomial.algebraTensorAlgEquiv_symm_map, Algebra.TensorProduct.comm_tmul,
            Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply])
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  have : Algebra.HasGoingDown (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) :=
    Algebra.HasGoingDown.of_flat
  have hunder : p'.asIdeal = Ideal.comap f Q'.asIdeal := by
    change Ideal.comap π.toRingHom (Ideal.comap incl q.asIdeal)
      = Ideal.comap f (Ideal.comap πK.toRingHom q.asIdeal)
    rw [Ideal.comap_comap, Ideal.comap_comap, hcomm']
  have : Q'.asIdeal.LiesOver p'.asIdeal := ⟨hunder⟩
  have hB := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p'.asIdeal Q'.asIdeal
  -- the two fibre rings are isomorphic, and the isomorphism sends the image of `Q'` to the image of `q`
  have hfib : (q.asIdeal.map (Ideal.Quotient.mk
        (p.asIdeal.map (algebraMap S (TensorProduct k K S))))).height =
      (Q'.asIdeal.map (Ideal.Quotient.mk (p'.asIdeal.map
        (algebraMap (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K))))).height := by
    change (q.asIdeal.map (Ideal.Quotient.mk (p.asIdeal.map incl))).height =
      (Q'.asIdeal.map (Ideal.Quotient.mk (p'.asIdeal.map f))).height
    set I : Ideal (TensorProduct k K S) := p.asIdeal.map incl with hI
    set J : Ideal (MvPolynomial (Fin n) K) := p'.asIdeal.map f with hJ
    have hIq : I ≤ q.asIdeal := Ideal.map_le_iff_le_comap.mpr le_rfl
    have hJQ : J ≤ Q'.asIdeal := Ideal.map_le_iff_le_comap.mpr hunder.le
    have hmapJ : J.map πK.toRingHom = I := by
      rw [hJ, hI, Ideal.map_map, hcomm', ← Ideal.map_map, hp',
        PrimeSpectrum.comap_asIdeal, Ideal.map_comap_of_surjective π.toRingHom hπ]
    have hker : RingHom.ker πK.toRingHom ≤ J :=
      (ker_le_map_ker_of_baseChange π πK hπ hcomm).trans
        (Ideal.map_mono (Ideal.ker_le_comap _))
    have hcomapI : Ideal.comap πK.toRingHom I = J := by
      rw [← hmapJ, Ideal.comap_map_of_surjective πK.toRingHom hπK, ← RingHom.ker_eq_comap_bot,
        sup_eq_left.mpr hker]
    let φ : MvPolynomial (Fin n) K →+* (TensorProduct k K S) ⧸ I :=
      (Ideal.Quotient.mk I).comp πK.toRingHom
    have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective.comp hπK
    have hkerφ : RingHom.ker φ = J := by
      rw [← hcomapI, RingHom.ker_eq_comap_bot]
      change Ideal.comap ((Ideal.Quotient.mk I).comp πK.toRingHom) ⊥ = _
      rw [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    let ε : (MvPolynomial (Fin n) K ⧸ J) ≃+* (TensorProduct k K S ⧸ I) :=
      (Ideal.quotEquivOfEq hkerφ.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)
    have hε : ∀ y, ε (Ideal.Quotient.mk J y) = Ideal.Quotient.mk I (πK y) := fun y => by
      rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk]
      rfl
    have hcomap : (q.asIdeal.map (Ideal.Quotient.mk I)).comap ε =
        Q'.asIdeal.map (Ideal.Quotient.mk J) := by
      ext x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.mem_comap, hε, Ideal.mem_quotient_iff_mem hIq, Ideal.mem_quotient_iff_mem hJQ]
      rfl
    rw [← RingEquiv.height_comap ε (q.asIdeal.map (Ideal.Quotient.mk I)), hcomap]
  rw [hA, hB, hfib]
  ring

/-- Stacks 00P4: the local dimension at a point is preserved by base change along a field
extension. -/
theorem stacks_00P4 {k : Type u} [Field k] (S : Type u) [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (K : Type u) [Field K] [Algebra k K] (q : PrimeSpectrum (TensorProduct k K S)) :
    (⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum (TensorProduct k K S)) | q ∈ U},
        topologicalKrullDim U) =
      ⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum S) |
          PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : S →ₐ[k] TensorProduct k K S).toRingHom q ∈ U},
        topologicalKrullDim U := by
  obtain ⟨n, π, πK, hπ, hπK, hcomm⟩ := exists_mvPolynomial_surjective_baseChange k K S
  set p : PrimeSpectrum S :=
    PrimeSpectrum.comap (Algebra.TensorProduct.includeRight :
      S →ₐ[k] TensorProduct k K S).toRingHom q with hpdef
  set p' : PrimeSpectrum (MvPolynomial (Fin n) k) := PrimeSpectrum.comap π.toRingHom p with hp'def
  set Q' : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom q with hQ'def
  have E2 := stacks_00P2 (k := k) π hπ p
  have E3 := stacks_00P2 (k := K) πK hπK q
  rw [localDim_mvPolynomial_eq k n p'] at E2
  rw [localDim_mvPolynomial_eq K n Q'] at E3
  have E5 := height_add_height_eq_of_baseChange π πK hπ hπK hcomm q
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : IsNoetherianRing (TensorProduct k K S) :=
    Algebra.FiniteType.isNoetherianRing K (TensorProduct k K S)
  have hb : p'.asIdeal.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  have hc : q.asIdeal.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  have he : Q'.asIdeal.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  refine withBot_enat_add_right_cancel
    (m := p'.asIdeal.height + q.asIdeal.height + Q'.asIdeal.height) ?_ ?_
  · simp [hb, hc, he]
  · have E5' : ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) + ((p'.asIdeal.height : ℕ∞) : WithBot ℕ∞)
        = ((Q'.asIdeal.height : ℕ∞) : WithBot ℕ∞) + ((p.asIdeal.height : ℕ∞) : WithBot ℕ∞) := by
      rw [← WithBot.coe_add, ← WithBot.coe_add]
      exact congrArg _ E5
    rw [WithBot.coe_add, WithBot.coe_add]
    simp only [← add_assoc]
    calc (⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum (TensorProduct k K S)) | q ∈ U},
            topologicalKrullDim U)
          + ((p'.asIdeal.height : ℕ∞) : WithBot ℕ∞) + ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞)
          + ((Q'.asIdeal.height : ℕ∞) : WithBot ℕ∞)
        = ((⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum (TensorProduct k K S)) | q ∈ U},
            topologicalKrullDim U) + ((Q'.asIdeal.height : ℕ∞) : WithBot ℕ∞))
          + (((p'.asIdeal.height : ℕ∞) : WithBot ℕ∞) + ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by
          abel
      _ = ((n : WithBot ℕ∞) + ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞))
          + (((p'.asIdeal.height : ℕ∞) : WithBot ℕ∞) + ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by
          rw [← E3]
      _ = (n : WithBot ℕ∞)
          + ((((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) + ((p'.asIdeal.height : ℕ∞) : WithBot ℕ∞))
            + ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by abel
      _ = (n : WithBot ℕ∞)
          + ((((Q'.asIdeal.height : ℕ∞) : WithBot ℕ∞) + ((p.asIdeal.height : ℕ∞) : WithBot ℕ∞))
            + ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by rw [E5']
      _ = ((n : WithBot ℕ∞) + ((p.asIdeal.height : ℕ∞) : WithBot ℕ∞))
          + (((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) + ((Q'.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by
          abel
      _ = ((⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum S) | p ∈ U},
            topologicalKrullDim U) + ((p'.asIdeal.height : ℕ∞) : WithBot ℕ∞))
          + (((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) + ((Q'.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by
          rw [E2]
      _ = (⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum S) | p ∈ U},
            topologicalKrullDim U)
          + ((p'.asIdeal.height : ℕ∞) : WithBot ℕ∞) + ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞)
          + ((Q'.asIdeal.height : ℕ∞) : WithBot ℕ∞) := by abel

end
