import BlowupIrrelevant

/-!
# ブローアップ(層10: `Proj B` の閉点は `blowupPoint` で尽くされる)

`𝔭 : ProjectiveSpectrum B` が `x − c`, `y − c'`, `a t + b u`(`(a, b) ≠ 0`)を含むなら、
ある `z ∈ blowupSet k` で `blowupPoint z = 𝔭` となる(`exists_blowupPoint_eq`)。

証明の流れ:
1. `E = c u − c' t ∈ 𝔭`(`x u = t y` と `x ≡ c`, `y ≡ c'` から)。`t, u` が両方 `𝔭` に入ると
   irrelevant ideal `(t, u)` が `𝔭` に入って矛盾するので、`a t + b u` と `E` の行列式 `c a + b c'` は 0。
2. 点 `z = ((c, c'), [b : −a])`。斉次多項式 `g` について `g − σ(g) ∈ (x − c, y − c', …)`、
   `σ(g) = g(c, c', b, −a) · T^n`(`T` は `t` か `u` の定数倍)から、
   `g ∈ 𝔭 ⇔ g(z) = 0`。
-/

open MvPolynomial Projectivization AlgebraicGeometry

namespace Blowup

section surj

variable {k : Type*} [Field k]

/-- `k[x,y,t,u] → B`。 -/
noncomputable abbrev mkB (k : Type*) [Field k] : MvPolynomial (Fin 4) k →+* BlowRing k :=
  Ideal.Quotient.mk (blowIdeal k)

lemma monomial_fin4 (d : Fin 4 →₀ ℕ) (r : k) :
    monomial d r = C r * (X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ d 2 * X 3 ^ d 3) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_four]

lemma weight_wt (d : Fin 4 →₀ ℕ) : Finsupp.weight wt d = d 2 + d 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four, wt]

/-- 次数 `n` の斉次多項式は `evalPair` について `n` 次斉次。 -/
lemma isBihom_of_mem_bigrading {n : ℕ} {g : MvPolynomial (Fin 4) k} (hg : g ∈ bigrading k n) :
    IsBihom n g := by
  intro P v s
  have hg' : IsWeightedHomogeneous wt g n := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hg
  unfold evalPair
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hn : n = d 2 + d 3 := (hg' (mem_support_iff.mp hd)).symm.trans (weight_wt d)
  rw [hn]
  simp only [Fin.prod_univ_four, Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, C_neg, neg_pow, mul_pow, pow_add]
  ring

/-- 代入 `x ↦ c`, `y ↦ c'`, `t ↦ b T`, `u ↦ −a T`。 -/
noncomputable def sig (c c' a b : k) (T : MvPolynomial (Fin 4) k) :
    MvPolynomial (Fin 4) k →ₐ[k] MvPolynomial (Fin 4) k :=
  MvPolynomial.aeval (![C c, C c', C b * T, -(C a * T)] : Fin 4 → MvPolynomial (Fin 4) k)

lemma sig_homog (c c' a b : k) (T : MvPolynomial (Fin 4) k) {n : ℕ} {g : MvPolynomial (Fin 4) k}
    (hg : g ∈ bigrading k n) :
    sig c c' a b T g = C (MvPolynomial.eval ![c, c', b, -a] g) * T ^ n := by
  have hg' : IsWeightedHomogeneous wt g n := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hg
  conv_lhs => rw [g.as_sum]
  rw [map_sum, MvPolynomial.eval_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hn : n = d 2 + d 3 := (hg' (mem_support_iff.mp hd)).symm.trans (weight_wt d)
  rw [hn, monomial_fin4]
  simp only [sig, map_mul, map_pow, map_neg, aeval_X, aeval_C, algebraMap_eq, C_mul, C_pow, C_neg,
    Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, C_neg, neg_pow, mul_pow, pow_add]
  ring

lemma sub_sig_mem (σ : MvPolynomial (Fin 4) k →ₐ[k] MvPolynomial (Fin 4) k)
    (p : MvPolynomial (Fin 4) k) :
    p - σ p ∈ Ideal.span (Set.range fun i : Fin 4 => (X i : MvPolynomial (Fin 4) k) - σ (X i)) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have h : σ (C c) = C c := by
      have := σ.commutes c
      rwa [MvPolynomial.algebraMap_eq] at this
    rw [h, sub_self]
    exact zero_mem _
  | add a b ha hb =>
    rw [map_add]
    have : a + b - (σ a + σ b) = (a - σ a) + (b - σ b) := by ring
    rw [this]
    exact add_mem ha hb
  | mul_X a i ha =>
    rw [map_mul]
    have : a * X i - σ a * σ (X i) = (a - σ a) * X i + σ a * (X i - σ (X i)) := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

lemma mem_of_C_mul_mem {P : Ideal (BlowRing k)} {D : k} (hD : D ≠ 0) {g : MvPolynomial (Fin 4) k}
    (h : mkB k (C D * g) ∈ P) : mkB k g ∈ P := by
  have e : g = C D⁻¹ * (C D * g) := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hD, C_1, one_mul]
  rw [e, map_mul]
  exact Ideal.mul_mem_left _ _ h

/-- 核心:`𝔭` が `x − c`, `y − c'`, `t − b T`, `u + a T` を含み `T ∉ 𝔭` なら、
斉次多項式 `g` について `g ∈ 𝔭 ⇔ g(c, c', b, −a) = 0`。 -/
lemma mem_iff_eval (𝔭 : ProjectiveSpectrum (blowGrading k)) (c c' a b : k)
    (T : MvPolynomial (Fin 4) k)
    (hx : mkB k (X 0 - C c) ∈ 𝔭.asHomogeneousIdeal.toIdeal)
    (hy : mkB k (X 1 - C c') ∈ 𝔭.asHomogeneousIdeal.toIdeal)
    (h2 : mkB k (X 2 - C b * T) ∈ 𝔭.asHomogeneousIdeal.toIdeal)
    (h3 : mkB k (X 3 + C a * T) ∈ 𝔭.asHomogeneousIdeal.toIdeal)
    (hT : mkB k T ∉ 𝔭.asHomogeneousIdeal.toIdeal)
    {n : ℕ} {g : MvPolynomial (Fin 4) k} (hg : g ∈ bigrading k n) :
    mkB k g ∈ 𝔭.asHomogeneousIdeal.toIdeal ↔ MvPolynomial.eval ![c, c', b, -a] g = 0 := by
  have hprime := 𝔭.isPrime
  set I := 𝔭.asHomogeneousIdeal.toIdeal with hI
  have hspan : Ideal.span (Set.range fun i : Fin 4 =>
      (X i : MvPolynomial (Fin 4) k) - sig c c' a b T (X i)) ≤ Ideal.comap (mkB k) I := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show mkB k _ ∈ I
    fin_cases i
    · simpa [sig] using hx
    · simpa [sig] using hy
    · simpa [sig] using h2
    · simpa [sig] using h3
  have hdiff : mkB k (g - sig c c' a b T g) ∈ I := hspan (sub_sig_mem _ g)
  have hiff : mkB k g ∈ I ↔ mkB k (sig c c' a b T g) ∈ I := by
    rw [map_sub] at hdiff
    constructor
    · intro h
      have := I.sub_mem h hdiff
      rwa [sub_sub_cancel] at this
    · intro h
      have := I.add_mem hdiff h
      rwa [sub_add_cancel] at this
  rw [hiff, sig_homog c c' a b T hg]
  set γ := MvPolynomial.eval ![c, c', b, -a] g with hγ
  constructor
  · intro h
    by_contra hne
    have h' : mkB k (C γ⁻¹ * (C γ * T ^ n)) ∈ I := by
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ h
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hne, C_1, one_mul, map_pow] at h'
    exact hT (hprime.mem_of_pow_mem n h')
  · intro h
    rw [h, C_0, zero_mul, map_zero]
    exact zero_mem _

lemma homIdeal_ext (I J : HomogeneousIdeal (blowGrading k))
    (h : ∀ (g : BlowRing k) (n : ℕ), g ∈ blowGrading k n → (g ∈ I ↔ g ∈ J)) : I = J := by
  classical
  have aux : ∀ (I J : HomogeneousIdeal (blowGrading k)),
      (∀ (g : BlowRing k) (n : ℕ), g ∈ blowGrading k n → (g ∈ I ↔ g ∈ J)) → I ≤ J := by
    intro I J h x hx
    rw [← DirectSum.sum_support_decompose (blowGrading k) x]
    refine Ideal.sum_mem _ fun i _ => ?_
    exact (h _ i (DirectSum.decompose (blowGrading k) x i).2).mp (I.isHomogeneous i hx)
  exact le_antisymm (aux I J h) (aux J I fun g n hg => (h g n hg).symm)

end surj

end Blowup
