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
    Matrix.head_cons, Matrix.tail_cons, mul_pow, pow_add]
  ring

/-- 代入 `x ↦ c`, `y ↦ c'`, `t ↦ b T`, `u ↦ −a T`。 -/
noncomputable def sig (c c' a b : k) (T : MvPolynomial (Fin 4) k) :
    MvPolynomial (Fin 4) k →ₐ[k] MvPolynomial (Fin 4) k :=
  MvPolynomial.aeval (![C c, C c', C b * T, C (-a) * T] : Fin 4 → MvPolynomial (Fin 4) k)

lemma sig_homog (c c' a b : k) (T : MvPolynomial (Fin 4) k) {n : ℕ} {g : MvPolynomial (Fin 4) k}
    (hg : g ∈ bigrading k n) :
    sig c c' a b T g = C (MvPolynomial.eval ![c, c', b, -a] g) * T ^ n := by
  have hg' : IsWeightedHomogeneous wt g n := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hg
  conv_lhs => rw [g.as_sum]
  rw [map_sum, MvPolynomial.eval_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hn : n = d 2 + d 3 := (hg' (mem_support_iff.mp hd)).symm.trans (weight_wt d)
  rw [hn, monomial_fin4]
  simp only [sig, map_mul, map_pow, aeval_X, aeval_C, algebraMap_eq, C_mul, C_pow,
    Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, mul_pow, pow_add]
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
    (h3 : mkB k (X 3 - C (-a) * T) ∈ 𝔭.asHomogeneousIdeal.toIdeal)
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


lemma mk_blowEq : mkB k (blowEq k) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

/-- `t, u` が両方 `𝔭` に入ることはない(irrelevant ideal が `(t, u)` だから)。 -/
lemma tu_not_both (𝔭 : ProjectiveSpectrum (blowGrading k)) :
    ¬ (mkB k (X 2) ∈ 𝔭.asHomogeneousIdeal.toIdeal ∧ mkB k (X 3) ∈ 𝔭.asHomogeneousIdeal.toIdeal) := by
  rintro ⟨h2, h3⟩
  apply 𝔭.not_irrelevant_le
  intro x hx
  have hx' : x ∈ (HomogeneousIdeal.irrelevant (blowGrading k)).toIdeal := hx
  rw [irrelevant_eq_span] at hx'
  refine (Ideal.span_le.mpr ?_ : Ideal.span _ ≤ 𝔭.asHomogeneousIdeal.toIdeal) hx'
  intro s hs
  rcases hs with rfl | rfl
  · exact h2
  · exact h3

lemma mem_E2 (𝔭 : ProjectiveSpectrum (blowGrading k)) (c c' : k)
    (hx : mkB k (X 0 - C c) ∈ 𝔭.asHomogeneousIdeal.toIdeal)
    (hy : mkB k (X 1 - C c') ∈ 𝔭.asHomogeneousIdeal.toIdeal) :
    mkB k (C c * X 3 - C c' * X 2) ∈ 𝔭.asHomogeneousIdeal.toIdeal := by
  have key : (C c * X 3 - C c' * X 2 : MvPolynomial (Fin 4) k) =
      (C c - X 0) * X 3 + X 2 * (X 1 - C c') + blowEq k := by
    simp only [blowEq]; ring
  have hx' : mkB k (C c - X 0) ∈ 𝔭.asHomogeneousIdeal.toIdeal := by
    rw [← neg_sub, map_neg]
    exact neg_mem hx
  rw [key, map_add, map_add, map_mul, map_mul, mk_blowEq, add_zero]
  exact add_mem (Ideal.mul_mem_right _ _ hx') (Ideal.mul_mem_left _ _ hy)

/-- 行列式 `c a + b c' = 0`。 -/
lemma det_eq_zero (𝔭 : ProjectiveSpectrum (blowGrading k)) (c c' a b : k)
    (hx : mkB k (X 0 - C c) ∈ 𝔭.asHomogeneousIdeal.toIdeal)
    (hy : mkB k (X 1 - C c') ∈ 𝔭.asHomogeneousIdeal.toIdeal)
    (hl : mkB k (C a * X 2 + C b * X 3) ∈ 𝔭.asHomogeneousIdeal.toIdeal) :
    c * a + b * c' = 0 := by
  have hE := mem_E2 𝔭 c c' hx hy
  by_contra hD
  apply tu_not_both 𝔭
  constructor
  · refine mem_of_C_mul_mem hD ?_
    have e : (C (c * a + b * c') * X 2 : MvPolynomial (Fin 4) k) =
        C c * (C a * X 2 + C b * X 3) - C b * (C c * X 3 - C c' * X 2) := by
      rw [C_add, C_mul, C_mul]; ring
    rw [e, map_sub, map_mul, map_mul]
    exact sub_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hE)
  · refine mem_of_C_mul_mem hD ?_
    have e : (C (c * a + b * c') * X 3 : MvPolynomial (Fin 4) k) =
        C c' * (C a * X 2 + C b * X 3) + C a * (C c * X 3 - C c' * X 2) := by
      rw [C_add, C_mul, C_mul]; ring
    rw [e, map_add, map_mul, map_mul]
    exact add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hE)

lemma exists_gen (𝔭 : ProjectiveSpectrum (blowGrading k)) (a b : k) (hab : a ≠ 0 ∨ b ≠ 0)
    (hl : mkB k (C a * X 2 + C b * X 3) ∈ 𝔭.asHomogeneousIdeal.toIdeal) :
    ∃ T : MvPolynomial (Fin 4) k,
      mkB k (X 2 - C b * T) ∈ 𝔭.asHomogeneousIdeal.toIdeal ∧
      mkB k (X 3 - C (-a) * T) ∈ 𝔭.asHomogeneousIdeal.toIdeal ∧
      mkB k T ∉ 𝔭.asHomogeneousIdeal.toIdeal := by
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := hab.resolve_right (not_not.mpr rfl)
    have hna : -a ≠ 0 := neg_ne_zero.mpr ha
    have hX2 : mkB k (X 2) ∈ 𝔭.asHomogeneousIdeal.toIdeal := by
      refine mem_of_C_mul_mem ha ?_
      simpa using hl
    refine ⟨C (-a)⁻¹ * X 3, ?_, ?_, ?_⟩
    · simpa using hX2
    · have e : (X 3 - C (-a) * (C (-a)⁻¹ * X 3) : MvPolynomial (Fin 4) k) = 0 := by
        rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hna, C_1, one_mul, sub_self]
      rw [e, map_zero]
      exact zero_mem _
    · intro h
      have hX3 := mem_of_C_mul_mem (inv_ne_zero hna) h
      exact tu_not_both 𝔭 ⟨hX2, hX3⟩
  · refine ⟨C b⁻¹ * X 2, ?_, ?_, ?_⟩
    · have e : (X 2 - C b * (C b⁻¹ * X 2) : MvPolynomial (Fin 4) k) = 0 := by
        rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hb, C_1, one_mul, sub_self]
      rw [e, map_zero]
      exact zero_mem _
    · have e0 : (C b⁻¹ * C b : MvPolynomial (Fin 4) k) = 1 := by
        rw [← C_mul, inv_mul_cancel₀ hb, C_1]
      have e : (X 3 - C (-a) * (C b⁻¹ * X 2) : MvPolynomial (Fin 4) k) =
          C b⁻¹ * (C a * X 2 + C b * X 3) := by
        rw [C_neg]
        linear_combination (-(X 3 : MvPolynomial (Fin 4) k)) * e0
      rw [e, map_mul]
      exact Ideal.mul_mem_left _ _ hl
    · intro h
      have hX2 := mem_of_C_mul_mem (inv_ne_zero hb) h
      have hX3 : mkB k (C b * X 3) ∈ 𝔭.asHomogeneousIdeal.toIdeal := by
        have : (C b * X 3 : MvPolynomial (Fin 4) k) =
            (C a * X 2 + C b * X 3) - C a * X 2 := by ring
        rw [this, map_sub, map_mul]
        exact sub_mem hl (Ideal.mul_mem_left _ _ hX2)
      exact tu_not_both 𝔭 ⟨hX2, mem_of_C_mul_mem hb hX3⟩

lemma vec_ne_zero {a b : k} (hab : a ≠ 0 ∨ b ≠ 0) : (![b, -a] : Fin 2 → k) ≠ 0 := by
  intro h
  rcases hab with ha | hb
  · apply ha
    have := congrFun h 1
    simpa using this
  · apply hb
    have := congrFun h 0
    simpa using this

lemma point_mem {c c' a b : k} (hab : a ≠ 0 ∨ b ≠ 0) (hD : c * a + b * c' = 0) :
    ((![c, c'] : Fin 2 → k), mk k ![b, -a] (vec_ne_zero hab)) ∈ blowupSet k := by
  rw [mem_blowupSet_iff (vec_ne_zero hab) rfl]
  change c * (-a) = b * c'
  linear_combination (-1 : k) * hD

/-- **`x − c`, `y − c'`, `a t + b u` を含む `Proj B` の点は `blowupPoint z` の形**(`(a, b) ≠ 0`)。 -/
theorem exists_blowupPoint_eq (𝔭 : ProjectiveSpectrum (blowGrading k)) (c c' a b : k)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (hx : mkB k (X 0 - C c) ∈ 𝔭.asHomogeneousIdeal.toIdeal)
    (hy : mkB k (X 1 - C c') ∈ 𝔭.asHomogeneousIdeal.toIdeal)
    (hl : mkB k (C a * X 2 + C b * X 3) ∈ 𝔭.asHomogeneousIdeal.toIdeal) :
    ∃ z : blowupSet k, blowupPoint k z = 𝔭 := by
  have hD := det_eq_zero 𝔭 c c' a b hx hy hl
  have hv := vec_ne_zero hab
  have hz := point_mem hab hD
  obtain ⟨T, h2, h3, hT⟩ := exists_gen 𝔭 a b hab hl
  have key : ∀ {n : ℕ} {g : MvPolynomial (Fin 4) k}, g ∈ bigrading k n →
      (mkB k g ∈ 𝔭.asHomogeneousIdeal.toIdeal ↔ MvPolynomial.eval ![c, c', b, -a] g = 0) :=
    fun hg => mem_iff_eval 𝔭 c c' a b T hx hy h2 h3 hT hg
  refine ⟨⟨_, hz⟩, ?_⟩
  apply ProjectiveSpectrum.ext
  apply homIdeal_ext
  intro g n hg
  obtain ⟨p, hp, hpg⟩ := Submodule.mem_map.mp hg
  have hpg' : g = mkB k p := hpg.symm
  subst hpg'
  have h1 : mkB k p ∈ pointIdeal k ⟨_, hz⟩ ↔ evalPair ![c, c'] (mk k ![b, -a] hv).rep p = 0 := by
    rw [mem_pointIdeal_iff k _ ⟨n, mk_mem_blowGrading k hp⟩, blowEv_mk]
  have h2' : evalPair ![c, c'] (mk k ![b, -a] hv).rep p = 0 ↔
      MvPolynomial.eval ![c, c', b, -a] p = 0 :=
    mem_projZeroSet_iff (isBihom_of_mem_bigrading hp) hv rfl
  exact h1.trans (h2'.trans (key hp).symm)
end surj

end Blowup
