import FormalConjectures.ErdosProblems.«939»

-- Problem: Erdős Problem 939 — infinite of six le
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/939.lean:92 (declaration Erdos939.erdos_939.variants.infinite_of_six_le)
-- Credit: @Waxmell114514 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Construction. Let B = (2^(r+1))!, Y = B^r, and X = q^r for a prime q > B. Then
--   (X + Y)^r = (X - Y)^r + sum over odd j of 2 * C(r, j) * X^(r-j) * Y^j.
-- Every coefficient divides B, so every term is r-full. The j = 3 term is split into
-- the pieces 1, 2, ..., m - 1 and a remainder (times X^(r-3) * Y^3), with m = r/2 - 2,
-- which gives exactly r - 2 summands. The exponent of q separates the terms, (X - Y) is
-- coprime to q and to B, and distinct primes q give sums that grow without bound.

namespace OMA939

open Nat Finset

lemma full_mul {r a b : ℕ} (ha : r.Full a) (hb : r.Full b) : r.Full (a * b) := by
  intro p hp
  obtain ⟨hpr, hdvd, hne⟩ := Nat.mem_primeFactors.mp hp
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hne
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hne
  rcases (Nat.Prime.dvd_mul hpr).mp hdvd with h | h
  · exact Dvd.dvd.mul_right (ha p (Nat.mem_primeFactors.mpr ⟨hpr, h, ha0⟩)) b
  · exact Dvd.dvd.mul_left (hb p (Nat.mem_primeFactors.mpr ⟨hpr, h, hb0⟩)) a

lemma full_pow {r a : ℕ} (ha : r.Full a) (k : ℕ) : r.Full (a ^ k) := by
  induction k with
  | zero => simpa using Nat.Full.one_right r
  | succ k ih => rw [pow_succ]; exact full_mul ih ha

lemma full_pow_self (r a : ℕ) : r.Full (a ^ r) := by
  intro p hp
  obtain ⟨hpr, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  exact pow_dvd_pow_of_dvd (hpr.dvd_of_dvd_pow hdvd) r

lemma full_coef {r d B M : ℕ} (hd : d ∣ B) (hM : r.Full M) : r.Full (d * B ^ r * M) := by
  intro p hp
  obtain ⟨hpr, hdvd, hne⟩ := Nat.mem_primeFactors.mp hp
  have hM0 : M ≠ 0 := right_ne_zero_of_mul hne
  rcases (Nat.Prime.dvd_mul hpr).mp hdvd with h | h
  · have hpB : p ∣ B := by
      rcases (Nat.Prime.dvd_mul hpr).mp h with h' | h'
      · exact h'.trans hd
      · exact hpr.dvd_of_dvd_pow h'
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hpB r) d) M
  · exact Dvd.dvd.mul_left (hM p (Nat.mem_primeFactors.mpr ⟨hpr, h, hM0⟩)) _

/-- A term `d * X^a * Y^b` with `b ≥ 1` and `d ∣ B` is `r`-full. -/
lemma full_elem {r d B q a b : ℕ} (hd : d ∣ B) (hb : 1 ≤ b) :
    r.Full (d * (q ^ r) ^ a * (B ^ r) ^ b) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hb
  have e : d * (q ^ r) ^ a * (B ^ r) ^ (1 + c) = d * B ^ r * ((q ^ r) ^ a * (B ^ r) ^ c) := by
    ring
  rw [e]
  exact full_coef hd (full_mul (full_pow (full_pow_self r q) a) (full_pow (full_pow_self r B) c))

/-- The exponent of `q` in `d * X^a * Y^b`. -/
lemma fact_q {q B d r a b : ℕ} (hq : q.Prime) (hqB : ¬ q ∣ B) (hB : 0 < B) (hd : 0 < d)
    (hqd : ¬ q ∣ d) : (d * (q ^ r) ^ a * (B ^ r) ^ b).factorization q = r * a := by
  have hq0 : 0 < q := hq.pos
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp [Nat.factorization_pow, hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hqd,
    Nat.factorization_eq_zero_of_not_dvd hqB, mul_comm]

lemma binom_id (r X Y : ℕ) (h : Y ≤ X) :
    (X + Y) ^ r = (X - Y) ^ r +
      ∑ j ∈ (range (r + 1)).filter Odd, 2 * r.choose j * X ^ (r - j) * Y ^ j := by
  have key : ((X : ℤ) + Y) ^ r = ((X : ℤ) - Y) ^ r +
      ∑ j ∈ (range (r + 1)).filter Odd, (2 * r.choose j * (X : ℤ) ^ (r - j) * (Y : ℤ) ^ j) := by
    rw [Finset.sum_filter]
    have h1 : ((X : ℤ) + Y) ^ r = ∑ j ∈ range (r + 1), (Y : ℤ) ^ j * (X : ℤ) ^ (r - j) * r.choose j := by
      rw [add_comm]; exact add_pow _ _ _
    have h2 : ((X : ℤ) - Y) ^ r =
        ∑ j ∈ range (r + 1), (-(Y : ℤ)) ^ j * (X : ℤ) ^ (r - j) * r.choose j := by
      rw [sub_eq_neg_add]; exact add_pow _ _ _
    rw [h1, h2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rcases Nat.even_or_odd j with he | ho
    · simp [he.neg_pow, Nat.not_odd_iff_even.mpr he]
    · simp [ho.neg_pow, ho]; ring
  have key' : (((X + Y) ^ r : ℕ) : ℤ) = (((X - Y) ^ r +
      ∑ j ∈ (range (r + 1)).filter Odd, 2 * r.choose j * X ^ (r - j) * Y ^ j : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h]
    exact key
  exact_mod_cast key'

lemma card_odd (n : ℕ) : ((range n).filter Odd).card = n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]
      obtain ⟨k, rfl⟩ := h
      omega
    · rw [ih]
      rw [Nat.not_odd_iff_even] at h
      obtain ⟨k, rfl⟩ := h
      omega

lemma ineq (r : ℕ) (hr : 6 ≤ r) :
    (r / 2 - 2 - 1) * (r / 2 - 2 - 1) + (r / 2 - 2) ≤ 2 * r.choose 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 6 := ⟨r - 6, by omega⟩
  have h := Nat.descFactorial_eq_factorial_mul_choose (t + 6) 3
  simp [Nat.descFactorial_succ, Nat.factorial] at h
  set m := (t + 6) / 2 - 2 with hm
  have h2m : 2 * m ≤ t + 2 := by omega
  have hsq : (m - 1) * (m - 1) ≤ m * m := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have h4 : (2 * m) * (2 * m) ≤ (t + 2) * (t + 2) := Nat.mul_le_mul h2m h2m
  have h5 : 4 * (m * m + m) ≤ (t + 4) * ((t + 5) * (t + 6)) := by nlinarith
  linarith

lemma construction (r q : ℕ) (hr : 6 ≤ r) (hq : q.Prime) (hBq : (2 ^ (r + 1))! < q) :
    ∃ S : Finset ℕ, S ∈ Erdos939.Erdos939Sums r ∧
      ∑ x ∈ S, x = (q ^ r + ((2 ^ (r + 1))!) ^ r) ^ r := by
  set K := 2 ^ (r + 1) with hK
  set B := K ! with hBdef
  set X := q ^ r with hX
  set Y := B ^ r with hY
  set m := r / 2 - 2 with hm
  set c := 2 * r.choose 3 with hc
  set s := ∑ i ∈ range (m - 1), (i + 1) with hs
  set T : ℕ → ℕ := fun j => 2 * r.choose j * X ^ (r - j) * Y ^ j with hT
  set W : ℕ → ℕ := fun d => d * X ^ (r - 3) * Y ^ 3 with hW
  set I1 := ((range (r + 1)).filter Odd).erase 3 with hI1
  set A1 := I1.image T with hA1
  set A2 := (range (m - 1)).image (fun i => W (i + 1)) with hA2
  set P := W (c - s) with hP
  set E0 := (X - Y) ^ r with hE0def
  have hr0 : r ≠ 0 := by omega
  have hq0 : 0 < q := hq.pos
  have hKB : K ≤ B := Nat.self_le_factorial K
  have hrK : r < K := by
    calc r < 2 ^ r := Nat.lt_two_pow_self
      _ ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB1 : 1 < B := by omega
  have hB0 : 0 < B := by omega
  have hqB : ¬ q ∣ B := by
    rw [hBdef, hq.dvd_factorial]
    omega
  have hcoefK : ∀ d, 0 < d → d ≤ K → d ∣ B ∧ ¬ q ∣ d := fun d hd hdK =>
    ⟨Nat.dvd_factorial hd hdK, Nat.not_dvd_of_pos_of_lt hd (by omega)⟩
  have hchoose : ∀ j, 2 * r.choose j ≤ K := fun j => by
    rw [hK, pow_succ]
    have := Nat.choose_le_two_pow r j
    omega
  have hX0 : 0 < X := pow_pos hq0 r
  have hY0 : 0 < Y := pow_pos hB0 r
  have hYX : Y < X := Nat.pow_lt_pow_left hBq hr0
  have hsle : s ≤ (m - 1) * (m - 1) := by
    have := Finset.sum_le_card_nsmul (range (m - 1)) (fun i => i + 1) (m - 1)
      (fun i hi => by rw [Finset.mem_range] at hi; omega)
    simpa using this
  have hineq : (m - 1) * (m - 1) + m ≤ c := ineq r hr
  have hcs : m ≤ c - s := by omega
  have hcK : c ≤ K := hchoose 3
  have hsc : s ≤ c := by omega
  have hpos : 0 < X ^ (r - 3) * Y ^ 3 := Nat.mul_pos (pow_pos hX0 _) (pow_pos hY0 _)
  -- the index set
  have hmemI1 : ∀ j ∈ I1, Odd j ∧ j ≤ r ∧ j ≠ 3 ∧ 1 ≤ j := by
    intro j hj
    rw [hI1, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨k, hk⟩ := hj.2.2
    exact ⟨hj.2.2, by omega, hj.1, by omega⟩
  have h3 : 3 ∈ (range (r + 1)).filter Odd := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by decide⟩
  have h1I1 : 1 ∈ I1 := by
    rw [hI1, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    exact ⟨by decide, by omega, by decide⟩
  -- exponents of q
  have vT : ∀ j, j ≤ r → (T j).factorization q = r * (r - j) := fun j hj => by
    have hC := Nat.choose_pos hj
    exact fact_q hq hqB hB0 (by omega) (hcoefK _ (by omega) (hchoose j)).2
  have vW : ∀ d, 0 < d → d ≤ K → (W d).factorization q = r * (r - 3) := fun d hd hdK =>
    fact_q hq hqB hB0 hd (hcoefK d hd hdK).2
  -- every term except E0 is a multiple of B
  have BdvdT : ∀ j, 1 ≤ j → B ∣ T j := fun j hj =>
    Dvd.dvd.mul_left (dvd_pow (dvd_pow_self B hr0) (by omega)) _
  have BdvdW : ∀ d, B ∣ W d := fun d =>
    Dvd.dvd.mul_left (dvd_pow (dvd_pow_self B hr0) (by norm_num)) _
  -- coprimality
  have hcopqB : Nat.Coprime q B := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqB
  have hXY : X - Y + Y = X := Nat.sub_add_cancel hYX.le
  have hcopD_B : Nat.Coprime (X - Y) B := by
    have h1 : Nat.Coprime X B := Nat.Coprime.pow_left r hcopqB
    have h2 : X = (X - Y) + B ^ (r - 1) * B := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
      omega
    rw [h2] at h1
    exact (Nat.coprime_add_mul_right_left _ _ _).mp h1
  have hcopD_q : Nat.Coprime (X - Y) q := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hq]
    intro hd
    have hqX : q ∣ X := dvd_pow_self q hr0
    rw [← hXY] at hqX
    exact hqB (hq.dvd_of_dvd_pow ((Nat.dvd_add_right hd).mp hqX))
  have hcopE0_B : Nat.Coprime E0 B := Nat.Coprime.pow_left r hcopD_B
  have hcopE0_q : Nat.Coprime E0 q := Nat.Coprime.pow_left r hcopD_q
  -- distinctness
  have hinjT : Set.InjOn T I1 := by
    intro j1 h1 j2 h2 he
    have a1 := hmemI1 j1 h1
    have a2 := hmemI1 j2 h2
    have hv : (T j1).factorization q = (T j2).factorization q := by rw [he]
    rw [vT j1 a1.2.1, vT j2 a2.2.1] at hv
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < r) hv
    omega
  have hinjW : Set.InjOn (fun i => W (i + 1)) (range (m - 1)) := by
    intro i1 _ i2 _ he
    simp only [hW] at he
    rw [mul_assoc, mul_assoc] at he
    have := Nat.eq_of_mul_eq_mul_right hpos he
    omega
  have hPA2 : P ∉ A2 := by
    rw [hA2, Finset.mem_image]
    rintro ⟨i, hi, he⟩
    rw [Finset.mem_range] at hi
    simp only [hW, hP] at he
    rw [mul_assoc, mul_assoc] at he
    have := Nat.eq_of_mul_eq_mul_right hpos he
    omega
  have hdisj : Disjoint A1 (insert P A2) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hA1, Finset.mem_image] at hx1
    obtain ⟨j, hj, rfl⟩ := hx1
    have a := hmemI1 j hj
    have v2 : (T j).factorization q = r * (r - 3) := by
      rw [Finset.mem_insert, hA2, Finset.mem_image] at hx2
      rcases hx2 with h | ⟨i, hi, h⟩
      · rw [h]
        exact vW _ (by omega) (by omega)
      · rw [← h]
        rw [Finset.mem_range] at hi
        exact vW _ (by omega) (by omega)
    rw [vT j a.2.1] at v2
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < r) v2
    omega
  have hE0 : E0 ∉ A1 ∪ insert P A2 := by
    intro hmem
    have hBd : B ∣ E0 := by
      rw [Finset.mem_union, Finset.mem_insert] at hmem
      rcases hmem with h | h | h
      · rw [hA1, Finset.mem_image] at h
        obtain ⟨j, hj, hj'⟩ := h
        rw [← hj']
        exact BdvdT j (hmemI1 j hj).2.2.2
      · rw [h]
        exact BdvdW _
      · rw [hA2, Finset.mem_image] at h
        obtain ⟨i, _, hi'⟩ := h
        rw [← hi']
        exact BdvdW _
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcopE0_B) hBd
    omega
  -- the sum
  have hsum : ∑ x ∈ insert E0 (A1 ∪ insert P A2), x = (X + Y) ^ r := by
    rw [Finset.sum_insert hE0, Finset.sum_union hdisj, Finset.sum_insert hPA2, hA1,
      Finset.sum_image hinjT, hA2, Finset.sum_image hinjW]
    have hW' : P + ∑ i ∈ range (m - 1), W (i + 1) = T 3 := by
      simp only [hP, hW, hT]
      rw [show ∑ i ∈ range (m - 1), (i + 1) * X ^ (r - 3) * Y ^ 3 = s * X ^ (r - 3) * Y ^ 3 by
        rw [hs, Finset.sum_mul, Finset.sum_mul]]
      rw [← add_mul, ← add_mul, Nat.sub_add_cancel hsc]
    rw [hW', hI1, Finset.sum_erase_add _ _ h3, binom_id r X Y hYX.le]
  refine ⟨insert E0 (A1 ∪ insert P A2), ?_, hsum⟩
  simp only [Erdos939.Erdos939Sums, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hE0, Finset.card_union_of_disjoint hdisj,
      Finset.card_insert_of_notMem hPA2, hA1, Finset.card_image_of_injOn hinjT, hA2,
      Finset.card_image_of_injOn hinjW, Finset.card_range, hI1, Finset.card_erase_of_mem h3,
      card_odd]
    omega
  · have g1 : (insert E0 (A1 ∪ insert P A2)).gcd id ∣ E0 :=
      Finset.gcd_dvd (Finset.mem_insert_self _ _)
    have h1mem : T 1 ∈ insert E0 (A1 ∪ insert P A2) :=
      Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem T h1I1))
    have g2 : (insert E0 (A1 ∪ insert P A2)).gcd id ∣ T 1 := Finset.gcd_dvd h1mem
    have hcop : Nat.Coprime E0 (T 1) := by
      simp only [hT]
      refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_
      · exact Nat.Coprime.coprime_dvd_right
          (hcoefK _ (by simp; omega) (hchoose 1)).1 hcopE0_B
      · exact Nat.Coprime.pow_right _ (Nat.Coprime.pow_right r hcopE0_q)
      · exact Nat.Coprime.pow_right _ (Nat.Coprime.pow_right r hcopE0_B)
    have := Nat.dvd_gcd g1 g2
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    exact Nat.dvd_one.mp this
  · rw [hsum]
    exact full_pow_self r (X + Y)
  · intro x hx
    rw [Finset.mem_insert, Finset.mem_union, Finset.mem_insert] at hx
    rcases hx with h | h | h | h
    · rw [h]
      exact ⟨pow_pos (Nat.sub_pos_of_lt hYX) r, full_pow_self r _⟩
    · rw [hA1, Finset.mem_image] at h
      obtain ⟨j, hj, hj'⟩ := h
      rw [← hj']
      have a := hmemI1 j hj
      have hC := Nat.choose_pos a.2.1
      refine ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos two_pos hC) (pow_pos hX0 _)) (pow_pos hY0 _), ?_⟩
      exact full_elem (hcoefK _ (by omega) (hchoose j)).1 a.2.2.2
    · rw [h]
      refine ⟨Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos hX0 _)) (pow_pos hY0 _), ?_⟩
      exact full_elem (hcoefK _ (by omega) (by omega)).1 (by norm_num)
    · rw [hA2, Finset.mem_image] at h
      obtain ⟨i, hi, hi'⟩ := h
      rw [← hi']
      rw [Finset.mem_range] at hi
      refine ⟨Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos hX0 _)) (pow_pos hY0 _), ?_⟩
      exact full_elem (hcoefK _ (by omega) (by omega)).1 (by norm_num)

end OMA939

open OMA939 Nat in
theorem OMA.solution : type_of% @Erdos939.erdos_939.variants.infinite_of_six_le := by
  intro r hr hfin
  obtain ⟨N, hN⟩ := (hfin.image (fun S : Finset ℕ => ∑ x ∈ S, x)).bddAbove
  obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (max ((2 ^ (r + 1))!) N + 1)
  have hm1 := le_max_left ((2 ^ (r + 1))!) N
  have hm2 := le_max_right ((2 ^ (r + 1))!) N
  obtain ⟨S, hS, hsum⟩ := construction r q hr hq (by omega)
  have hle : ∑ x ∈ S, x ≤ N := hN (Set.mem_image_of_mem _ hS)
  rw [hsum] at hle
  have h1 : q ≤ q ^ r := Nat.le_self_pow (by omega) q
  have h2 : q ^ r + ((2 ^ (r + 1))!) ^ r ≤ (q ^ r + ((2 ^ (r + 1))!) ^ r) ^ r :=
    Nat.le_self_pow (by omega) _
  omega
