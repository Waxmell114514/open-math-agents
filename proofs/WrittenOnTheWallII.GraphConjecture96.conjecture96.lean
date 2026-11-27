import FormalConjectures.WrittenOnTheWallII.GraphConjecture96

-- Problem: Written on the Wall II - Conjecture 96
-- Credit: @Waxmell114514 (the owner of the agent is credited as the solver)
--
-- Proof outline. Fix any vertex v, let E be the set of vertices at even distance from v and
-- let L = max_z l(z). Take a maximum independent set I. Send every vertex u of I at even
-- distance to itself and every vertex at odd distance to a neighbour one step closer to v
-- (which is at even distance). Consider the fibre of a vertex z of E.
-- * If z is in I, the fibre is {z} (an odd vertex sent to z is adjacent to z).
-- * Otherwise the fibre is an independent set of neighbours of z at distance d(v,z) + 1;
--   for z different from v, adding a neighbour of z one step closer to v keeps it independent
--   (distances differ by two), so the fibre has at most l(z) - 1 <= L - 1 elements;
--   for z = v it has at most l(v) <= L elements.
-- When L >= 2 this gives alpha <= L + (|E| - 1)(L - 1) = 1 + |E| (L - 1).
-- When L = 1 every neighbourhood is a clique, which forces alpha <= 1.

namespace OMA96

open SimpleGraph Finset Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma dist_le_one_of_adj {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : G.dist a b ≤ 1 := by
  simpa using SimpleGraph.dist_le (Walk.cons h Walk.nil)

lemma dist_adj_le {G : SimpleGraph V} (hG : G.Connected) (v : V) {a b : V} (h : G.Adj a b) :
    G.dist v b ≤ G.dist v a + 1 := by
  have h1 := hG.dist_triangle (u := v) (v := a) (w := b)
  have h2 := dist_le_one_of_adj h
  omega

lemma exists_pred {G : SimpleGraph V} (hG : G.Connected) (v u : V) (hu : u ≠ v) :
    ∃ w, G.Adj u w ∧ G.dist v w + 1 = G.dist v u := by
  obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist u v
  obtain ⟨w, huw, q', rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hu q
  refine ⟨w, huw, ?_⟩
  have h1 : G.dist w v ≤ q'.length := SimpleGraph.dist_le q'
  simp only [Walk.length_cons] at hq
  have h2 := dist_adj_le hG v huw.symm
  rw [SimpleGraph.dist_comm (u := v) (v := w), SimpleGraph.dist_comm (u := v) (v := u)] at *
  have h3 : G.dist u v ≤ G.dist w v + 1 := by
    have := hG.dist_triangle (u := u) (v := w) (w := v)
    have := dist_le_one_of_adj huw
    omega
  omega

lemma card_le_indepNeighbors (G : SimpleGraph V) (z : V) (A : Finset V)
    (hA : ∀ a ∈ A, G.Adj z a) (hI : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ G.Adj a b) :
    A.card ≤ indepNeighborsCard G z := by
  unfold indepNeighborsCard
  let s : Finset (G.neighborSet z) := A.subtype (fun x => x ∈ G.neighborSet z)
  have hs : s.card = A.card := by
    simp only [s, Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun a ha => hA a ha)
  have hind : (G.induce (G.neighborSet z)).IsIndepSet (s : Set (G.neighborSet z)) := by
    intro x hx y hy hxy hadj
    have hx' : x.1 ∈ A := Finset.mem_subtype.mp (Finset.mem_coe.mp hx)
    have hy' : y.1 ∈ A := Finset.mem_subtype.mp (Finset.mem_coe.mp hy)
    have hne : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    exact hI x.1 hx' y.1 hy' hne hadj
  rw [← hs]
  exact hind.card_le_indepNum

/-- The main counting bound, valid for every vertex `v` when the local independence is at least 2. -/
lemma main_bound (G : SimpleGraph V) (hG : G.Connected) (v : V) (L : ℕ) (hL : 2 ≤ L)
    (hLz : ∀ z, indepNeighborsCard G z ≤ L) (I : Finset V) (hI : G.IsIndepSet (I : Set V)) :
    I.card ≤ L + ((univ.filter fun w => Even (G.dist v w)).card - 1) * (L - 1) := by
  set E := univ.filter fun w => Even (G.dist v w) with hE
  let pred : V → V := fun u => if h : u ≠ v then Classical.choose (exists_pred hG v u h) else v
  have hpred : ∀ u, u ≠ v → G.Adj u (pred u) ∧ G.dist v (pred u) + 1 = G.dist v u := by
    intro u hu
    simp only [pred, dif_pos hu]
    exact Classical.choose_spec (exists_pred hG v u hu)
  let φ : V → V := fun u => if Even (G.dist v u) then u else pred u
  have hvE : v ∈ E := by simp [E]
  have hφ : ∀ u ∈ I, φ u ∈ E := by
    intro u _
    by_cases he : Even (G.dist v u)
    · simp only [φ, if_pos he]; simp [E, he]
    · simp only [φ, if_neg he]
      have huv : u ≠ v := by rintro rfl; simp at he
      have := (hpred u huv).2
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Nat.not_even_iff_odd] at he
      obtain ⟨k, hk⟩ := he
      exact ⟨k, by omega⟩
  rw [Finset.card_eq_sum_card_fiberwise hφ]
  have hfib : ∀ z ∈ E, (I.filter fun u => φ u = z).card ≤ if z = v then L else L - 1 := by
    intro z hz
    have hzE : Even (G.dist v z) := (Finset.mem_filter.mp hz).2
    set F := I.filter fun u => φ u = z with hF
    by_cases hzI : z ∈ I
    · have hsub : F ⊆ {z} := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨huI, hφu⟩ := hu
        rw [Finset.mem_singleton]
        by_cases he : Even (G.dist v u)
        · simpa [φ, he] using hφu
        · exfalso
          simp only [φ, if_neg he] at hφu
          have huv : u ≠ v := by rintro rfl; simp at he
          have hadj := (hpred u huv).1
          rw [hφu] at hadj
          have hne : u ≠ z := by rintro rfl; exact G.irrefl hadj
          exact hI huI hzI hne hadj
      have h1 : F.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
      split_ifs <;> omega
    · -- every element of the fibre is a neighbour of z one step further from v
      have hFprop : ∀ u ∈ F, G.Adj z u ∧ G.dist v u = G.dist v z + 1 := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨huI, hφu⟩ := hu
        by_cases he : Even (G.dist v u)
        · simp only [φ, if_pos he] at hφu
          exact absurd (hφu ▸ huI) hzI
        · simp only [φ, if_neg he] at hφu
          have huv : u ≠ v := by rintro rfl; simp at he
          have h := hpred u huv
          rw [hφu] at h
          exact ⟨h.1.symm, by omega⟩
      have hFind : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ¬ G.Adj a b := by
        intro a ha b hb hab
        exact hI (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
      by_cases hzv : z = v
      · rw [if_pos hzv]
        exact (card_le_indepNeighbors G z F (fun u hu => (hFprop u hu).1) hFind).trans (hLz z)
      · rw [if_neg hzv]
        obtain ⟨hzp, hdp⟩ := hpred z hzv
        set p := pred z
        have hpF : p ∉ F := by
          intro hp
          have := (hFprop p hp).2
          omega
        have hins : (insert p F).card ≤ indepNeighborsCard G z := by
          apply card_le_indepNeighbors
          · intro a ha
            rcases Finset.mem_insert.mp ha with ha | ha
            · rw [ha]; exact hzp
            · exact (hFprop a ha).1
          · intro a ha b hb hab
            rcases Finset.mem_insert.mp ha with ha | ha <;> rcases Finset.mem_insert.mp hb with hb | hb
            · exact absurd (ha.trans hb.symm) hab
            · intro hadj
              rw [ha] at hadj
              have h1 := (hFprop b hb).2
              have h2 := dist_adj_le hG v hadj
              omega
            · intro hadj
              rw [hb] at hadj
              have h1 := (hFprop a ha).2
              have h2 := dist_adj_le hG v hadj.symm
              omega
            · exact hFind a ha b hb hab
        rw [Finset.card_insert_of_notMem hpF] at hins
        have := hLz z
        omega
  calc ∑ z ∈ E, (I.filter fun u => φ u = z).card
      ≤ ∑ z ∈ E, (if z = v then L else L - 1) := Finset.sum_le_sum hfib
    _ = L + (E.card - 1) * (L - 1) := by
      rw [← Finset.add_sum_erase E _ hvE, if_pos rfl]
      rw [Finset.sum_congr rfl (fun z hz => if_neg (Finset.ne_of_mem_erase hz))]
      rw [Finset.sum_const, Finset.card_erase_of_mem hvE, smul_eq_mul]

/-- If every neighbourhood is a clique, the graph has independence number at most one. -/
lemma indep_le_one (G : SimpleGraph V) (hG : G.Connected) (hLz : ∀ z, indepNeighborsCard G z ≤ 1)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) : I.card ≤ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hcon
  have hnadj : ¬ G.Adj u w := hI hu hw huw
  obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist u w
  obtain ⟨m, hum, q', rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne huw q
  have hmw : m ≠ w := by rintro rfl; exact hnadj hum
  obtain ⟨t, hmt, q'', rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hmw q'
  simp only [Walk.length_cons] at hq
  have hdt : G.dist t w ≤ q''.length := SimpleGraph.dist_le q''
  have hut : u ≠ t := by
    rintro rfl
    have := hG.dist_triangle (u := u) (v := u) (w := w)
    simp at this
    omega
  have hnut : ¬ G.Adj u t := by
    intro hadj
    have h1 := hG.dist_triangle (u := u) (v := t) (w := w)
    have h2 := dist_le_one_of_adj hadj
    omega
  have h2 : ({u, t} : Finset V).card ≤ indepNeighborsCard G m := by
    apply card_le_indepNeighbors
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hum.symm
      · exact hmt
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hnut
      · exact fun h => hnut h.symm
      · exact absurd rfl hab
  rw [Finset.card_pair hut] at h2
  have := hLz m
  omega

end OMA96

open OMA96 SimpleGraph Classical in
theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture96.conjecture96 := by
  intro α _ _ _ G hG
  set mE := (Finset.univ.image (distEven G)).min'
    (Finset.image_nonempty.mpr Finset.univ_nonempty) with hmE
  set L := (Finset.univ.image (fun v => indepNeighborsCard G v)).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty) with hL
  show (G.indepNum : ℝ) ≤ 1 + (mE : ℝ) * ((L : ℝ) - 1)
  have hmem : mE ∈ Finset.univ.image (distEven G) := Finset.min'_mem _ _
  obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hmem
  have hLz : ∀ z, indepNeighborsCard G z ≤ L := fun z =>
    Finset.le_max' _ _ (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩)
  obtain ⟨I, hIs⟩ := G.exists_isNIndepSet_indepNum
  have hIcard : I.card = G.indepNum := hIs.card_eq
  -- L is at least one: v has a neighbour
  have hL1 : 1 ≤ L := by
    obtain ⟨u, hu⟩ := exists_ne v
    obtain ⟨q, -⟩ := hG.exists_walk_length_eq_dist v u
    obtain ⟨a, hva, -, -⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hu.symm q
    have h1 : ({a} : Finset α).card ≤ indepNeighborsCard G v := by
      apply card_le_indepNeighbors
      · intro b hb; rw [Finset.mem_singleton] at hb; subst hb; exact hva
      · intro b hb c hc hbc
        rw [Finset.mem_singleton] at hb hc; subst hb; subst hc; exact absurd rfl hbc
    simp at h1
    exact h1.trans (hLz v)
  have hE1 : 1 ≤ mE := by
    rw [← hv]
    unfold distEven
    apply Finset.card_pos.mpr
    exact ⟨v, by simp⟩
  rcases Nat.lt_or_ge L 2 with hL2 | hL2
  · have hL1' : L = 1 := by omega
    have hI1 : I.card ≤ 1 := indep_le_one G hG (fun z => hL1' ▸ hLz z) I hIs.isIndepSet
    rw [← hIcard, hL1']
    have : (I.card : ℝ) ≤ 1 := by exact_mod_cast hI1
    push_cast
    nlinarith
  · have hb := main_bound G hG v L hL2 hLz I hIs.isIndepSet
    have hEv : (Finset.univ.filter fun w => Even (G.dist v w)).card = mE := hv
    rw [hEv] at hb
    rw [← hIcard]
    have hcast : ((L + (mE - 1) * (L - 1) : ℕ) : ℝ) = 1 + (mE : ℝ) * ((L : ℝ) - 1) := by
      push_cast [Nat.cast_sub hE1, Nat.cast_sub hL1]
      ring
    rw [← hcast]
    exact_mod_cast hb
