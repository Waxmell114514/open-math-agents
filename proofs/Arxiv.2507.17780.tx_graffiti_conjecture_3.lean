import FormalConjectures.Arxiv.«2507.17780».«3»

-- Problem: TxGraffiti Conjecture 3
-- Credit: @Waxmell114514 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Counterexample: a connected cubic graph on 50 vertices (the incidence graph of a 3-CNF formula
on 15 variables and 20 clauses, each literal occurring exactly twice) with independent
domination number 16 and saturation number 15. Vertex 2(j-1) is the negative literal of
variable j, vertex 2(j-1)+1 the positive one, and vertex 29+a is clause a.
The lower bound i(G) ≥ 16 is proved by splitting the variables into a part A of 6 variables
and a part B of 9 variables, joined by 4 clauses, and checking each part by kernel evaluation.
-/

open SimpleGraph Finset

namespace OMA.TxG3

def nbT : List (List ℕ) := [[1, 38, 49], [0, 30, 32], [3, 40, 45], [2, 33, 35], [5, 35, 46], [4, 36, 41], [7, 31, 42], [6, 39, 44], [9, 34, 49], [8, 36, 38], [11, 34, 37], [10, 33, 49], [13, 39, 45], [12, 43, 44], [15, 42, 43], [14, 40, 47], [17, 32, 36], [16, 30, 41], [19, 31, 48], [18, 42, 47], [21, 30, 38], [20, 41, 46], [23, 37, 40], [22, 47, 48], [25, 31, 44], [24, 43, 48], [27, 32, 46], [26, 33, 45], [29, 37, 39], [28, 34, 35], [1, 17, 20], [6, 18, 24], [1, 16, 26], [3, 11, 27], [8, 10, 29], [3, 4, 29], [5, 9, 16], [10, 22, 28], [0, 9, 20], [7, 12, 28], [2, 15, 22], [5, 17, 21], [6, 14, 19], [13, 14, 25], [7, 13, 24], [2, 12, 27], [4, 21, 26], [15, 19, 23], [18, 23, 25], [0, 8, 11]]

def nbN (v i : ℕ) : ℕ := (nbT.getD v []).getD i 0

def adjB (u v : Fin 50) : Bool := (nbT.getD u.val []).contains v.val

def bAll (f : Bool → Bool) : Bool := f false && f true

theorem bAll_spec {f : Bool → Bool} (h : bAll f = true) (b : Bool) : f b = true := by
  cases b <;> simp_all [bAll]

def bImp (a c : Bool) : Bool := !a || c

theorem bImp_spec {a c : Bool} (h : bImp a c = true) (ha : a = true) : c = true := by
  simp_all [bImp]

theorem hb2 {a b : Bool} (h : a = true → b = false) : (!(a && b)) = true := by
  cases a <;> cases b <;> simp_all

theorem hb4 {a b c d : Bool} (h : a = true ∨ b = true ∨ c = true ∨ d = true) :
    (a || b || c || d) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

def TA (a1 a2 a3 a4 t1 t2 t3 t4 : Bool) : ℕ :=
  (13429589928599224621838761500052135553889454469465052557378095366302418710188412890809418630178838765730039390998680104182236629750653023750105930511950524680551761187487608795488925741166232863861022769082323739936423274180274656390390958773022818541029871930109105417388429249359921181145391264800390441663464635941019149406725231494687504064657584937034079577211921622881806253169286 / 32 ^ (a1.toNat + 2 * a2.toNat + 4 * a3.toNat + 8 * a4.toNat + 16 * t1.toNat + 32 * t2.toNat + 64 * t3.toNat + 128 * t4.toNat)) % 32

def TB (a1 a2 a3 a4 t1 t2 t3 t4 : Bool) : ℕ :=
  (13429589928599224621838813155490504711141308666627406173280800137218286354130484729119482988954498031500204364811597265254640933607280450301806570272844025161241732335332866747316034370771248395821580541268373718206851803999403593526425194877609231813917041285212911358559607792559773397830504365641114072027914639827215955276383477939620103008037618716318729921814044797068062956507433 / 32 ^ (a1.toNat + 2 * a2.toNat + 4 * a3.toNat + 8 * a4.toNat + 16 * t1.toNat + 32 * t2.toNat + 64 * t3.toNat + 128 * t4.toNat)) % 32

def chkA : Bool :=
  bAll fun x12 =>
  bAll fun x45 =>
  bImp (!(x45 && x12)) <|
  bAll fun x13 =>
  bImp (!(x12 && x13)) <|
  bAll fun x6 =>
  bAll fun x7 =>
  bImp (!(x6 && x7)) <|
  bAll fun x39 =>
  bImp (!(x39 && x7)) <|
  bImp (!(x39 && x12)) <|
  bImp (x12 || x13 || x39 || x45) <|
  bAll fun x22 =>
  bAll fun x37 =>
  bImp (!(x37 && x22)) <|
  bAll fun x23 =>
  bImp (!(x22 && x23)) <|
  bAll fun x14 =>
  bAll fun x15 =>
  bImp (!(x14 && x15)) <|
  bAll fun x40 =>
  bImp (!(x40 && x15)) <|
  bImp (!(x40 && x22)) <|
  bImp (x22 || x23 || x37 || x40) <|
  bAll fun x18 =>
  bAll fun x19 =>
  bImp (!(x18 && x19)) <|
  bAll fun x42 =>
  bImp (!(x42 && x6)) <|
  bImp (!(x42 && x14)) <|
  bImp (!(x42 && x19)) <|
  bImp (x42 || x6 || x14 || x19) <|
  bAll fun x47 =>
  bImp (!(x47 && x15)) <|
  bImp (!(x47 && x19)) <|
  bImp (!(x47 && x23)) <|
  bImp (x47 || x15 || x19 || x23) <|
  bImp (x15 || x14 || x40 || x47) <|
  bImp (x19 || x18 || x42 || x47) <|
  bAll fun x24 =>
  bAll fun x31 =>
  bImp (!(x31 && x6)) <|
  bImp (!(x31 && x18)) <|
  bImp (!(x31 && x24)) <|
  bImp (x31 || x6 || x18 || x24) <|
  bImp (x6 || x7 || x31 || x42) <|
  bAll fun x44 =>
  bImp (!(x44 && x7)) <|
  bImp (!(x44 && x13)) <|
  bImp (!(x44 && x24)) <|
  bImp (x44 || x7 || x13 || x24) <|
  bImp (x7 || x6 || x39 || x44) <|
  bAll fun x25 =>
  bImp (!(x24 && x25)) <|
  bImp (x24 || x25 || x31 || x44) <|
  bAll fun x43 =>
  bImp (!(x43 && x13)) <|
  bImp (!(x43 && x14)) <|
  bImp (!(x43 && x25)) <|
  bImp (x43 || x13 || x14 || x25) <|
  bImp (x13 || x12 || x43 || x44) <|
  bImp (x14 || x15 || x42 || x43) <|
  bAll fun x48 =>
  bImp (!(x48 && x18)) <|
  bImp (!(x48 && x23)) <|
  bImp (!(x48 && x25)) <|
  bImp (x48 || x18 || x23 || x25) <|
  bImp (x18 || x19 || x31 || x48) <|
  bImp (x23 || x22 || x47 || x48) <|
  bImp (x25 || x24 || x43 || x48) <|
  (decide (TA (x22) (x7 || x12) (x15 || x22) (x12) x37 x39 x40 x45 ≤ x6.toNat + x7.toNat + x12.toNat + x13.toNat + x14.toNat + x15.toNat + x18.toNat + x19.toNat + x22.toNat + x23.toNat + x24.toNat + x25.toNat + x31.toNat + x42.toNat + x43.toNat + x44.toNat + x47.toNat + x48.toNat))

theorem chkA_true : chkA = true := by
  decide +kernel

def chkB : Bool :=
  bAll fun x2 =>
  bAll fun x40 =>
  bImp (!(x40 && x2)) <|
  bAll fun x3 =>
  bImp (!(x2 && x3)) <|
  bAll fun x26 =>
  bAll fun x27 =>
  bImp (!(x26 && x27)) <|
  bAll fun x45 =>
  bImp (!(x45 && x2)) <|
  bImp (!(x45 && x27)) <|
  bImp (x2 || x3 || x40 || x45) <|
  bAll fun x10 =>
  bAll fun x11 =>
  bImp (!(x10 && x11)) <|
  bAll fun x33 =>
  bImp (!(x33 && x3)) <|
  bImp (!(x33 && x11)) <|
  bImp (!(x33 && x27)) <|
  bImp (x33 || x3 || x11 || x27) <|
  bImp (x27 || x26 || x33 || x45) <|
  bAll fun x28 =>
  bAll fun x37 =>
  bImp (!(x37 && x10)) <|
  bImp (!(x37 && x28)) <|
  bAll fun x39 =>
  bImp (!(x39 && x28)) <|
  bAll fun x29 =>
  bImp (!(x28 && x29)) <|
  bImp (x28 || x29 || x37 || x39) <|
  bAll fun x4 =>
  bAll fun x35 =>
  bImp (!(x35 && x3)) <|
  bImp (!(x35 && x4)) <|
  bImp (!(x35 && x29)) <|
  bImp (x35 || x3 || x4 || x29) <|
  bImp (x3 || x2 || x33 || x35) <|
  bAll fun x5 =>
  bImp (!(x4 && x5)) <|
  bAll fun x8 =>
  bAll fun x34 =>
  bImp (!(x34 && x8)) <|
  bImp (!(x34 && x10)) <|
  bImp (!(x34 && x29)) <|
  bImp (x34 || x8 || x10 || x29) <|
  bImp (x10 || x11 || x34 || x37) <|
  bImp (x29 || x28 || x34 || x35) <|
  bAll fun x9 =>
  bImp (!(x8 && x9)) <|
  bAll fun x0 =>
  bAll fun x49 =>
  bImp (!(x49 && x0)) <|
  bImp (!(x49 && x8)) <|
  bImp (!(x49 && x11)) <|
  bImp (x49 || x0 || x8 || x11) <|
  bImp (x8 || x9 || x34 || x49) <|
  bImp (x11 || x10 || x33 || x49) <|
  bAll fun x1 =>
  bImp (!(x0 && x1)) <|
  bAll fun x16 =>
  bAll fun x32 =>
  bImp (!(x32 && x1)) <|
  bImp (!(x32 && x16)) <|
  bImp (!(x32 && x26)) <|
  bImp (x32 || x1 || x16 || x26) <|
  bAll fun x36 =>
  bImp (!(x36 && x5)) <|
  bImp (!(x36 && x9)) <|
  bImp (!(x36 && x16)) <|
  bImp (x36 || x5 || x9 || x16) <|
  bAll fun x17 =>
  bImp (!(x16 && x17)) <|
  bImp (x16 || x17 || x32 || x36) <|
  bAll fun x20 =>
  bAll fun x30 =>
  bImp (!(x30 && x1)) <|
  bImp (!(x30 && x17)) <|
  bImp (!(x30 && x20)) <|
  bImp (x30 || x1 || x17 || x20) <|
  bImp (x1 || x0 || x30 || x32) <|
  bAll fun x38 =>
  bImp (!(x38 && x0)) <|
  bImp (!(x38 && x9)) <|
  bImp (!(x38 && x20)) <|
  bImp (x38 || x0 || x9 || x20) <|
  bImp (x0 || x1 || x38 || x49) <|
  bImp (x9 || x8 || x36 || x38) <|
  bAll fun x21 =>
  bImp (!(x20 && x21)) <|
  bImp (x20 || x21 || x30 || x38) <|
  bAll fun x41 =>
  bImp (!(x41 && x5)) <|
  bImp (!(x41 && x17)) <|
  bImp (!(x41 && x21)) <|
  bImp (x41 || x5 || x17 || x21) <|
  bImp (x5 || x4 || x36 || x41) <|
  bImp (x17 || x16 || x30 || x41) <|
  bAll fun x46 =>
  bImp (!(x46 && x4)) <|
  bImp (!(x46 && x21)) <|
  bImp (!(x46 && x26)) <|
  bImp (x46 || x4 || x21 || x26) <|
  bImp (x4 || x5 || x35 || x46) <|
  bImp (x21 || x20 || x41 || x46) <|
  bImp (x26 || x27 || x32 || x46) <|
  (decide (TB (x10 || x28) (x28) (x2) (x2 || x27) x37 x39 x40 x45 ≤ x0.toNat + x1.toNat + x2.toNat + x3.toNat + x4.toNat + x5.toNat + x8.toNat + x9.toNat + x10.toNat + x11.toNat + x16.toNat + x17.toNat + x20.toNat + x21.toNat + x26.toNat + x27.toNat + x28.toNat + x29.toNat + x30.toNat + x32.toNat + x33.toNat + x34.toNat + x35.toNat + x36.toNat + x38.toNat + x41.toNat + x46.toNat + x49.toNat))

theorem chkB_true : chkB = true := by
  decide +kernel

def chkC : Bool :=
  bAll fun x2 =>
  bAll fun x7 =>
  bAll fun x10 =>
  bAll fun x12 =>
  bAll fun x15 =>
  bAll fun x22 =>
  bAll fun x27 =>
  bAll fun x28 =>
  bAll fun x37 =>
  bImp (!(x37 && x10)) <|
  bImp (!(x37 && x22)) <|
  bImp (!(x37 && x28)) <|
  bImp (x37 || x10 || x22 || x28) <|
  bAll fun x39 =>
  bImp (!(x39 && x7)) <|
  bImp (!(x39 && x12)) <|
  bImp (!(x39 && x28)) <|
  bImp (x39 || x7 || x12 || x28) <|
  bAll fun x40 =>
  bImp (!(x40 && x2)) <|
  bImp (!(x40 && x15)) <|
  bImp (!(x40 && x22)) <|
  bImp (x40 || x2 || x15 || x22) <|
  bAll fun x45 =>
  bImp (!(x45 && x2)) <|
  bImp (!(x45 && x12)) <|
  bImp (!(x45 && x27)) <|
  bImp (x45 || x2 || x12 || x27) <|
  (decide (16 ≤ TA (x22) (x7 || x12) (x15 || x22) (x12) x37 x39 x40 x45 + TB (x10 || x28) (x28) (x2) (x2 || x27) x37 x39 x40 x45 + x37.toNat + x39.toNat + x40.toNat + x45.toNat))

theorem chkC_true : chkC = true := by
  decide +kernel

theorem core (x : ℕ → Bool)
    (hi : ∀ v : Fin 50, ∀ i : Fin 3, x v.val = true → x (nbN v.val i.val) = false)
    (hd : ∀ v : Fin 50, x v.val = true ∨ x (nbN v.val 0) = true ∨ x (nbN v.val 1) = true ∨ x (nbN v.val 2) = true) :
    16 ≤ ∑ k ∈ range 50, (x k).toNat := by
  have hA0 := chkA_true
  have hA1 := bAll_spec hA0 (x 12)
  have hA2 := bAll_spec hA1 (x 45)
  have hA3 := bImp_spec hA2 (hb2 (hi 45 1))
  have hA4 := bAll_spec hA3 (x 13)
  have hA5 := bImp_spec hA4 (hb2 (hi 12 0))
  have hA6 := bAll_spec hA5 (x 6)
  have hA7 := bAll_spec hA6 (x 7)
  have hA8 := bImp_spec hA7 (hb2 (hi 6 0))
  have hA9 := bAll_spec hA8 (x 39)
  have hA10 := bImp_spec hA9 (hb2 (hi 39 0))
  have hA11 := bImp_spec hA10 (hb2 (hi 39 1))
  have hA12 := bImp_spec hA11 (hb4 (hd 12))
  have hA13 := bAll_spec hA12 (x 22)
  have hA14 := bAll_spec hA13 (x 37)
  have hA15 := bImp_spec hA14 (hb2 (hi 37 1))
  have hA16 := bAll_spec hA15 (x 23)
  have hA17 := bImp_spec hA16 (hb2 (hi 22 0))
  have hA18 := bAll_spec hA17 (x 14)
  have hA19 := bAll_spec hA18 (x 15)
  have hA20 := bImp_spec hA19 (hb2 (hi 14 0))
  have hA21 := bAll_spec hA20 (x 40)
  have hA22 := bImp_spec hA21 (hb2 (hi 40 1))
  have hA23 := bImp_spec hA22 (hb2 (hi 40 2))
  have hA24 := bImp_spec hA23 (hb4 (hd 22))
  have hA25 := bAll_spec hA24 (x 18)
  have hA26 := bAll_spec hA25 (x 19)
  have hA27 := bImp_spec hA26 (hb2 (hi 18 0))
  have hA28 := bAll_spec hA27 (x 42)
  have hA29 := bImp_spec hA28 (hb2 (hi 42 0))
  have hA30 := bImp_spec hA29 (hb2 (hi 42 1))
  have hA31 := bImp_spec hA30 (hb2 (hi 42 2))
  have hA32 := bImp_spec hA31 (hb4 (hd 42))
  have hA33 := bAll_spec hA32 (x 47)
  have hA34 := bImp_spec hA33 (hb2 (hi 47 0))
  have hA35 := bImp_spec hA34 (hb2 (hi 47 1))
  have hA36 := bImp_spec hA35 (hb2 (hi 47 2))
  have hA37 := bImp_spec hA36 (hb4 (hd 47))
  have hA38 := bImp_spec hA37 (hb4 (hd 15))
  have hA39 := bImp_spec hA38 (hb4 (hd 19))
  have hA40 := bAll_spec hA39 (x 24)
  have hA41 := bAll_spec hA40 (x 31)
  have hA42 := bImp_spec hA41 (hb2 (hi 31 0))
  have hA43 := bImp_spec hA42 (hb2 (hi 31 1))
  have hA44 := bImp_spec hA43 (hb2 (hi 31 2))
  have hA45 := bImp_spec hA44 (hb4 (hd 31))
  have hA46 := bImp_spec hA45 (hb4 (hd 6))
  have hA47 := bAll_spec hA46 (x 44)
  have hA48 := bImp_spec hA47 (hb2 (hi 44 0))
  have hA49 := bImp_spec hA48 (hb2 (hi 44 1))
  have hA50 := bImp_spec hA49 (hb2 (hi 44 2))
  have hA51 := bImp_spec hA50 (hb4 (hd 44))
  have hA52 := bImp_spec hA51 (hb4 (hd 7))
  have hA53 := bAll_spec hA52 (x 25)
  have hA54 := bImp_spec hA53 (hb2 (hi 24 0))
  have hA55 := bImp_spec hA54 (hb4 (hd 24))
  have hA56 := bAll_spec hA55 (x 43)
  have hA57 := bImp_spec hA56 (hb2 (hi 43 0))
  have hA58 := bImp_spec hA57 (hb2 (hi 43 1))
  have hA59 := bImp_spec hA58 (hb2 (hi 43 2))
  have hA60 := bImp_spec hA59 (hb4 (hd 43))
  have hA61 := bImp_spec hA60 (hb4 (hd 13))
  have hA62 := bImp_spec hA61 (hb4 (hd 14))
  have hA63 := bAll_spec hA62 (x 48)
  have hA64 := bImp_spec hA63 (hb2 (hi 48 0))
  have hA65 := bImp_spec hA64 (hb2 (hi 48 1))
  have hA66 := bImp_spec hA65 (hb2 (hi 48 2))
  have hA67 := bImp_spec hA66 (hb4 (hd 48))
  have hA68 := bImp_spec hA67 (hb4 (hd 18))
  have hA69 := bImp_spec hA68 (hb4 (hd 23))
  have hA70 := bImp_spec hA69 (hb4 (hd 25))
  have hA := of_decide_eq_true hA70
  have hB0 := chkB_true
  have hB1 := bAll_spec hB0 (x 2)
  have hB2 := bAll_spec hB1 (x 40)
  have hB3 := bImp_spec hB2 (hb2 (hi 40 0))
  have hB4 := bAll_spec hB3 (x 3)
  have hB5 := bImp_spec hB4 (hb2 (hi 2 0))
  have hB6 := bAll_spec hB5 (x 26)
  have hB7 := bAll_spec hB6 (x 27)
  have hB8 := bImp_spec hB7 (hb2 (hi 26 0))
  have hB9 := bAll_spec hB8 (x 45)
  have hB10 := bImp_spec hB9 (hb2 (hi 45 0))
  have hB11 := bImp_spec hB10 (hb2 (hi 45 2))
  have hB12 := bImp_spec hB11 (hb4 (hd 2))
  have hB13 := bAll_spec hB12 (x 10)
  have hB14 := bAll_spec hB13 (x 11)
  have hB15 := bImp_spec hB14 (hb2 (hi 10 0))
  have hB16 := bAll_spec hB15 (x 33)
  have hB17 := bImp_spec hB16 (hb2 (hi 33 0))
  have hB18 := bImp_spec hB17 (hb2 (hi 33 1))
  have hB19 := bImp_spec hB18 (hb2 (hi 33 2))
  have hB20 := bImp_spec hB19 (hb4 (hd 33))
  have hB21 := bImp_spec hB20 (hb4 (hd 27))
  have hB22 := bAll_spec hB21 (x 28)
  have hB23 := bAll_spec hB22 (x 37)
  have hB24 := bImp_spec hB23 (hb2 (hi 37 0))
  have hB25 := bImp_spec hB24 (hb2 (hi 37 2))
  have hB26 := bAll_spec hB25 (x 39)
  have hB27 := bImp_spec hB26 (hb2 (hi 39 2))
  have hB28 := bAll_spec hB27 (x 29)
  have hB29 := bImp_spec hB28 (hb2 (hi 28 0))
  have hB30 := bImp_spec hB29 (hb4 (hd 28))
  have hB31 := bAll_spec hB30 (x 4)
  have hB32 := bAll_spec hB31 (x 35)
  have hB33 := bImp_spec hB32 (hb2 (hi 35 0))
  have hB34 := bImp_spec hB33 (hb2 (hi 35 1))
  have hB35 := bImp_spec hB34 (hb2 (hi 35 2))
  have hB36 := bImp_spec hB35 (hb4 (hd 35))
  have hB37 := bImp_spec hB36 (hb4 (hd 3))
  have hB38 := bAll_spec hB37 (x 5)
  have hB39 := bImp_spec hB38 (hb2 (hi 4 0))
  have hB40 := bAll_spec hB39 (x 8)
  have hB41 := bAll_spec hB40 (x 34)
  have hB42 := bImp_spec hB41 (hb2 (hi 34 0))
  have hB43 := bImp_spec hB42 (hb2 (hi 34 1))
  have hB44 := bImp_spec hB43 (hb2 (hi 34 2))
  have hB45 := bImp_spec hB44 (hb4 (hd 34))
  have hB46 := bImp_spec hB45 (hb4 (hd 10))
  have hB47 := bImp_spec hB46 (hb4 (hd 29))
  have hB48 := bAll_spec hB47 (x 9)
  have hB49 := bImp_spec hB48 (hb2 (hi 8 0))
  have hB50 := bAll_spec hB49 (x 0)
  have hB51 := bAll_spec hB50 (x 49)
  have hB52 := bImp_spec hB51 (hb2 (hi 49 0))
  have hB53 := bImp_spec hB52 (hb2 (hi 49 1))
  have hB54 := bImp_spec hB53 (hb2 (hi 49 2))
  have hB55 := bImp_spec hB54 (hb4 (hd 49))
  have hB56 := bImp_spec hB55 (hb4 (hd 8))
  have hB57 := bImp_spec hB56 (hb4 (hd 11))
  have hB58 := bAll_spec hB57 (x 1)
  have hB59 := bImp_spec hB58 (hb2 (hi 0 0))
  have hB60 := bAll_spec hB59 (x 16)
  have hB61 := bAll_spec hB60 (x 32)
  have hB62 := bImp_spec hB61 (hb2 (hi 32 0))
  have hB63 := bImp_spec hB62 (hb2 (hi 32 1))
  have hB64 := bImp_spec hB63 (hb2 (hi 32 2))
  have hB65 := bImp_spec hB64 (hb4 (hd 32))
  have hB66 := bAll_spec hB65 (x 36)
  have hB67 := bImp_spec hB66 (hb2 (hi 36 0))
  have hB68 := bImp_spec hB67 (hb2 (hi 36 1))
  have hB69 := bImp_spec hB68 (hb2 (hi 36 2))
  have hB70 := bImp_spec hB69 (hb4 (hd 36))
  have hB71 := bAll_spec hB70 (x 17)
  have hB72 := bImp_spec hB71 (hb2 (hi 16 0))
  have hB73 := bImp_spec hB72 (hb4 (hd 16))
  have hB74 := bAll_spec hB73 (x 20)
  have hB75 := bAll_spec hB74 (x 30)
  have hB76 := bImp_spec hB75 (hb2 (hi 30 0))
  have hB77 := bImp_spec hB76 (hb2 (hi 30 1))
  have hB78 := bImp_spec hB77 (hb2 (hi 30 2))
  have hB79 := bImp_spec hB78 (hb4 (hd 30))
  have hB80 := bImp_spec hB79 (hb4 (hd 1))
  have hB81 := bAll_spec hB80 (x 38)
  have hB82 := bImp_spec hB81 (hb2 (hi 38 0))
  have hB83 := bImp_spec hB82 (hb2 (hi 38 1))
  have hB84 := bImp_spec hB83 (hb2 (hi 38 2))
  have hB85 := bImp_spec hB84 (hb4 (hd 38))
  have hB86 := bImp_spec hB85 (hb4 (hd 0))
  have hB87 := bImp_spec hB86 (hb4 (hd 9))
  have hB88 := bAll_spec hB87 (x 21)
  have hB89 := bImp_spec hB88 (hb2 (hi 20 0))
  have hB90 := bImp_spec hB89 (hb4 (hd 20))
  have hB91 := bAll_spec hB90 (x 41)
  have hB92 := bImp_spec hB91 (hb2 (hi 41 0))
  have hB93 := bImp_spec hB92 (hb2 (hi 41 1))
  have hB94 := bImp_spec hB93 (hb2 (hi 41 2))
  have hB95 := bImp_spec hB94 (hb4 (hd 41))
  have hB96 := bImp_spec hB95 (hb4 (hd 5))
  have hB97 := bImp_spec hB96 (hb4 (hd 17))
  have hB98 := bAll_spec hB97 (x 46)
  have hB99 := bImp_spec hB98 (hb2 (hi 46 0))
  have hB100 := bImp_spec hB99 (hb2 (hi 46 1))
  have hB101 := bImp_spec hB100 (hb2 (hi 46 2))
  have hB102 := bImp_spec hB101 (hb4 (hd 46))
  have hB103 := bImp_spec hB102 (hb4 (hd 4))
  have hB104 := bImp_spec hB103 (hb4 (hd 21))
  have hB105 := bImp_spec hB104 (hb4 (hd 26))
  have hB := of_decide_eq_true hB105
  have hC0 := chkC_true
  have hC1 := bAll_spec hC0 (x 2)
  have hC2 := bAll_spec hC1 (x 7)
  have hC3 := bAll_spec hC2 (x 10)
  have hC4 := bAll_spec hC3 (x 12)
  have hC5 := bAll_spec hC4 (x 15)
  have hC6 := bAll_spec hC5 (x 22)
  have hC7 := bAll_spec hC6 (x 27)
  have hC8 := bAll_spec hC7 (x 28)
  have hC9 := bAll_spec hC8 (x 37)
  have hC10 := bImp_spec hC9 (hb2 (hi 37 0))
  have hC11 := bImp_spec hC10 (hb2 (hi 37 1))
  have hC12 := bImp_spec hC11 (hb2 (hi 37 2))
  have hC13 := bImp_spec hC12 (hb4 (hd 37))
  have hC14 := bAll_spec hC13 (x 39)
  have hC15 := bImp_spec hC14 (hb2 (hi 39 0))
  have hC16 := bImp_spec hC15 (hb2 (hi 39 1))
  have hC17 := bImp_spec hC16 (hb2 (hi 39 2))
  have hC18 := bImp_spec hC17 (hb4 (hd 39))
  have hC19 := bAll_spec hC18 (x 40)
  have hC20 := bImp_spec hC19 (hb2 (hi 40 0))
  have hC21 := bImp_spec hC20 (hb2 (hi 40 1))
  have hC22 := bImp_spec hC21 (hb2 (hi 40 2))
  have hC23 := bImp_spec hC22 (hb4 (hd 40))
  have hC24 := bAll_spec hC23 (x 45)
  have hC25 := bImp_spec hC24 (hb2 (hi 45 0))
  have hC26 := bImp_spec hC25 (hb2 (hi 45 1))
  have hC27 := bImp_spec hC26 (hb2 (hi 45 2))
  have hC28 := bImp_spec hC27 (hb4 (hd 45))
  have hC := of_decide_eq_true hC28
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  omega

theorem adjB_symm : ∀ u v : Fin 50, adjB u v = true → adjB v u = true := by
  decide +kernel

theorem adjB_irrefl : ∀ u : Fin 50, adjB u u = false := by
  decide +kernel

def G : SimpleGraph (Fin 50) where
  Adj u v := adjB u v = true
  symm := ⟨fun u v h => adjB_symm u v h⟩
  loopless := ⟨fun u h => by
    have := adjB_irrefl u
    simp_all⟩

instance instDecAdj : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (adjB u v = true))

theorem deg3 : ∀ v : Fin 50, G.degree v = 3 := by
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  revert v
  decide +kernel

def nb (v : Fin 50) (i : Fin 3) : Fin 50 := ⟨nbN v.val i.val % 50, Nat.mod_lt _ (by norm_num)⟩

theorem nb_val : ∀ v : Fin 50, ∀ i : Fin 3, (nb v i).val = nbN v.val i.val := by
  decide +kernel

theorem adj_nb : ∀ v : Fin 50, ∀ i : Fin 3, adjB v (nb v i) = true := by
  decide +kernel

theorem nbr_cases : ∀ v w : Fin 50, adjB v w = true → w = nb v 0 ∨ w = nb v 1 ∨ w = nb v 2 := by
  decide +kernel

theorem card_ge (D : Finset (Fin 50)) (hI : G.IsIndepSet (D : Set (Fin 50)))
    (hD : G.IsDominating (D : Set (Fin 50))) : 16 ≤ D.card := by
  set x : ℕ → Bool := fun k => if h : k < 50 then decide ((⟨k, h⟩ : Fin 50) ∈ D) else false with hx
  have xv : ∀ v : Fin 50, x v.val = decide (v ∈ D) := by
    intro v
    simp [hx, v.isLt]
  have xn : ∀ v : Fin 50, ∀ i : Fin 3, x (nbN v.val i.val) = decide (nb v i ∈ D) := by
    intro v i
    rw [← nb_val v i, xv]
  have hi : ∀ v : Fin 50, ∀ i : Fin 3, x v.val = true → x (nbN v.val i.val) = false := by
    intro v i h
    rw [xv] at h
    rw [xn]
    have hv : v ∈ D := of_decide_eq_true h
    by_contra hw
    have hw' : nb v i ∈ D := by simpa using hw
    have hne : v ≠ nb v i := by
      intro he
      have h1 := adj_nb v i
      rw [← he, adjB_irrefl] at h1
      exact Bool.false_ne_true h1
    exact hI (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hw') hne (adj_nb v i)
  have hd : ∀ v : Fin 50, x v.val = true ∨ x (nbN v.val 0) = true ∨ x (nbN v.val 1) = true ∨
      x (nbN v.val 2) = true := by
    intro v
    have e0 := xn v 0
    have e1 := xn v 1
    have e2 := xn v 2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
    rw [xv, e0, e1, e2]
    rcases hD v with h | ⟨w, hw, hadj⟩
    · left; simpa using h
    · have hw' : w ∈ D := Finset.mem_coe.mp hw
      rcases nbr_cases v w hadj with h | h | h
      · right; left; rw [← h]; simpa using hw'
      · right; right; left; rw [← h]; simpa using hw'
      · right; right; right; rw [← h]; simpa using hw'
  have hc := core x hi hd
  have hsum : ∑ k ∈ range 50, (x k).toNat = D.card := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => (x k).toNat) 50]
    simp only [xv]
    rw [Finset.card_eq_sum_ones, ← Finset.sum_subset (Finset.subset_univ D)]
    · apply Finset.sum_congr rfl
      intro v hv
      simp [hv]
    · intro v _ hv
      simp [hv]
  omega

def D0 : Finset (Fin 50) := {0, 2, 5, 7, 8, 13, 15, 30, 31, 32, 33, 35, 37, 42, 46, 48}

theorem D0_noadj : ∀ u ∈ D0, ∀ v ∈ D0, adjB u v = false := by
  decide +kernel

theorem D0_dom : ∀ v : Fin 50, v ∈ D0 ∨ ∃ w ∈ D0, adjB v w = true := by
  decide +kernel

theorem D0_ids : G.IsNIndepDominatingSet 16 D0 := by
  refine ⟨?_, ?_, by decide⟩
  · intro u hu v hv _ hadj
    have h := D0_noadj u (Finset.mem_coe.mp hu) v (Finset.mem_coe.mp hv)
    change adjB u v = true at hadj
    rw [h] at hadj
    exact Bool.false_ne_true hadj
  · intro v
    rcases D0_dom v with h | ⟨w, hw, hadj⟩
    · exact Or.inl (Finset.mem_coe.mpr h)
    · exact Or.inr ⟨w, Finset.mem_coe.mpr hw, hadj⟩

theorem i_ge : 16 ≤ G.indepDominationNumber := by
  unfold SimpleGraph.indepDominationNumber
  refine le_csInf ⟨16, D0, D0_ids⟩ ?_
  rintro n ⟨D, hD⟩
  rw [← hD.card_eq]
  exact card_ge D hD.isIndep hD.isDominating

def M : Finset (Sym2 (Fin 50)) :=
  {s(0, 1), s(2, 3), s(4, 5), s(6, 7), s(8, 9), s(10, 11), s(12, 13), s(14, 15), s(16, 17),
    s(18, 19), s(20, 21), s(22, 23), s(24, 25), s(26, 27), s(28, 29)}

theorem M_matching : G.IsEdgeMatching M := by
  unfold SimpleGraph.IsEdgeMatching
  decide +kernel

def pe (a : Fin 50) : Sym2 (Fin 50) :=
  s(⟨a.val / 2 * 2 % 50, Nat.mod_lt _ (by norm_num)⟩, ⟨(a.val / 2 * 2 + 1) % 50, Nat.mod_lt _ (by norm_num)⟩)

theorem pe_spec : ∀ a b : Fin 50, adjB a b = true →
    (pe a ∈ M ∧ a ∈ pe a) ∨ (pe b ∈ M ∧ b ∈ pe b) := by
  decide +kernel

theorem M_max : G.IsMaximalEdgeMatching M := by
  refine ⟨M_matching, ?_⟩
  intro e
  induction e using Sym2.ind with
  | h a b =>
    intro he heM hmat
    have hab : adjB a b = true := he
    have key : ∀ c : Fin 50, c ∈ s(a, b) → pe c ∈ M → c ∈ pe c → False := by
      intro c hc hpM hcp
      rcases hmat.2 s(a, b) (Finset.mem_insert_self _ _) (pe c) (Finset.mem_insert_of_mem hpM) with
        h | h
      · exact heM (h ▸ hpM)
      · exact h c ⟨hc, hcp⟩
    rcases pe_spec a b hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key a (Sym2.mem_mk_left a b) h1 h2
    · exact key b (Sym2.mem_mk_right a b) h1 h2

theorem mu_le : G.saturationNumber ≤ 15 := by
  unfold SimpleGraph.saturationNumber
  exact Nat.sInf_le ⟨M, M_max, by decide⟩

end OMA.TxG3

theorem OMA.disproof : ¬ (type_of% @Arxiv.«2507.17780».tx_graffiti_conjecture_3) := by
  intro h
  have h1 := h (Fin 50) OMA.TxG3.G 3 OMA.TxG3.deg3 (by norm_num)
  have h2 := OMA.TxG3.i_ge
  have h3 := OMA.TxG3.mu_le
  omega

