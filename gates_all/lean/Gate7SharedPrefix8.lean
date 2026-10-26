import Mathlib

namespace CPOQWord

/-- An exact accelerated odd Collatz step, with odd positive input and odd quotient. -/
def ExactStep (x y v : Nat) : Prop :=
  0 < x ∧ (∃ t : Nat, x = 2*t+1) ∧
  2^v * y = 3*x+1 ∧ (∃ t : Nat, y = 2*t+1)

/-- Exact valuation word, represented as a chain of exact accelerated steps. -/
inductive Word : List Nat → Nat → Nat → Prop where
  | nil (x : Nat) : Word [] x x
  | cons {v : Nat} {vs : List Nat} {x y z : Nat}
      (hstep : ExactStep x y v) (htail : Word vs y z) :
      Word (v :: vs) x z

/-- One-step exact transport: a 2^(v+1) input shift preserves valuation v. -/
theorem step_transport (x y v d : Nat) (h : ExactStep x y v) :
    ExactStep (x + 2^(v+1)*d) (y+6*d) v := by
  rcases h with ⟨hx, ⟨a, ha⟩, heq, ⟨b, hb⟩⟩
  refine ⟨by omega, ?_, ?_, ?_⟩
  · refine ⟨a + 2^v*d, ?_⟩
    rw [ha, pow_succ]
    ring
  · rw [pow_succ]
    nlinarith [heq]
  · refine ⟨b+3*d, ?_⟩
    rw [hb]
    ring

/-- The exact valuation word survives any displacement divisible by
    2^(sum of valuations + 1). Its output displacement is 2*3^length*d.
    The extra +1 bit ensures the last quotient stays odd. -/
theorem word_transport {vs : List Nat} {x y : Nat}
    (h : Word vs x y) (d : Nat) :
    Word vs (x + 2^(vs.sum+1)*d) (y + 2*3^vs.length*d) := by
  induction h generalizing d with
  | nil x =>
      simp only [List.sum_nil, List.length_nil, pow_zero]
      convert Word.nil (x + 2*d) using 1
  | @cons v vs x mid y hstep htail ih =>
      have hpow : 2^((v :: vs).sum+1)*d =
          2^(v+1)*(2^vs.sum*d) := by
        simp only [List.sum_cons]
        rw [show v + vs.sum + 1 = (v+1)+vs.sum by omega, pow_add]
        ring
      have hout : 6*(2^vs.sum*d) = 2^(vs.sum+1)*(3*d) := by
        rw [pow_succ]
        ring
      have hfirst : ExactStep
          (x + 2^((v :: vs).sum+1)*d)
          (mid + 2^(vs.sum+1)*(3*d)) v := by
        rw [hpow, ← hout]
        exact step_transport x mid v (2^vs.sum*d) hstep
      have hrest := ih (3*d)
      have hlast : y + 2*3^vs.length*(3*d) =
          y + 2*3^(v :: vs).length*d := by
        simp only [List.length_cons, pow_succ]
        ring
      rw [← hlast]
      exact Word.cons hfirst hrest

/-- If the representative descends and the exact word contracts in slope,
    every nonnegative member of the precision cylinder descends too. -/
theorem word_uniform_descent {vs : List Nat} {x y : Nat}
    (hword : Word vs x y)
    (hbase : y < x)
    (hslope : 3^vs.length < 2^vs.sum)
    (d : Nat) :
    ∃ z : Nat,
      Word vs (x + 2^(vs.sum+1)*d) z ∧
      z < x + 2^(vs.sum+1)*d := by
  let z := y + 2*3^vs.length*d
  have hpath : Word vs (x + 2^(vs.sum+1)*d) z :=
    word_transport hword d
  have hshift : 2*3^vs.length*d ≤ 2^(vs.sum+1)*d := by
    calc
      2*3^vs.length*d = 3^vs.length*(2*d) := by ring
      _ ≤ 2^vs.sum*(2*d) :=
        Nat.mul_le_mul_right (2*d) (Nat.le_of_lt hslope)
      _ = 2^(vs.sum+1)*d := by rw [pow_succ]; ring
  refine ⟨z, hpath, ?_⟩
  dsimp [z]
  omega

#print axioms word_uniform_descent

#print axioms step_transport
#print axioms word_transport

/-- Exact concatenation of valuation words. -/
theorem word_append {as bs : List Nat} {x y z : Nat}
    (ha : Word as x y) (hb : Word bs y z) :
    Word (as ++ bs) x z := by
  induction ha with
  | nil _ => simpa using hb
  | cons hstep htail ih =>
      simpa using Word.cons hstep (ih hb)

/-- Shared 40-step prefix, valid for every q in the O5/8 source progression. -/
def sharedPrefix : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1]

theorem shared_prefix_base : Word sharedPrefix 118140960795 4983230072969 := by
  unfold sharedPrefix
  exact Word.cons
        (show ExactStep 118140960795 177211441193 1 from by
          refine ⟨by norm_num, ⟨59070480397, by norm_num⟩, by norm_num, ⟨88605720596, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 177211441193 132908580895 2 from by
          refine ⟨by norm_num, ⟨88605720596, by norm_num⟩, by norm_num, ⟨66454290447, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 132908580895 199362871343 1 from by
          refine ⟨by norm_num, ⟨66454290447, by norm_num⟩, by norm_num, ⟨99681435671, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 199362871343 299044307015 1 from by
          refine ⟨by norm_num, ⟨99681435671, by norm_num⟩, by norm_num, ⟨149522153507, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 299044307015 448566460523 1 from by
          refine ⟨by norm_num, ⟨149522153507, by norm_num⟩, by norm_num, ⟨224283230261, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 448566460523 672849690785 1 from by
          refine ⟨by norm_num, ⟨224283230261, by norm_num⟩, by norm_num, ⟨336424845392, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 672849690785 504637268089 2 from by
          refine ⟨by norm_num, ⟨336424845392, by norm_num⟩, by norm_num, ⟨252318634044, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 504637268089 378477951067 2 from by
          refine ⟨by norm_num, ⟨252318634044, by norm_num⟩, by norm_num, ⟨189238975533, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 378477951067 567716926601 1 from by
          refine ⟨by norm_num, ⟨189238975533, by norm_num⟩, by norm_num, ⟨283858463300, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 567716926601 425787694951 2 from by
          refine ⟨by norm_num, ⟨283858463300, by norm_num⟩, by norm_num, ⟨212893847475, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 425787694951 638681542427 1 from by
          refine ⟨by norm_num, ⟨212893847475, by norm_num⟩, by norm_num, ⟨319340771213, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 638681542427 958022313641 1 from by
          refine ⟨by norm_num, ⟨319340771213, by norm_num⟩, by norm_num, ⟨479011156820, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 958022313641 718516735231 2 from by
          refine ⟨by norm_num, ⟨479011156820, by norm_num⟩, by norm_num, ⟨359258367615, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 718516735231 1077775102847 1 from by
          refine ⟨by norm_num, ⟨359258367615, by norm_num⟩, by norm_num, ⟨538887551423, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1077775102847 1616662654271 1 from by
          refine ⟨by norm_num, ⟨538887551423, by norm_num⟩, by norm_num, ⟨808331327135, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1616662654271 2424993981407 1 from by
          refine ⟨by norm_num, ⟨808331327135, by norm_num⟩, by norm_num, ⟨1212496990703, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2424993981407 3637490972111 1 from by
          refine ⟨by norm_num, ⟨1212496990703, by norm_num⟩, by norm_num, ⟨1818745486055, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 3637490972111 5456236458167 1 from by
          refine ⟨by norm_num, ⟨1818745486055, by norm_num⟩, by norm_num, ⟨2728118229083, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 5456236458167 8184354687251 1 from by
          refine ⟨by norm_num, ⟨2728118229083, by norm_num⟩, by norm_num, ⟨4092177343625, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 8184354687251 12276532030877 1 from by
          refine ⟨by norm_num, ⟨4092177343625, by norm_num⟩, by norm_num, ⟨6138266015438, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 12276532030877 4603699511579 3 from by
          refine ⟨by norm_num, ⟨6138266015438, by norm_num⟩, by norm_num, ⟨2301849755789, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 4603699511579 6905549267369 1 from by
          refine ⟨by norm_num, ⟨2301849755789, by norm_num⟩, by norm_num, ⟨3452774633684, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 6905549267369 5179161950527 2 from by
          refine ⟨by norm_num, ⟨3452774633684, by norm_num⟩, by norm_num, ⟨2589580975263, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 5179161950527 7768742925791 1 from by
          refine ⟨by norm_num, ⟨2589580975263, by norm_num⟩, by norm_num, ⟨3884371462895, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 7768742925791 11653114388687 1 from by
          refine ⟨by norm_num, ⟨3884371462895, by norm_num⟩, by norm_num, ⟨5826557194343, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 11653114388687 17479671583031 1 from by
          refine ⟨by norm_num, ⟨5826557194343, by norm_num⟩, by norm_num, ⟨8739835791515, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 17479671583031 26219507374547 1 from by
          refine ⟨by norm_num, ⟨8739835791515, by norm_num⟩, by norm_num, ⟨13109753687273, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 26219507374547 39329261061821 1 from by
          refine ⟨by norm_num, ⟨13109753687273, by norm_num⟩, by norm_num, ⟨19664630530910, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 39329261061821 14748472898183 3 from by
          refine ⟨by norm_num, ⟨19664630530910, by norm_num⟩, by norm_num, ⟨7374236449091, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 14748472898183 22122709347275 1 from by
          refine ⟨by norm_num, ⟨7374236449091, by norm_num⟩, by norm_num, ⟨11061354673637, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 22122709347275 33184064020913 1 from by
          refine ⟨by norm_num, ⟨11061354673637, by norm_num⟩, by norm_num, ⟨16592032010456, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 33184064020913 24888048015685 2 from by
          refine ⟨by norm_num, ⟨16592032010456, by norm_num⟩, by norm_num, ⟨12444024007842, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 24888048015685 4666509002941 4 from by
          refine ⟨by norm_num, ⟨12444024007842, by norm_num⟩, by norm_num, ⟨2333254501470, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 4666509002941 1749940876103 3 from by
          refine ⟨by norm_num, ⟨2333254501470, by norm_num⟩, by norm_num, ⟨874970438051, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1749940876103 2624911314155 1 from by
          refine ⟨by norm_num, ⟨874970438051, by norm_num⟩, by norm_num, ⟨1312455657077, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2624911314155 3937366971233 1 from by
          refine ⟨by norm_num, ⟨1312455657077, by norm_num⟩, by norm_num, ⟨1968683485616, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 3937366971233 2953025228425 2 from by
          refine ⟨by norm_num, ⟨1968683485616, by norm_num⟩, by norm_num, ⟨1476512614212, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2953025228425 2214768921319 2 from by
          refine ⟨by norm_num, ⟨1476512614212, by norm_num⟩, by norm_num, ⟨1107384460659, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2214768921319 3322153381979 1 from by
          refine ⟨by norm_num, ⟨1107384460659, by norm_num⟩, by norm_num, ⟨1661076690989, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 3322153381979 4983230072969 1 from by
          refine ⟨by norm_num, ⟨1661076690989, by norm_num⟩, by norm_num, ⟨2491615036484, by norm_num⟩⟩)
        (Word.nil 4983230072969))))))))))))))))))))))))))))))))))))))))

theorem shared_prefix_sum : sharedPrefix.sum = 58 := by decide
theorem shared_prefix_length : sharedPrefix.length = 40 := by decide

/-- Reuse one concrete proof across ALL q, not just the selected sample. -/
theorem shared_prefix_all (q : Nat) :
    Word sharedPrefix (118140960795 + 2^59*q)
      (4983230072969 + 2*3^40*q) := by
  have h := word_transport shared_prefix_base q
  simpa [shared_prefix_sum, shared_prefix_length] using h


/-- Recorded row 0, q=10880, bits=15, full length=46. -/
def suffix_0 : List Nat := [2, 1, 1, 2, 1, 8]
def word_0 : List Nat := sharedPrefix ++ suffix_0

theorem suffix_proof_0 : Word suffix_0 264550800394062000782729 5885544845192602495441 := by
  unfold suffix_0
  exact Word.cons
        (show ExactStep 264550800394062000782729 198413100295546500587047 2 from by
          refine ⟨by norm_num, ⟨132275400197031000391364, by norm_num⟩, by norm_num, ⟨99206550147773250293523, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 198413100295546500587047 297619650443319750880571 1 from by
          refine ⟨by norm_num, ⟨99206550147773250293523, by norm_num⟩, by norm_num, ⟨148809825221659875440285, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 297619650443319750880571 446429475664979626320857 1 from by
          refine ⟨by norm_num, ⟨148809825221659875440285, by norm_num⟩, by norm_num, ⟨223214737832489813160428, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 446429475664979626320857 334822106748734719740643 2 from by
          refine ⟨by norm_num, ⟨223214737832489813160428, by norm_num⟩, by norm_num, ⟨167411053374367359870321, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 334822106748734719740643 502233160123102079610965 1 from by
          refine ⟨by norm_num, ⟨167411053374367359870321, by norm_num⟩, by norm_num, ⟨251116580061551039805482, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 502233160123102079610965 5885544845192602495441 8 from by
          refine ⟨by norm_num, ⟨251116580061551039805482, by norm_num⟩, by norm_num, ⟨2942772422596301247720, by norm_num⟩⟩)
        (Word.nil 5885544845192602495441))))))

theorem full_word_0 : Word word_0 6271892985179388510235 5885544845192602495441 := by
  unfold word_0
  have hp := shared_prefix_all 10880
  have ht := suffix_proof_0
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_0 : word_0.length = 46 := by decide
theorem word_sum_0 : word_0.sum = 73 := by decide

theorem infinite_family_0 (d : Nat) :
    ∃ z : Nat, Word word_0 (6271892985179388510235 + 2^74*d) z ∧
      z < 6271892985179388510235 + 2^74*d := by
  have h := word_uniform_descent full_word_0
    (show 5885544845192602495441 < 6271892985179388510235 by norm_num)
    (show 3^word_0.length < 2^word_0.sum by norm_num [word_0, sharedPrefix, suffix_0]) d
  simpa [word_sum_0] using h

/-- Recorded row 1, q=27264, bits=16, full length=46. -/
def suffix_1 : List Nat := [2, 1, 1, 2, 1, 9]
def word_1 : List Nat := sharedPrefix ++ suffix_1

theorem suffix_proof_1 : Word suffix_1 662933182156439443733897 7374241482422551795685 := by
  unfold suffix_1
  exact Word.cons
        (show ExactStep 662933182156439443733897 497199886617329582800423 2 from by
          refine ⟨by norm_num, ⟨331466591078219721866948, by norm_num⟩, by norm_num, ⟨248599943308664791400211, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 497199886617329582800423 745799829925994374200635 1 from by
          refine ⟨by norm_num, ⟨248599943308664791400211, by norm_num⟩, by norm_num, ⟨372899914962997187100317, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 745799829925994374200635 1118699744888991561300953 1 from by
          refine ⟨by norm_num, ⟨372899914962997187100317, by norm_num⟩, by norm_num, ⟨559349872444495780650476, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1118699744888991561300953 839024808666743670975715 2 from by
          refine ⟨by norm_num, ⟨559349872444495780650476, by norm_num⟩, by norm_num, ⟨419512404333371835487857, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 839024808666743670975715 1258537213000115506463573 1 from by
          refine ⟨by norm_num, ⟨419512404333371835487857, by norm_num⟩, by norm_num, ⟨629268606500057753231786, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1258537213000115506463573 7374241482422551795685 9 from by
          refine ⟨by norm_num, ⟨629268606500057753231786, by norm_num⟩, by norm_num, ⟨3687120741211275897842, by norm_num⟩⟩)
        (Word.nil 7374241482422551795685))))))

theorem full_word_1 : Word word_1 15716625950918678937627 7374241482422551795685 := by
  unfold word_1
  have hp := shared_prefix_all 27264
  have ht := suffix_proof_1
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_1 : word_1.length = 46 := by decide
theorem word_sum_1 : word_1.sum = 74 := by decide

theorem infinite_family_1 (d : Nat) :
    ∃ z : Nat, Word word_1 (15716625950918678937627 + 2^75*d) z ∧
      z < 15716625950918678937627 + 2^75*d := by
  have h := word_uniform_descent full_word_1
    (show 7374241482422551795685 < 15716625950918678937627 by norm_num)
    (show 3^word_1.length < 2^word_1.sum by norm_num [word_1, sharedPrefix, suffix_1]) d
  simpa [word_sum_1] using h

/-- Recorded row 2, q=6208, bits=15, full length=46. -/
def suffix_2 : List Nat := [2, 1, 1, 2, 2, 7]
def word_2 : List Nat := sharedPrefix ++ suffix_2

theorem suffix_proof_2 : Word suffix_2 150949574344634058066185 3358222647010443979805 := by
  unfold suffix_2
  exact Word.cons
        (show ExactStep 150949574344634058066185 113212180758475543549639 2 from by
          refine ⟨by norm_num, ⟨75474787172317029033092, by norm_num⟩, by norm_num, ⟨56606090379237771774819, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 113212180758475543549639 169818271137713315324459 1 from by
          refine ⟨by norm_num, ⟨56606090379237771774819, by norm_num⟩, by norm_num, ⟨84909135568856657662229, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 169818271137713315324459 254727406706569972986689 1 from by
          refine ⟨by norm_num, ⟨84909135568856657662229, by norm_num⟩, by norm_num, ⟨127363703353284986493344, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 254727406706569972986689 191045555029927479740017 2 from by
          refine ⟨by norm_num, ⟨127363703353284986493344, by norm_num⟩, by norm_num, ⟨95522777514963739870008, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 191045555029927479740017 143284166272445609805013 2 from by
          refine ⟨by norm_num, ⟨95522777514963739870008, by norm_num⟩, by norm_num, ⟨71642083136222804902506, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 143284166272445609805013 3358222647010443979805 7 from by
          refine ⟨by norm_num, ⟨71642083136222804902506, by norm_num⟩, by norm_num, ⟨1679111323505221989902, by norm_num⟩⟩)
        (Word.nil 3358222647010443979805))))))

theorem full_word_2 : Word word_2 3578668350417793974299 3358222647010443979805 := by
  unfold word_2
  have hp := shared_prefix_all 6208
  have ht := suffix_proof_2
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_2 : word_2.length = 46 := by decide
theorem word_sum_2 : word_2.sum = 73 := by decide

theorem infinite_family_2 (d : Nat) :
    ∃ z : Nat, Word word_2 (3578668350417793974299 + 2^74*d) z ∧
      z < 3578668350417793974299 + 2^74*d := by
  have h := word_uniform_descent full_word_2
    (show 3358222647010443979805 < 3578668350417793974299 by norm_num)
    (show 3^word_2.length < 2^word_2.sum by norm_num [word_2, sharedPrefix, suffix_2]) d
  simpa [word_sum_2] using h

/-- Recorded row 3, q=22592, bits=16, full length=46. -/
def suffix_3 : List Nat := [2, 1, 1, 2, 2, 8]
def word_3 : List Nat := sharedPrefix ++ suffix_3

theorem suffix_proof_3 : Word suffix_3 549331956107011501017353 6110580383331472537867 := by
  unfold suffix_3
  exact Word.cons
        (show ExactStep 549331956107011501017353 411998967080258625763015 2 from by
          refine ⟨by norm_num, ⟨274665978053505750508676, by norm_num⟩, by norm_num, ⟨205999483540129312881507, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 411998967080258625763015 617998450620387938644523 1 from by
          refine ⟨by norm_num, ⟨205999483540129312881507, by norm_num⟩, by norm_num, ⟨308999225310193969322261, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 617998450620387938644523 926997675930581907966785 1 from by
          refine ⟨by norm_num, ⟨308999225310193969322261, by norm_num⟩, by norm_num, ⟨463498837965290953983392, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 926997675930581907966785 695248256947936430975089 2 from by
          refine ⟨by norm_num, ⟨463498837965290953983392, by norm_num⟩, by norm_num, ⟨347624128473968215487544, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 695248256947936430975089 521436192710952323231317 2 from by
          refine ⟨by norm_num, ⟨347624128473968215487544, by norm_num⟩, by norm_num, ⟨260718096355476161615658, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 521436192710952323231317 6110580383331472537867 8 from by
          refine ⟨by norm_num, ⟨260718096355476161615658, by norm_num⟩, by norm_num, ⟨3055290191665736268933, by norm_num⟩⟩)
        (Word.nil 6110580383331472537867))))))

theorem full_word_3 : Word word_3 13023401316157084401691 6110580383331472537867 := by
  unfold word_3
  have hp := shared_prefix_all 22592
  have ht := suffix_proof_3
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_3 : word_3.length = 46 := by decide
theorem word_sum_3 : word_3.sum = 74 := by decide

theorem infinite_family_3 (d : Nat) :
    ∃ z : Nat, Word word_3 (13023401316157084401691 + 2^75*d) z ∧
      z < 13023401316157084401691 + 2^75*d := by
  have h := word_uniform_descent full_word_3
    (show 6110580383331472537867 < 13023401316157084401691 by norm_num)
    (show 3^word_3.length < 2^word_3.sum by norm_num [word_3, sharedPrefix, suffix_3]) d
  simpa [word_sum_3] using h

/-- Recorded row 4, q=6336, bits=15, full length=46. -/
def suffix_4 : List Nat := [2, 1, 1, 2, 5, 4]
def word_4 : List Nat := sharedPrefix ++ suffix_4

theorem suffix_proof_4 : Word suffix_4 154061936702152631839241 3427464351070229144617 := by
  unfold suffix_4
  exact Word.cons
        (show ExactStep 154061936702152631839241 115546452526614473879431 2 from by
          refine ⟨by norm_num, ⟨77030968351076315919620, by norm_num⟩, by norm_num, ⟨57773226263307236939715, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 115546452526614473879431 173319678789921710819147 1 from by
          refine ⟨by norm_num, ⟨57773226263307236939715, by norm_num⟩, by norm_num, ⟨86659839394960855409573, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 173319678789921710819147 259979518184882566228721 1 from by
          refine ⟨by norm_num, ⟨86659839394960855409573, by norm_num⟩, by norm_num, ⟨129989759092441283114360, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 259979518184882566228721 194984638638661924671541 2 from by
          refine ⟨by norm_num, ⟨129989759092441283114360, by norm_num⟩, by norm_num, ⟨97492319319330962335770, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 194984638638661924671541 18279809872374555437957 5 from by
          refine ⟨by norm_num, ⟨97492319319330962335770, by norm_num⟩, by norm_num, ⟨9139904936187277718978, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 18279809872374555437957 3427464351070229144617 4 from by
          refine ⟨by norm_num, ⟨9139904936187277718978, by norm_num⟩, by norm_num, ⟨1713732175535114572308, by norm_num⟩⟩)
        (Word.nil 3427464351070229144617))))))

theorem full_word_4 : Word word_4 3652455326712632180763 3427464351070229144617 := by
  unfold word_4
  have hp := shared_prefix_all 6336
  have ht := suffix_proof_4
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_4 : word_4.length = 46 := by decide
theorem word_sum_4 : word_4.sum = 73 := by decide

theorem infinite_family_4 (d : Nat) :
    ∃ z : Nat, Word word_4 (3652455326712632180763 + 2^74*d) z ∧
      z < 3652455326712632180763 + 2^74*d := by
  have h := word_uniform_descent full_word_4
    (show 3427464351070229144617 < 3652455326712632180763 by norm_num)
    (show 3^word_4.length < 2^word_4.sum by norm_num [word_4, sharedPrefix, suffix_4]) d
  simpa [word_sum_4] using h

/-- Recorded row 5, q=22720, bits=16, full length=46. -/
def suffix_5 : List Nat := [2, 1, 1, 2, 5, 5]
def word_5 : List Nat := sharedPrefix ++ suffix_5

theorem suffix_proof_5 : Word suffix_5 552444318464530074790409 6145201235361365120273 := by
  unfold suffix_5
  exact Word.cons
        (show ExactStep 552444318464530074790409 414333238848397556092807 2 from by
          refine ⟨by norm_num, ⟨276222159232265037395204, by norm_num⟩, by norm_num, ⟨207166619424198778046403, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 414333238848397556092807 621499858272596334139211 1 from by
          refine ⟨by norm_num, ⟨207166619424198778046403, by norm_num⟩, by norm_num, ⟨310749929136298167069605, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 621499858272596334139211 932249787408894501208817 1 from by
          refine ⟨by norm_num, ⟨310749929136298167069605, by norm_num⟩, by norm_num, ⟨466124893704447250604408, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 932249787408894501208817 699187340556670875906613 2 from by
          refine ⟨by norm_num, ⟨466124893704447250604408, by norm_num⟩, by norm_num, ⟨349593670278335437953306, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 699187340556670875906613 65548813177187894616245 5 from by
          refine ⟨by norm_num, ⟨349593670278335437953306, by norm_num⟩, by norm_num, ⟨32774406588593947308122, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 65548813177187894616245 6145201235361365120273 5 from by
          refine ⟨by norm_num, ⟨32774406588593947308122, by norm_num⟩, by norm_num, ⟨3072600617680682560136, by norm_num⟩⟩)
        (Word.nil 6145201235361365120273))))))

theorem full_word_5 : Word word_5 13097188292451922608155 6145201235361365120273 := by
  unfold word_5
  have hp := shared_prefix_all 22720
  have ht := suffix_proof_5
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_5 : word_5.length = 46 := by decide
theorem word_sum_5 : word_5.sum = 74 := by decide

theorem infinite_family_5 (d : Nat) :
    ∃ z : Nat, Word word_5 (13097188292451922608155 + 2^75*d) z ∧
      z < 13097188292451922608155 + 2^75*d := by
  have h := word_uniform_descent full_word_5
    (show 6145201235361365120273 < 13097188292451922608155 by norm_num)
    (show 3^word_5.length < 2^word_5.sum by norm_num [word_5, sharedPrefix, suffix_5]) d
  simpa [word_sum_5] using h

/-- Recorded row 6, q=13504, bits=16, full length=46. -/
def suffix_6 : List Nat := [2, 1, 1, 2, 6, 4]
def word_6 : List Nat := sharedPrefix ++ suffix_6

theorem suffix_proof_6 : Word suffix_6 328354228723192763130377 3652499889209099187043 := by
  unfold suffix_6
  exact Word.cons
        (show ExactStep 328354228723192763130377 246265671542394572347783 2 from by
          refine ⟨by norm_num, ⟨164177114361596381565188, by norm_num⟩, by norm_num, ⟨123132835771197286173891, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 246265671542394572347783 369398507313591858521675 1 from by
          refine ⟨by norm_num, ⟨123132835771197286173891, by norm_num⟩, by norm_num, ⟨184699253656795929260837, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 369398507313591858521675 554097760970387787782513 1 from by
          refine ⟨by norm_num, ⟨184699253656795929260837, by norm_num⟩, by norm_num, ⟨277048880485193893891256, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 554097760970387787782513 415573320727790840836885 2 from by
          refine ⟨by norm_num, ⟨277048880485193893891256, by norm_num⟩, by norm_num, ⟨207786660363895420418442, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 415573320727790840836885 19479999409115195664229 6 from by
          refine ⟨by norm_num, ⟨207786660363895420418442, by norm_num⟩, by norm_num, ⟨9739999704557597832114, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 19479999409115195664229 3652499889209099187043 4 from by
          refine ⟨by norm_num, ⟨9739999704557597832114, by norm_num⟩, by norm_num, ⟨1826249944604549593521, by norm_num⟩⟩)
        (Word.nil 3652499889209099187043))))))

theorem full_word_6 : Word word_6 7784525999223571742747 3652499889209099187043 := by
  unfold word_6
  have hp := shared_prefix_all 13504
  have ht := suffix_proof_6
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_6 : word_6.length = 46 := by decide
theorem word_sum_6 : word_6.sum = 74 := by decide

theorem infinite_family_6 (d : Nat) :
    ∃ z : Nat, Word word_6 (7784525999223571742747 + 2^75*d) z ∧
      z < 7784525999223571742747 + 2^75*d := by
  have h := word_uniform_descent full_word_6
    (show 3652499889209099187043 < 7784525999223571742747 by norm_num)
    (show 3^word_6.length < 2^word_6.sum by norm_num [word_6, sharedPrefix, suffix_6]) d
  simpa [word_sum_6] using h

/-- Recorded row 7, q=29888, bits=15, full length=46. -/
def suffix_7 : List Nat := [2, 1, 1, 2, 6, 3]
def word_7 : List Nat := sharedPrefix ++ suffix_7

theorem suffix_proof_7 : Word suffix_7 726736610485570206081545 16167937898070699470015 := by
  unfold suffix_7
  exact Word.cons
        (show ExactStep 726736610485570206081545 545052457864177654561159 2 from by
          refine ⟨by norm_num, ⟨363368305242785103040772, by norm_num⟩, by norm_num, ⟨272526228932088827280579, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 545052457864177654561159 817578686796266481841739 1 from by
          refine ⟨by norm_num, ⟨272526228932088827280579, by norm_num⟩, by norm_num, ⟨408789343398133240920869, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 817578686796266481841739 1226368030194399722762609 1 from by
          refine ⟨by norm_num, ⟨408789343398133240920869, by norm_num⟩, by norm_num, ⟨613184015097199861381304, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1226368030194399722762609 919776022645799792071957 2 from by
          refine ⟨by norm_num, ⟨613184015097199861381304, by norm_num⟩, by norm_num, ⟨459888011322899896035978, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 919776022645799792071957 43114501061521865253373 6 from by
          refine ⟨by norm_num, ⟨459888011322899896035978, by norm_num⟩, by norm_num, ⟨21557250530760932626686, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 43114501061521865253373 16167937898070699470015 3 from by
          refine ⟨by norm_num, ⟨21557250530760932626686, by norm_num⟩, by norm_num, ⟨8083968949035349735007, by norm_num⟩⟩)
        (Word.nil 16167937898070699470015))))))

theorem full_word_7 : Word word_7 17229258964962862170139 16167937898070699470015 := by
  unfold word_7
  have hp := shared_prefix_all 29888
  have ht := suffix_proof_7
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_7 : word_7.length = 46 := by decide
theorem word_sum_7 : word_7.sum = 73 := by decide

theorem infinite_family_7 (d : Nat) :
    ∃ z : Nat, Word word_7 (17229258964962862170139 + 2^74*d) z ∧
      z < 17229258964962862170139 + 2^74*d := by
  have h := word_uniform_descent full_word_7
    (show 16167937898070699470015 < 17229258964962862170139 by norm_num)
    (show 3^word_7.length < 2^word_7.sum by norm_num [word_7, sharedPrefix, suffix_7]) d
  simpa [word_sum_7] using h

#print axioms shared_prefix_base
#print axioms shared_prefix_all
#print axioms word_append
#print axioms infinite_family_0
#print axioms infinite_family_7
end CPOQWord
