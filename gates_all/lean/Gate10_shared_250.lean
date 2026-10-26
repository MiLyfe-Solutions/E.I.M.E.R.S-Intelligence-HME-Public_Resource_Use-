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
theorem shared_prefix_all (q : Nat) :
    Word sharedPrefix (118140960795 + 2^59*q)
      (4983230072969 + 2*3^40*q) := by
  have h := word_transport shared_prefix_base q
  simpa [shared_prefix_sum, shared_prefix_length] using h

/-- Certificate 0; shared prefix plus independently witnessed suffix. -/
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

/-- Certificate 1; shared prefix plus independently witnessed suffix. -/
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

/-- Certificate 2; shared prefix plus independently witnessed suffix. -/
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

/-- Certificate 3; shared prefix plus independently witnessed suffix. -/
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

/-- Certificate 4; shared prefix plus independently witnessed suffix. -/
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

/-- Certificate 5; shared prefix plus independently witnessed suffix. -/
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

/-- Certificate 6; shared prefix plus independently witnessed suffix. -/
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

/-- Certificate 7; shared prefix plus independently witnessed suffix. -/
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

/-- Certificate 8; shared prefix plus independently witnessed suffix. -/
def suffix_8 : List Nat := [2, 1, 1, 2, 7, 2]
def word_8 : List Nat := sharedPrefix ++ suffix_8
theorem suffix_proof_8 : Word suffix_8 278556431002895582761481 6197132513461635737095 := by
  unfold suffix_8
  exact Word.cons
        (show ExactStep 278556431002895582761481 208917323252171687071111 2 from by
          refine ⟨by norm_num, ⟨139278215501447791380740, by norm_num⟩, by norm_num, ⟨104458661626085843535555, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 208917323252171687071111 313375984878257530606667 1 from by
          refine ⟨by norm_num, ⟨104458661626085843535555, by norm_num⟩, by norm_num, ⟨156687992439128765303333, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 313375984878257530606667 470063977317386295910001 1 from by
          refine ⟨by norm_num, ⟨156687992439128765303333, by norm_num⟩, by norm_num, ⟨235031988658693147955000, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 470063977317386295910001 352547982988039721932501 2 from by
          refine ⟨by norm_num, ⟨235031988658693147955000, by norm_num⟩, by norm_num, ⟨176273991494019860966250, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 352547982988039721932501 8262843351282180982793 7 from by
          refine ⟨by norm_num, ⟨176273991494019860966250, by norm_num⟩, by norm_num, ⟨4131421675641090491396, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 8262843351282180982793 6197132513461635737095 2 from by
          refine ⟨by norm_num, ⟨4131421675641090491396, by norm_num⟩, by norm_num, ⟨3098566256730817868547, by norm_num⟩⟩)
        (Word.nil 6197132513461635737095))))))
theorem full_word_8 : Word word_8 6603934378506160439323 6197132513461635737095 := by
  unfold word_8
  have hp := shared_prefix_all 11456
  have ht := suffix_proof_8
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_8 : word_8.length = 46 := by decide
theorem word_sum_8 : word_8.sum = 73 := by decide
theorem infinite_family_8 (d : Nat) :
    ∃ z : Nat, Word word_8 (6603934378506160439323 + 2^74*d) z ∧
      z < 6603934378506160439323 + 2^74*d := by
  have h := word_uniform_descent full_word_8
    (show 6197132513461635737095 < 6603934378506160439323 by norm_num)
    (show 3^word_8.length < 2^word_8.sum by norm_num [word_8, sharedPrefix, suffix_8]) d
  simpa [word_sum_8] using h

/-- Certificate 9; shared prefix plus independently witnessed suffix. -/
def suffix_9 : List Nat := [2, 1, 1, 2, 7, 3]
def word_9 : List Nat := sharedPrefix ++ suffix_9
theorem suffix_proof_9 : Word suffix_9 1473703576290027911614985 16392973436209569512441 := by
  unfold suffix_9
  exact Word.cons
        (show ExactStep 1473703576290027911614985 1105277682217520933711239 2 from by
          refine ⟨by norm_num, ⟨736851788145013955807492, by norm_num⟩, by norm_num, ⟨552638841108760466855619, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1105277682217520933711239 1657916523326281400566859 1 from by
          refine ⟨by norm_num, ⟨552638841108760466855619, by norm_num⟩, by norm_num, ⟨828958261663140700283429, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1657916523326281400566859 2486874784989422100850289 1 from by
          refine ⟨by norm_num, ⟨828958261663140700283429, by norm_num⟩, by norm_num, ⟨1243437392494711050425144, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2486874784989422100850289 1865156088742066575637717 2 from by
          refine ⟨by norm_num, ⟨1243437392494711050425144, by norm_num⟩, by norm_num, ⟨932578044371033287818858, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1865156088742066575637717 43714595829892185366509 7 from by
          refine ⟨by norm_num, ⟨932578044371033287818858, by norm_num⟩, by norm_num, ⟨21857297914946092683254, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 43714595829892185366509 16392973436209569512441 3 from by
          refine ⟨by norm_num, ⟨21857297914946092683254, by norm_num⟩, by norm_num, ⟨8196486718104784756220, by norm_num⟩⟩)
        (Word.nil 16392973436209569512441))))))
theorem full_word_9 : Word word_9 34938133275724031721499 16392973436209569512441 := by
  unfold word_9
  have hp := shared_prefix_all 60608
  have ht := suffix_proof_9
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_9 : word_9.length = 46 := by decide
theorem word_sum_9 : word_9.sum = 74 := by decide
theorem infinite_family_9 (d : Nat) :
    ∃ z : Nat, Word word_9 (34938133275724031721499 + 2^75*d) z ∧
      z < 34938133275724031721499 + 2^75*d := by
  have h := word_uniform_descent full_word_9
    (show 16392973436209569512441 < 34938133275724031721499 by norm_num)
    (show 3^word_9.length < 2^word_9.sum by norm_num [word_9, sharedPrefix, suffix_9]) d
  simpa [word_sum_9] using h

/-- Certificate 10; shared prefix plus independently witnessed suffix. -/
def suffix_10 : List Nat := [2, 1, 1, 2, 8]
def word_10 : List Nat := sharedPrefix ++ suffix_10
theorem suffix_proof_10 : Word suffix_10 178960835562301222023689 2654265322365673642075 := by
  unfold suffix_10
  exact Word.cons
        (show ExactStep 178960835562301222023689 134220626671725916517767 2 from by
          refine ⟨by norm_num, ⟨89480417781150611011844, by norm_num⟩, by norm_num, ⟨67110313335862958258883, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 134220626671725916517767 201330940007588874776651 1 from by
          refine ⟨by norm_num, ⟨67110313335862958258883, by norm_num⟩, by norm_num, ⟨100665470003794437388325, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 201330940007588874776651 301996410011383312164977 1 from by
          refine ⟨by norm_num, ⟨100665470003794437388325, by norm_num⟩, by norm_num, ⟨150998205005691656082488, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 301996410011383312164977 226497307508537484123733 2 from by
          refine ⟨by norm_num, ⟨150998205005691656082488, by norm_num⟩, by norm_num, ⟨113248653754268742061866, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 226497307508537484123733 2654265322365673642075 8 from by
          refine ⟨by norm_num, ⟨113248653754268742061866, by norm_num⟩, by norm_num, ⟨1327132661182836821037, by norm_num⟩⟩)
        (Word.nil 2654265322365673642075)))))
theorem full_word_10 : Word word_10 4242751137071337832475 2654265322365673642075 := by
  unfold word_10
  have hp := shared_prefix_all 7360
  have ht := suffix_proof_10
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_10 : word_10.length = 45 := by decide
theorem word_sum_10 : word_10.sum = 72 := by decide
theorem infinite_family_10 (d : Nat) :
    ∃ z : Nat, Word word_10 (4242751137071337832475 + 2^73*d) z ∧
      z < 4242751137071337832475 + 2^73*d := by
  have h := word_uniform_descent full_word_10
    (show 2654265322365673642075 < 4242751137071337832475 by norm_num)
    (show 3^word_10.length < 2^word_10.sum by norm_num [word_10, sharedPrefix, suffix_10]) d
  simpa [word_sum_10] using h

/-- Certificate 11; shared prefix plus independently witnessed suffix. -/
def suffix_11 : List Nat := [2, 1, 1, 2, 9]
def word_11 : List Nat := sharedPrefix ++ suffix_11
theorem suffix_proof_11 : Word suffix_11 378152026443489943499273 2804289014458253670359 := by
  unfold suffix_11
  exact Word.cons
        (show ExactStep 378152026443489943499273 283614019832617457624455 2 from by
          refine ⟨by norm_num, ⟨189076013221744971749636, by norm_num⟩, by norm_num, ⟨141807009916308728812227, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 283614019832617457624455 425421029748926186436683 1 from by
          refine ⟨by norm_num, ⟨141807009916308728812227, by norm_num⟩, by norm_num, ⟨212710514874463093218341, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 425421029748926186436683 638131544623389279655025 1 from by
          refine ⟨by norm_num, ⟨212710514874463093218341, by norm_num⟩, by norm_num, ⟨319065772311694639827512, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 638131544623389279655025 478598658467541959741269 2 from by
          refine ⟨by norm_num, ⟨319065772311694639827512, by norm_num⟩, by norm_num, ⟨239299329233770979870634, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 478598658467541959741269 2804289014458253670359 9 from by
          refine ⟨by norm_num, ⟨239299329233770979870634, by norm_num⟩, by norm_num, ⟨1402144507229126835179, by norm_num⟩⟩)
        (Word.nil 2804289014458253670359)))))
theorem full_word_11 : Word word_11 8965117619940983046171 2804289014458253670359 := by
  unfold word_11
  have hp := shared_prefix_all 15552
  have ht := suffix_proof_11
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_11 : word_11.length = 45 := by decide
theorem word_sum_11 : word_11.sum = 73 := by decide
theorem infinite_family_11 (d : Nat) :
    ∃ z : Nat, Word word_11 (8965117619940983046171 + 2^74*d) z ∧
      z < 8965117619940983046171 + 2^74*d := by
  have h := word_uniform_descent full_word_11
    (show 2804289014458253670359 < 8965117619940983046171 by norm_num)
    (show 3^word_11.length < 2^word_11.sum by norm_num [word_11, sharedPrefix, suffix_11]) d
  simpa [word_sum_11] using h

/-- Certificate 12; shared prefix plus independently witnessed suffix. -/
def suffix_12 : List Nat := [2, 1, 1, 2, 10]
def word_12 : List Nat := sharedPrefix ++ suffix_12
theorem suffix_proof_12 : Word suffix_12 776534408205867386450441 2879300860504543684501 := by
  unfold suffix_12
  exact Word.cons
        (show ExactStep 776534408205867386450441 582400806154400539837831 2 from by
          refine ⟨by norm_num, ⟨388267204102933693225220, by norm_num⟩, by norm_num, ⟨291200403077200269918915, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 582400806154400539837831 873601209231600809756747 1 from by
          refine ⟨by norm_num, ⟨291200403077200269918915, by norm_num⟩, by norm_num, ⟨436800604615800404878373, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 873601209231600809756747 1310401813847401214635121 1 from by
          refine ⟨by norm_num, ⟨436800604615800404878373, by norm_num⟩, by norm_num, ⟨655200906923700607317560, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1310401813847401214635121 982801360385550910976341 2 from by
          refine ⟨by norm_num, ⟨655200906923700607317560, by norm_num⟩, by norm_num, ⟨491400680192775455488170, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 982801360385550910976341 2879300860504543684501 10 from by
          refine ⟨by norm_num, ⟨491400680192775455488170, by norm_num⟩, by norm_num, ⟨1439650430252271842250, by norm_num⟩⟩)
        (Word.nil 2879300860504543684501)))))
theorem full_word_12 : Word word_12 18409850585680273473563 2879300860504543684501 := by
  unfold word_12
  have hp := shared_prefix_all 31936
  have ht := suffix_proof_12
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_12 : word_12.length = 45 := by decide
theorem word_sum_12 : word_12.sum = 74 := by decide
theorem infinite_family_12 (d : Nat) :
    ∃ z : Nat, Word word_12 (18409850585680273473563 + 2^75*d) z ∧
      z < 18409850585680273473563 + 2^75*d := by
  have h := word_uniform_descent full_word_12
    (show 2879300860504543684501 < 18409850585680273473563 by norm_num)
    (show 3^word_12.length < 2^word_12.sum by norm_num [word_12, sharedPrefix, suffix_12]) d
  simpa [word_sum_12] using h

/-- Certificate 13; shared prefix plus independently witnessed suffix. -/
def suffix_13 : List Nat := [2, 1, 1, 2, 4, 5]
def word_13 : List Nat := sharedPrefix ++ suffix_13
theorem suffix_proof_13 : Word suffix_13 266106981572821287669257 5920165697222495077847 := by
  unfold suffix_13
  exact Word.cons
        (show ExactStep 266106981572821287669257 199580236179615965751943 2 from by
          refine ⟨by norm_num, ⟨133053490786410643834628, by norm_num⟩, by norm_num, ⟨99790118089807982875971, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 199580236179615965751943 299370354269423948627915 1 from by
          refine ⟨by norm_num, ⟨99790118089807982875971, by norm_num⟩, by norm_num, ⟨149685177134711974313957, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 299370354269423948627915 449055531404135922941873 1 from by
          refine ⟨by norm_num, ⟨149685177134711974313957, by norm_num⟩, by norm_num, ⟨224527765702067961470936, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 449055531404135922941873 336791648553101942206405 2 from by
          refine ⟨by norm_num, ⟨224527765702067961470936, by norm_num⟩, by norm_num, ⟨168395824276550971103202, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 336791648553101942206405 63148434103706614163701 4 from by
          refine ⟨by norm_num, ⟨168395824276550971103202, by norm_num⟩, by norm_num, ⟨31574217051853307081850, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 63148434103706614163701 5920165697222495077847 5 from by
          refine ⟨by norm_num, ⟨31574217051853307081850, by norm_num⟩, by norm_num, ⟨2960082848611247538923, by norm_num⟩⟩)
        (Word.nil 5920165697222495077847))))))
theorem full_word_13 : Word word_13 6308786473326807613467 5920165697222495077847 := by
  unfold word_13
  have hp := shared_prefix_all 10944
  have ht := suffix_proof_13
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_13 : word_13.length = 46 := by decide
theorem word_sum_13 : word_13.sum = 73 := by decide
theorem infinite_family_13 (d : Nat) :
    ∃ z : Nat, Word word_13 (6308786473326807613467 + 2^74*d) z ∧
      z < 6308786473326807613467 + 2^74*d := by
  have h := word_uniform_descent full_word_13
    (show 5920165697222495077847 < 6308786473326807613467 by norm_num)
    (show 3^word_13.length < 2^word_13.sum by norm_num [word_13, sharedPrefix, suffix_13]) d
  simpa [word_sum_13] using h

/-- Certificate 14; shared prefix plus independently witnessed suffix. -/
def suffix_14 : List Nat := [2, 1, 1, 2, 4, 6]
def word_14 : List Nat := sharedPrefix ++ suffix_14
theorem suffix_proof_14 : Word suffix_14 1461254126859953616522761 16254490028089999182817 := by
  unfold suffix_14
  exact Word.cons
        (show ExactStep 1461254126859953616522761 1095940595144965212392071 2 from by
          refine ⟨by norm_num, ⟨730627063429976808261380, by norm_num⟩, by norm_num, ⟨547970297572482606196035, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1095940595144965212392071 1643910892717447818588107 1 from by
          refine ⟨by norm_num, ⟨547970297572482606196035, by norm_num⟩, by norm_num, ⟨821955446358723909294053, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1643910892717447818588107 2465866339076171727882161 1 from by
          refine ⟨by norm_num, ⟨821955446358723909294053, by norm_num⟩, by norm_num, ⟨1232933169538085863941080, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2465866339076171727882161 1849399754307128795911621 2 from by
          refine ⟨by norm_num, ⟨1232933169538085863941080, by norm_num⟩, by norm_num, ⟨924699877153564397955810, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1849399754307128795911621 346762453932586649233429 4 from by
          refine ⟨by norm_num, ⟨924699877153564397955810, by norm_num⟩, by norm_num, ⟨173381226966293324616714, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 346762453932586649233429 16254490028089999182817 6 from by
          refine ⟨by norm_num, ⟨173381226966293324616714, by norm_num⟩, by norm_num, ⟨8127245014044999591408, by norm_num⟩⟩)
        (Word.nil 16254490028089999182817))))))
theorem full_word_14 : Word word_14 34642985370544678895643 16254490028089999182817 := by
  unfold word_14
  have hp := shared_prefix_all 60096
  have ht := suffix_proof_14
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_14 : word_14.length = 46 := by decide
theorem word_sum_14 : word_14.sum = 74 := by decide
theorem infinite_family_14 (d : Nat) :
    ∃ z : Nat, Word word_14 (34642985370544678895643 + 2^75*d) z ∧
      z < 34642985370544678895643 + 2^75*d := by
  have h := word_uniform_descent full_word_14
    (show 16254490028089999182817 < 34642985370544678895643 by norm_num)
    (show 3^word_14.length < 2^word_14.sum by norm_num [word_14, sharedPrefix, suffix_14]) d
  simpa [word_sum_14] using h

/-- Certificate 15; shared prefix plus independently witnessed suffix. -/
def suffix_15 : List Nat := [2, 1, 1, 2, 3, 7]
def word_15 : List Nat := sharedPrefix ++ suffix_15
theorem suffix_proof_15 : Word suffix_15 322129504008155615584265 3583258185149314022231 := by
  unfold suffix_15
  exact Word.cons
        (show ExactStep 322129504008155615584265 241597128006116711688199 2 from by
          refine ⟨by norm_num, ⟨161064752004077807792132, by norm_num⟩, by norm_num, ⟨120798564003058355844099, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 241597128006116711688199 362395692009175067532299 1 from by
          refine ⟨by norm_num, ⟨120798564003058355844099, by norm_num⟩, by norm_num, ⟨181197846004587533766149, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 362395692009175067532299 543593538013762601298449 1 from by
          refine ⟨by norm_num, ⟨181197846004587533766149, by norm_num⟩, by norm_num, ⟨271796769006881300649224, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 543593538013762601298449 407695153510321950973837 2 from by
          refine ⟨by norm_num, ⟨271796769006881300649224, by norm_num⟩, by norm_num, ⟨203847576755160975486918, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 407695153510321950973837 152885682566370731615189 3 from by
          refine ⟨by norm_num, ⟨203847576755160975486918, by norm_num⟩, by norm_num, ⟨76442841283185365807594, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 152885682566370731615189 3583258185149314022231 7 from by
          refine ⟨by norm_num, ⟨76442841283185365807594, by norm_num⟩, by norm_num, ⟨1791629092574657011115, by norm_num⟩⟩)
        (Word.nil 3583258185149314022231))))))
theorem full_word_15 : Word word_15 7636952046633895329819 3583258185149314022231 := by
  unfold word_15
  have hp := shared_prefix_all 13248
  have ht := suffix_proof_15
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_15 : word_15.length = 46 := by decide
theorem word_sum_15 : word_15.sum = 74 := by decide
theorem infinite_family_15 (d : Nat) :
    ∃ z : Nat, Word word_15 (7636952046633895329819 + 2^75*d) z ∧
      z < 7636952046633895329819 + 2^75*d := by
  have h := word_uniform_descent full_word_15
    (show 3583258185149314022231 < 7636952046633895329819 by norm_num)
    (show 3^word_15.length < 2^word_15.sum by norm_num [word_15, sharedPrefix, suffix_15]) d
  simpa [word_sum_15] using h

/-- Certificate 16; shared prefix plus independently witnessed suffix. -/
def suffix_16 : List Nat := [2, 1, 1, 2, 3, 6]
def word_16 : List Nat := sharedPrefix ++ suffix_16
theorem suffix_proof_16 : Word suffix_16 720511885770533058535433 16029454489951129140391 := by
  unfold suffix_16
  exact Word.cons
        (show ExactStep 720511885770533058535433 540383914327899793901575 2 from by
          refine ⟨by norm_num, ⟨360255942885266529267716, by norm_num⟩, by norm_num, ⟨270191957163949896950787, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 540383914327899793901575 810575871491849690852363 1 from by
          refine ⟨by norm_num, ⟨270191957163949896950787, by norm_num⟩, by norm_num, ⟨405287935745924845426181, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 810575871491849690852363 1215863807237774536278545 1 from by
          refine ⟨by norm_num, ⟨405287935745924845426181, by norm_num⟩, by norm_num, ⟨607931903618887268139272, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1215863807237774536278545 911897855428330902208909 2 from by
          refine ⟨by norm_num, ⟨607931903618887268139272, by norm_num⟩, by norm_num, ⟨455948927714165451104454, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 911897855428330902208909 341961695785624088328341 3 from by
          refine ⟨by norm_num, ⟨455948927714165451104454, by norm_num⟩, by norm_num, ⟨170980847892812044164170, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 341961695785624088328341 16029454489951129140391 6 from by
          refine ⟨by norm_num, ⟨170980847892812044164170, by norm_num⟩, by norm_num, ⟨8014727244975564570195, by norm_num⟩⟩)
        (Word.nil 16029454489951129140391))))))
theorem full_word_16 : Word word_16 17081685012373185757211 16029454489951129140391 := by
  unfold word_16
  have hp := shared_prefix_all 29632
  have ht := suffix_proof_16
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_16 : word_16.length = 46 := by decide
theorem word_sum_16 : word_16.sum = 73 := by decide
theorem infinite_family_16 (d : Nat) :
    ∃ z : Nat, Word word_16 (17081685012373185757211 + 2^74*d) z ∧
      z < 17081685012373185757211 + 2^74*d := by
  have h := word_uniform_descent full_word_16
    (show 16029454489951129140391 < 17081685012373185757211 by norm_num)
    (show 3^word_16.length < 2^word_16.sum by norm_num [word_16, sharedPrefix, suffix_16]) d
  simpa [word_sum_16] using h

/-- Certificate 17; shared prefix plus independently witnessed suffix. -/
def suffix_17 : List Nat := [2, 1, 1, 8]
def word_17 : List Nat := sharedPrefix ++ suffix_17
theorem suffix_proof_17 : Word suffix_17 778090594362873516233 15387045445164246781 := by
  unfold suffix_17
  exact Word.cons
        (show ExactStep 778090594362873516233 583567945772155137175 2 from by
          refine ⟨by norm_num, ⟨389045297181436758116, by norm_num⟩, by norm_num, ⟨291783972886077568587, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 583567945772155137175 875351918658232705763 1 from by
          refine ⟨by norm_num, ⟨291783972886077568587, by norm_num⟩, by norm_num, ⟨437675959329116352881, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 875351918658232705763 1313027877987349058645 1 from by
          refine ⟨by norm_num, ⟨437675959329116352881, by norm_num⟩, by norm_num, ⟨656513938993674529322, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1313027877987349058645 15387045445164246781 8 from by
          refine ⟨by norm_num, ⟨656513938993674529322, by norm_num⟩, by norm_num, ⟨7693522722582123390, by norm_num⟩⟩)
        (Word.nil 15387045445164246781))))
theorem full_word_17 : Word word_17 18446744191850512411 15387045445164246781 := by
  unfold word_17
  have hp := shared_prefix_all 32
  have ht := suffix_proof_17
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_17 : word_17.length = 44 := by decide
theorem word_sum_17 : word_17.sum = 70 := by decide
theorem infinite_family_17 (d : Nat) :
    ∃ z : Nat, Word word_17 (18446744191850512411 + 2^71*d) z ∧
      z < 18446744191850512411 + 2^71*d := by
  have h := word_uniform_descent full_word_17
    (show 15387045445164246781 < 18446744191850512411 by norm_num)
    (show 3^word_17.length < 2^word_17.sum by norm_num [word_17, sharedPrefix, suffix_17]) d
  simpa [word_sum_17] using h

/-- Certificate 18; shared prefix plus independently witnessed suffix. -/
def suffix_18 : List Nat := [2, 1, 1, 9]
def word_18 : List Nat := sharedPrefix ++ suffix_18
theorem suffix_proof_18 : Word suffix_18 50575888314660053885129 500078973814387739831 := by
  unfold suffix_18
  exact Word.cons
        (show ExactStep 50575888314660053885129 37931916235995040413847 2 from by
          refine ⟨by norm_num, ⟨25287944157330026942564, by norm_num⟩, by norm_num, ⟨18965958117997520206923, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 37931916235995040413847 56897874353992560620771 1 from by
          refine ⟨by norm_num, ⟨18965958117997520206923, by norm_num⟩, by norm_num, ⟨28448937176996280310385, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 56897874353992560620771 85346811530988840931157 1 from by
          refine ⟨by norm_num, ⟨28448937176996280310385, by norm_num⟩, by norm_num, ⟨42673405765494420465578, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 85346811530988840931157 500078973814387739831 9 from by
          refine ⟨by norm_num, ⟨42673405765494420465578, by norm_num⟩, by norm_num, ⟨250039486907193869915, by norm_num⟩⟩)
        (Word.nil 500078973814387739831))))
theorem full_word_18 : Word word_18 1199038364909261815835 500078973814387739831 := by
  unfold word_18
  have hp := shared_prefix_all 2080
  have ht := suffix_proof_18
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_18 : word_18.length = 44 := by decide
theorem word_sum_18 : word_18.sum = 71 := by decide
theorem infinite_family_18 (d : Nat) :
    ∃ z : Nat, Word word_18 (1199038364909261815835 + 2^72*d) z ∧
      z < 1199038364909261815835 + 2^72*d := by
  have h := word_uniform_descent full_word_18
    (show 500078973814387739831 < 1199038364909261815835 by norm_num)
    (show 3^word_18.length < 2^word_18.sum by norm_num [word_18, sharedPrefix, suffix_18]) d
  simpa [word_sum_18] using h

/-- Certificate 19; shared prefix plus independently witnessed suffix. -/
def suffix_19 : List Nat := [2, 1, 1, 12]
def word_19 : List Nat := sharedPrefix ++ suffix_19
theorem suffix_proof_19 : Word suffix_19 150171483755254414622921 185606234499749871589 := by
  unfold suffix_19
  exact Word.cons
        (show ExactStep 150171483755254414622921 112628612816440810967191 2 from by
          refine ⟨by norm_num, ⟨75085741877627207311460, by norm_num⟩, by norm_num, ⟨56314306408220405483595, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 112628612816440810967191 168942919224661216450787 1 from by
          refine ⟨by norm_num, ⟨56314306408220405483595, by norm_num⟩, by norm_num, ⟨84471459612330608225393, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 168942919224661216450787 253414378836991824676181 1 from by
          refine ⟨by norm_num, ⟨84471459612330608225393, by norm_num⟩, by norm_num, ⟨126707189418495912338090, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 253414378836991824676181 185606234499749871589 12 from by
          refine ⟨by norm_num, ⟨126707189418495912338090, by norm_num⟩, by norm_num, ⟨92803117249874935794, by norm_num⟩⟩)
        (Word.nil 185606234499749871589))))
theorem full_word_19 : Word word_19 3560221606344084422683 185606234499749871589 := by
  unfold word_19
  have hp := shared_prefix_all 6176
  have ht := suffix_proof_19
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_19 : word_19.length = 44 := by decide
theorem word_sum_19 : word_19.sum = 74 := by decide
theorem infinite_family_19 (d : Nat) :
    ∃ z : Nat, Word word_19 (3560221606344084422683 + 2^75*d) z ∧
      z < 3560221606344084422683 + 2^75*d := by
  have h := word_uniform_descent full_word_19
    (show 185606234499749871589 < 3560221606344084422683 by norm_num)
    (show 3^word_19.length < 2^word_19.sum by norm_num [word_19, sharedPrefix, suffix_19]) d
  simpa [word_sum_19] using h

/-- Certificate 20; shared prefix plus independently witnessed suffix. -/
def suffix_20 : List Nat := [2, 1, 1, 11]
def word_20 : List Nat := sharedPrefix ++ suffix_20
theorem suffix_proof_20 : Word suffix_20 548553865517631857574089 1355983371183110976059 := by
  unfold suffix_20
  exact Word.cons
        (show ExactStep 548553865517631857574089 411415399138223893180567 2 from by
          refine ⟨by norm_num, ⟨274276932758815928787044, by norm_num⟩, by norm_num, ⟨205707699569111946590283, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 411415399138223893180567 617123098707335839770851 1 from by
          refine ⟨by norm_num, ⟨205707699569111946590283, by norm_num⟩, by norm_num, ⟨308561549353667919885425, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 617123098707335839770851 925684648061003759656277 1 from by
          refine ⟨by norm_num, ⟨308561549353667919885425, by norm_num⟩, by norm_num, ⟨462842324030501879828138, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 925684648061003759656277 1355983371183110976059 11 from by
          refine ⟨by norm_num, ⟨462842324030501879828138, by norm_num⟩, by norm_num, ⟨677991685591555488029, by norm_num⟩⟩)
        (Word.nil 1355983371183110976059))))
theorem full_word_20 : Word word_20 13004954572083374850075 1355983371183110976059 := by
  unfold word_20
  have hp := shared_prefix_all 22560
  have ht := suffix_proof_20
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_20 : word_20.length = 44 := by decide
theorem word_sum_20 : word_20.sum = 73 := by decide
theorem infinite_family_20 (d : Nat) :
    ∃ z : Nat, Word word_20 (13004954572083374850075 + 2^74*d) z ∧
      z < 13004954572083374850075 + 2^74*d := by
  have h := word_uniform_descent full_word_20
    (show 1355983371183110976059 < 13004954572083374850075 by norm_num)
    (show 3^word_20.length < 2^word_20.sum by norm_num [word_20, sharedPrefix, suffix_20]) d
  simpa [word_sum_20] using h

/-- Certificate 21; shared prefix plus independently witnessed suffix. -/
def suffix_21 : List Nat := [2, 1, 1, 10]
def word_21 : List Nat := sharedPrefix ++ suffix_21
theorem suffix_proof_21 : Word suffix_21 349362674636443136098505 1727195840182610719237 := by
  unfold suffix_21
  exact Word.cons
        (show ExactStep 349362674636443136098505 262022005977332352073879 2 from by
          refine ⟨by norm_num, ⟨174681337318221568049252, by norm_num⟩, by norm_num, ⟨131011002988666176036939, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 262022005977332352073879 393033008965998528110819 1 from by
          refine ⟨by norm_num, ⟨131011002988666176036939, by norm_num⟩, by norm_num, ⟨196516504482999264055409, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 393033008965998528110819 589549513448997792166229 1 from by
          refine ⟨by norm_num, ⟨196516504482999264055409, by norm_num⟩, by norm_num, ⟨294774756724498896083114, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 589549513448997792166229 1727195840182610719237 10 from by
          refine ⟨by norm_num, ⟨294774756724498896083114, by norm_num⟩, by norm_num, ⟨863597920091305359618, by norm_num⟩⟩)
        (Word.nil 1727195840182610719237))))
theorem full_word_21 : Word word_21 8282588089213729636379 1727195840182610719237 := by
  unfold word_21
  have hp := shared_prefix_all 14368
  have ht := suffix_proof_21
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_21 : word_21.length = 44 := by decide
theorem word_sum_21 : word_21.sum = 72 := by decide
theorem infinite_family_21 (d : Nat) :
    ∃ z : Nat, Word word_21 (8282588089213729636379 + 2^73*d) z ∧
      z < 8282588089213729636379 + 2^73*d := by
  have h := word_uniform_descent full_word_21
    (show 1727195840182610719237 < 8282588089213729636379 by norm_num)
    (show 3^word_21.length < 2^word_21.sum by norm_num [word_21, sharedPrefix, suffix_21]) d
  simpa [word_sum_21] using h

/-- Certificate 22; shared prefix plus independently witnessed suffix. -/
def suffix_22 : List Nat := [2, 1, 1, 7, 1, 3]
def word_22 : List Nat := sharedPrefix ++ suffix_22
theorem suffix_proof_22 : Word suffix_22 224868180335700185176265 5002713118430341644089 := by
  unfold suffix_22
  exact Word.cons
        (show ExactStep 224868180335700185176265 168651135251775138882199 2 from by
          refine ⟨by norm_num, ⟨112434090167850092588132, by norm_num⟩, by norm_num, ⟨84325567625887569441099, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 168651135251775138882199 252976702877662708323299 1 from by
          refine ⟨by norm_num, ⟨84325567625887569441099, by norm_num⟩, by norm_num, ⟨126488351438831354161649, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 252976702877662708323299 379465054316494062484949 1 from by
          refine ⟨by norm_num, ⟨126488351438831354161649, by norm_num⟩, by norm_num, ⟨189732527158247031242474, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 379465054316494062484949 8893712210542829589491 7 from by
          refine ⟨by norm_num, ⟨189732527158247031242474, by norm_num⟩, by norm_num, ⟨4446856105271414794745, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 8893712210542829589491 13340568315814244384237 1 from by
          refine ⟨by norm_num, ⟨4446856105271414794745, by norm_num⟩, by norm_num, ⟨6670284157907122192118, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 13340568315814244384237 5002713118430341644089 3 from by
          refine ⟨by norm_num, ⟨6670284157907122192118, by norm_num⟩, by norm_num, ⟨2501356559215170822044, by norm_num⟩⟩)
        (Word.nil 5002713118430341644089))))))
theorem full_word_22 : Word word_22 5331109037420201377819 5002713118430341644089 := by
  unfold word_22
  have hp := shared_prefix_all 9248
  have ht := suffix_proof_22
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_22 : word_22.length = 46 := by decide
theorem word_sum_22 : word_22.sum = 73 := by decide
theorem infinite_family_22 (d : Nat) :
    ∃ z : Nat, Word word_22 (5331109037420201377819 + 2^74*d) z ∧
      z < 5331109037420201377819 + 2^74*d := by
  have h := word_uniform_descent full_word_22
    (show 5002713118430341644089 < 5331109037420201377819 by norm_num)
    (show 3^word_22.length < 2^word_22.sum by norm_num [word_22, sharedPrefix, suffix_22]) d
  simpa [word_sum_22] using h

/-- Certificate 23; shared prefix plus independently witnessed suffix. -/
def suffix_23 : List Nat := [2, 1, 1, 7, 1, 4]
def word_23 : List Nat := sharedPrefix ++ suffix_23
theorem suffix_proof_23 : Word suffix_23 623250562098077628127433 6932825619041421370009 := by
  unfold suffix_23
  exact Word.cons
        (show ExactStep 623250562098077628127433 467437921573558221095575 2 from by
          refine ⟨by norm_num, ⟨311625281049038814063716, by norm_num⟩, by norm_num, ⟨233718960786779110547787, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 467437921573558221095575 701156882360337331643363 1 from by
          refine ⟨by norm_num, ⟨233718960786779110547787, by norm_num⟩, by norm_num, ⟨350578441180168665821681, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 701156882360337331643363 1051735323540505997465045 1 from by
          refine ⟨by norm_num, ⟨350578441180168665821681, by norm_num⟩, by norm_num, ⟨525867661770252998732522, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1051735323540505997465045 24650046645480609315587 7 from by
          refine ⟨by norm_num, ⟨525867661770252998732522, by norm_num⟩, by norm_num, ⟨12325023322740304657793, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 24650046645480609315587 36975069968220913973381 1 from by
          refine ⟨by norm_num, ⟨12325023322740304657793, by norm_num⟩, by norm_num, ⟨18487534984110456986690, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 36975069968220913973381 6932825619041421370009 4 from by
          refine ⟨by norm_num, ⟨18487534984110456986690, by norm_num⟩, by norm_num, ⟨3466412809520710685004, by norm_num⟩⟩)
        (Word.nil 6932825619041421370009))))))
theorem full_word_23 : Word word_23 14775842003159491805211 6932825619041421370009 := by
  unfold word_23
  have hp := shared_prefix_all 25632
  have ht := suffix_proof_23
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_23 : word_23.length = 46 := by decide
theorem word_sum_23 : word_23.sum = 74 := by decide
theorem infinite_family_23 (d : Nat) :
    ∃ z : Nat, Word word_23 (14775842003159491805211 + 2^75*d) z ∧
      z < 14775842003159491805211 + 2^75*d := by
  have h := word_uniform_descent full_word_23
    (show 6932825619041421370009 < 14775842003159491805211 by norm_num)
    (show 3^word_23.length < 2^word_23.sum by norm_num [word_23, sharedPrefix, suffix_23]) d
  simpa [word_sum_23] using h

/-- Certificate 24; shared prefix plus independently witnessed suffix. -/
def suffix_24 : List Nat := [2, 1, 1, 7, 3]
def word_24 : List Nat := sharedPrefix ++ suffix_24
theorem suffix_proof_24 : Word suffix_24 75474787174808644069577 1119407549040435822077 := by
  unfold suffix_24
  exact Word.cons
        (show ExactStep 75474787174808644069577 56606090381106483052183 2 from by
          refine ⟨by norm_num, ⟨37737393587404322034788, by norm_num⟩, by norm_num, ⟨28303045190553241526091, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 56606090381106483052183 84909135571659724578275 1 from by
          refine ⟨by norm_num, ⟨28303045190553241526091, by norm_num⟩, by norm_num, ⟨42454567785829862289137, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 84909135571659724578275 127363703357489586867413 1 from by
          refine ⟨by norm_num, ⟨42454567785829862289137, by norm_num⟩, by norm_num, ⟨63681851678744793433706, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 127363703357489586867413 2985086797441162192205 7 from by
          refine ⟨by norm_num, ⟨63681851678744793433706, by norm_num⟩, by norm_num, ⟨1492543398720581096102, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2985086797441162192205 1119407549040435822077 3 from by
          refine ⟨by norm_num, ⟨1492543398720581096102, by norm_num⟩, by norm_num, ⟨559703774520217911038, by norm_num⟩⟩)
        (Word.nil 1119407549040435822077)))))
theorem full_word_24 : Word word_24 1789334175267967467547 1119407549040435822077 := by
  unfold word_24
  have hp := shared_prefix_all 3104
  have ht := suffix_proof_24
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_24 : word_24.length = 45 := by decide
theorem word_sum_24 : word_24.sum = 72 := by decide
theorem infinite_family_24 (d : Nat) :
    ∃ z : Nat, Word word_24 (1789334175267967467547 + 2^73*d) z ∧
      z < 1789334175267967467547 + 2^73*d := by
  have h := word_uniform_descent full_word_24
    (show 1119407549040435822077 < 1789334175267967467547 by norm_num)
    (show 3^word_24.length < 2^word_24.sum by norm_num [word_24, sharedPrefix, suffix_24]) d
  simpa [word_sum_24] using h

/-- Certificate 25; shared prefix plus independently witnessed suffix. -/
def suffix_25 : List Nat := [2, 1, 1, 7, 5]
def word_25 : List Nat := sharedPrefix ++ suffix_25
theorem suffix_proof_25 : Word suffix_25 1071430741580752251447497 3972742770448651078823 := by
  unfold suffix_25
  exact Word.cons
        (show ExactStep 1071430741580752251447497 803573056185564188585623 2 from by
          refine ⟨by norm_num, ⟨535715370790376125723748, by norm_num⟩, by norm_num, ⟨401786528092782094292811, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 803573056185564188585623 1205359584278346282878435 1 from by
          refine ⟨by norm_num, ⟨401786528092782094292811, by norm_num⟩, by norm_num, ⟨602679792139173141439217, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1205359584278346282878435 1808039376417519424317653 1 from by
          refine ⟨by norm_num, ⟨602679792139173141439217, by norm_num⟩, by norm_num, ⟨904019688208759712158826, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1808039376417519424317653 42375922884785611507445 7 from by
          refine ⟨by norm_num, ⟨904019688208759712158826, by norm_num⟩, by norm_num, ⟨21187961442392805753722, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 42375922884785611507445 3972742770448651078823 5 from by
          refine ⟨by norm_num, ⟨21187961442392805753722, by norm_num⟩, by norm_num, ⟨1986371385224325539411, by norm_num⟩⟩)
        (Word.nil 3972742770448651078823)))))
theorem full_word_25 : Word word_25 25401166589616193536027 3972742770448651078823 := by
  unfold word_25
  have hp := shared_prefix_all 44064
  have ht := suffix_proof_25
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_25 : word_25.length = 45 := by decide
theorem word_sum_25 : word_25.sum = 74 := by decide
theorem infinite_family_25 (d : Nat) :
    ∃ z : Nat, Word word_25 (25401166589616193536027 + 2^75*d) z ∧
      z < 25401166589616193536027 + 2^75*d := by
  have h := word_uniform_descent full_word_25
    (show 3972742770448651078823 < 25401166589616193536027 by norm_num)
    (show 3^word_25.length < 2^word_25.sum by norm_num [word_25, sharedPrefix, suffix_25]) d
  simpa [word_sum_25] using h

/-- Certificate 26; shared prefix plus independently witnessed suffix. -/
def suffix_26 : List Nat := [2, 1, 1, 7, 4]
def word_26 : List Nat := sharedPrefix ++ suffix_26
theorem suffix_proof_26 : Word suffix_26 673048359818374808496329 4991172834346468459003 := by
  unfold suffix_26
  exact Word.cons
        (show ExactStep 673048359818374808496329 504786269863781106372247 2 from by
          refine ⟨by norm_num, ⟨336524179909187404248164, by norm_num⟩, by norm_num, ⟨252393134931890553186123, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 504786269863781106372247 757179404795671659558371 1 from by
          refine ⟨by norm_num, ⟨252393134931890553186123, by norm_num⟩, by norm_num, ⟨378589702397835829779185, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 757179404795671659558371 1135769107193507489337557 1 from by
          refine ⟨by norm_num, ⟨378589702397835829779185, by norm_num⟩, by norm_num, ⟨567884553596753744668778, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1135769107193507489337557 26619588449847831781349 7 from by
          refine ⟨by norm_num, ⟨567884553596753744668778, by norm_num⟩, by norm_num, ⟨13309794224923915890674, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 26619588449847831781349 4991172834346468459003 4 from by
          refine ⟨by norm_num, ⟨13309794224923915890674, by norm_num⟩, by norm_num, ⟨2495586417173234229501, by norm_num⟩⟩)
        (Word.nil 4991172834346468459003)))))
theorem full_word_26 : Word word_26 15956433623876903108635 4991172834346468459003 := by
  unfold word_26
  have hp := shared_prefix_all 27680
  have ht := suffix_proof_26
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_26 : word_26.length = 45 := by decide
theorem word_sum_26 : word_26.sum = 73 := by decide
theorem infinite_family_26 (d : Nat) :
    ∃ z : Nat, Word word_26 (15956433623876903108635 + 2^74*d) z ∧
      z < 15956433623876903108635 + 2^74*d := by
  have h := word_uniform_descent full_word_26
    (show 4991172834346468459003 < 15956433623876903108635 by norm_num)
    (show 3^word_26.length < 2^word_26.sum by norm_num [word_26, sharedPrefix, suffix_26]) d
  simpa [word_sum_26] using h

/-- Certificate 27; shared prefix plus independently witnessed suffix. -/
def suffix_27 : List Nat := [2, 1, 1, 7, 2, 3]
def word_27 : List Nat := sharedPrefix ++ suffix_27
theorem suffix_proof_27 : Word suffix_27 175070382615403004807369 1947422926736889503549 := by
  unfold suffix_27
  exact Word.cons
        (show ExactStep 175070382615403004807369 131302786961552253605527 2 from by
          refine ⟨by norm_num, ⟨87535191307701502403684, by norm_num⟩, by norm_num, ⟨65651393480776126802763, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 131302786961552253605527 196954180442328380408291 1 from by
          refine ⟨by norm_num, ⟨65651393480776126802763, by norm_num⟩, by norm_num, ⟨98477090221164190204145, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 196954180442328380408291 295431270663492570612437 1 from by
          refine ⟨by norm_num, ⟨98477090221164190204145, by norm_num⟩, by norm_num, ⟨147715635331746285306218, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 295431270663492570612437 6924170406175607123729 7 from by
          refine ⟨by norm_num, ⟨147715635331746285306218, by norm_num⟩, by norm_num, ⟨3462085203087803561864, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 6924170406175607123729 5193127804631705342797 2 from by
          refine ⟨by norm_num, ⟨3462085203087803561864, by norm_num⟩, by norm_num, ⟨2596563902315852671398, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 5193127804631705342797 1947422926736889503549 3 from by
          refine ⟨by norm_num, ⟨2596563902315852671398, by norm_num⟩, by norm_num, ⟨973711463368444751774, by norm_num⟩⟩)
        (Word.nil 1947422926736889503549))))))
theorem full_word_27 : Word word_27 4150517416702790074395 1947422926736889503549 := by
  unfold word_27
  have hp := shared_prefix_all 7200
  have ht := suffix_proof_27
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_27 : word_27.length = 46 := by decide
theorem word_sum_27 : word_27.sum = 74 := by decide
theorem infinite_family_27 (d : Nat) :
    ∃ z : Nat, Word word_27 (4150517416702790074395 + 2^75*d) z ∧
      z < 4150517416702790074395 + 2^75*d := by
  have h := word_uniform_descent full_word_27
    (show 1947422926736889503549 < 4150517416702790074395 by norm_num)
    (show 3^word_27.length < 2^word_27.sum by norm_num [word_27, sharedPrefix, suffix_27]) d
  simpa [word_sum_27] using h

/-- Certificate 28; shared prefix plus independently witnessed suffix. -/
def suffix_28 : List Nat := [2, 1, 1, 7, 2, 2]
def word_28 : List Nat := sharedPrefix ++ suffix_28
theorem suffix_proof_28 : Word suffix_28 573452764377780447758537 12757783973126280103027 := by
  unfold suffix_28
  exact Word.cons
        (show ExactStep 573452764377780447758537 430089573283335335818903 2 from by
          refine ⟨by norm_num, ⟨286726382188890223879268, by norm_num⟩, by norm_num, ⟨215044786641667667909451, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 430089573283335335818903 645134359925003003728355 1 from by
          refine ⟨by norm_num, ⟨215044786641667667909451, by norm_num⟩, by norm_num, ⟨322567179962501501864177, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 645134359925003003728355 967701539887504505592533 1 from by
          refine ⟨by norm_num, ⟨322567179962501501864177, by norm_num⟩, by norm_num, ⟨483850769943752252796266, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 967701539887504505592533 22680504841113386849825 7 from by
          refine ⟨by norm_num, ⟨483850769943752252796266, by norm_num⟩, by norm_num, ⟨11340252420556693424912, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 22680504841113386849825 17010378630835040137369 2 from by
          refine ⟨by norm_num, ⟨11340252420556693424912, by norm_num⟩, by norm_num, ⟨8505189315417520068684, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 17010378630835040137369 12757783973126280103027 2 from by
          refine ⟨by norm_num, ⟨8505189315417520068684, by norm_num⟩, by norm_num, ⟨6378891986563140051513, by norm_num⟩⟩)
        (Word.nil 12757783973126280103027))))))
theorem full_word_28 : Word word_28 13595250382442080501787 12757783973126280103027 := by
  unfold word_28
  have hp := shared_prefix_all 23584
  have ht := suffix_proof_28
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_28 : word_28.length = 46 := by decide
theorem word_sum_28 : word_28.sum = 73 := by decide
theorem infinite_family_28 (d : Nat) :
    ∃ z : Nat, Word word_28 (13595250382442080501787 + 2^74*d) z ∧
      z < 13595250382442080501787 + 2^74*d := by
  have h := word_uniform_descent full_word_28
    (show 12757783973126280103027 < 13595250382442080501787 by norm_num)
    (show 3^word_28.length < 2^word_28.sum by norm_num [word_28, sharedPrefix, suffix_28]) d
  simpa [word_sum_28] using h

/-- Certificate 29; shared prefix plus independently witnessed suffix. -/
def suffix_29 : List Nat := [2, 1, 1, 6, 4]
def word_29 : List Nat := sharedPrefix ++ suffix_29
theorem suffix_proof_29 : Word suffix_29 13227540024437168608457 196184828243300291251 := by
  unfold suffix_29
  exact Word.cons
        (show ExactStep 13227540024437168608457 9920655018327876456343 2 from by
          refine ⟨by norm_num, ⟨6613770012218584304228, by norm_num⟩, by norm_num, ⟨4960327509163938228171, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 9920655018327876456343 14880982527491814684515 1 from by
          refine ⟨by norm_num, ⟨4960327509163938228171, by norm_num⟩, by norm_num, ⟨7440491263745907342257, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 14880982527491814684515 22321473791237722026773 1 from by
          refine ⟨by norm_num, ⟨7440491263745907342257, by norm_num⟩, by norm_num, ⟨11160736895618861013386, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 22321473791237722026773 1046319083964268220005 6 from by
          refine ⟨by norm_num, ⟨11160736895618861013386, by norm_num⟩, by norm_num, ⟨523159541982134110002, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1046319083964268220005 196184828243300291251 4 from by
          refine ⟨by norm_num, ⟨523159541982134110002, by norm_num⟩, by norm_num, ⟨98092414121650145625, by norm_num⟩⟩)
        (Word.nil 196184828243300291251)))))
theorem full_word_29 : Word word_29 313594649371203338267 196184828243300291251 := by
  unfold word_29
  have hp := shared_prefix_all 544
  have ht := suffix_proof_29
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_29 : word_29.length = 45 := by decide
theorem word_sum_29 : word_29.sum = 72 := by decide
theorem infinite_family_29 (d : Nat) :
    ∃ z : Nat, Word word_29 (313594649371203338267 + 2^73*d) z ∧
      z < 313594649371203338267 + 2^73*d := by
  have h := word_uniform_descent full_word_29
    (show 196184828243300291251 < 313594649371203338267 by norm_num)
    (show 3^word_29.length < 2^word_29.sum by norm_num [word_29, sharedPrefix, suffix_29]) d
  simpa [word_sum_29] using h

/-- Certificate 30; shared prefix plus independently witnessed suffix. -/
def suffix_30 : List Nat := [2, 1, 1, 6, 5]
def word_30 : List Nat := sharedPrefix ++ suffix_30
theorem suffix_proof_30 : Word suffix_30 212418730905625890084041 1575248767397066994947 := by
  unfold suffix_30
  exact Word.cons
        (show ExactStep 212418730905625890084041 159314048179219417563031 2 from by
          refine ⟨by norm_num, ⟨106209365452812945042020, by norm_num⟩, by norm_num, ⟨79657024089609708781515, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 159314048179219417563031 238971072268829126344547 1 from by
          refine ⟨by norm_num, ⟨79657024089609708781515, by norm_num⟩, by norm_num, ⟨119485536134414563172273, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 238971072268829126344547 358456608403243689516821 1 from by
          refine ⟨by norm_num, ⟨119485536134414563172273, by norm_num⟩, by norm_num, ⟨179228304201621844758410, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 358456608403243689516821 16802653518902047946101 6 from by
          refine ⟨by norm_num, ⟨179228304201621844758410, by norm_num⟩, by norm_num, ⟨8401326759451023973050, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 16802653518902047946101 1575248767397066994947 5 from by
          refine ⟨by norm_num, ⟨8401326759451023973050, by norm_num⟩, by norm_num, ⟨787624383698533497473, by norm_num⟩⟩)
        (Word.nil 1575248767397066994947)))))
theorem full_word_30 : Word word_30 5035961132240848551963 1575248767397066994947 := by
  unfold word_30
  have hp := shared_prefix_all 8736
  have ht := suffix_proof_30
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_30 : word_30.length = 45 := by decide
theorem word_sum_30 : word_30.sum = 73 := by decide
theorem infinite_family_30 (d : Nat) :
    ∃ z : Nat, Word word_30 (5035961132240848551963 + 2^74*d) z ∧
      z < 5035961132240848551963 + 2^74*d := by
  have h := word_uniform_descent full_word_30
    (show 1575248767397066994947 < 5035961132240848551963 by norm_num)
    (show 3^word_30.length < 2^word_30.sum by norm_num [word_30, sharedPrefix, suffix_30]) d
  simpa [word_sum_30] using h

/-- Certificate 31; shared prefix plus independently witnessed suffix. -/
def suffix_31 : List Nat := [2, 1, 1, 6, 6]
def word_31 : List Nat := sharedPrefix ++ suffix_31
theorem suffix_proof_31 : Word suffix_31 610801112668003333035209 2264780736973950346795 := by
  unfold suffix_31
  exact Word.cons
        (show ExactStep 610801112668003333035209 458100834501002499776407 2 from by
          refine ⟨by norm_num, ⟨305400556334001666517604, by norm_num⟩, by norm_num, ⟨229050417250501249888203, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 458100834501002499776407 687151251751503749664611 1 from by
          refine ⟨by norm_num, ⟨229050417250501249888203, by norm_num⟩, by norm_num, ⟨343575625875751874832305, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 687151251751503749664611 1030726877627255624496917 1 from by
          refine ⟨by norm_num, ⟨343575625875751874832305, by norm_num⟩, by norm_num, ⟨515363438813627812248458, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1030726877627255624496917 48315322388777607398293 6 from by
          refine ⟨by norm_num, ⟨515363438813627812248458, by norm_num⟩, by norm_num, ⟨24157661194388803699146, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 48315322388777607398293 2264780736973950346795 6 from by
          refine ⟨by norm_num, ⟨24157661194388803699146, by norm_num⟩, by norm_num, ⟨1132390368486975173397, by norm_num⟩⟩)
        (Word.nil 2264780736973950346795)))))
theorem full_word_31 : Word word_31 14480694097980138979355 2264780736973950346795 := by
  unfold word_31
  have hp := shared_prefix_all 25120
  have ht := suffix_proof_31
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_31 : word_31.length = 45 := by decide
theorem word_sum_31 : word_31.sum = 74 := by decide
theorem infinite_family_31 (d : Nat) :
    ∃ z : Nat, Word word_31 (14480694097980138979355 + 2^75*d) z ∧
      z < 14480694097980138979355 + 2^75*d := by
  have h := word_uniform_descent full_word_31
    (show 2264780736973950346795 < 14480694097980138979355 by norm_num)
    (show 3^word_31.length < 2^word_31.sum by norm_num [word_31, sharedPrefix, suffix_31]) d
  simpa [word_sum_31] using h

/-- Certificate 32; shared prefix plus independently witnessed suffix. -/
def suffix_32 : List Nat := [2, 1, 1, 6, 3, 2]
def word_32 : List Nat := sharedPrefix ++ suffix_32
theorem suffix_proof_32 : Word suffix_32 112823135465031529346249 2510011772278075710859 := by
  unfold suffix_32
  exact Word.cons
        (show ExactStep 112823135465031529346249 84617351598773647009687 2 from by
          refine ⟨by norm_num, ⟨56411567732515764673124, by norm_num⟩, by norm_num, ⟨42308675799386823504843, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 84617351598773647009687 126926027398160470514531 1 from by
          refine ⟨by norm_num, ⟨42308675799386823504843, by norm_num⟩, by norm_num, ⟨63463013699080235257265, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 126926027398160470514531 190389041097240705771797 1 from by
          refine ⟨by norm_num, ⟨63463013699080235257265, by norm_num⟩, by norm_num, ⟨95194520548620352885898, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 190389041097240705771797 8924486301433158083053 6 from by
          refine ⟨by norm_num, ⟨95194520548620352885898, by norm_num⟩, by norm_num, ⟨4462243150716579041526, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 8924486301433158083053 3346682363037434281145 3 from by
          refine ⟨by norm_num, ⟨4462243150716579041526, by norm_num⟩, by norm_num, ⟨1673341181518717140572, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 3346682363037434281145 2510011772278075710859 2 from by
          refine ⟨by norm_num, ⟨1673341181518717140572, by norm_num⟩, by norm_num, ⟨1255005886139037855429, by norm_num⟩⟩)
        (Word.nil 2510011772278075710859))))))
theorem full_word_32 : Word word_32 2674777890806025945115 2510011772278075710859 := by
  unfold word_32
  have hp := shared_prefix_all 4640
  have ht := suffix_proof_32
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_32 : word_32.length = 46 := by decide
theorem word_sum_32 : word_32.sum = 73 := by decide
theorem infinite_family_32 (d : Nat) :
    ∃ z : Nat, Word word_32 (2674777890806025945115 + 2^74*d) z ∧
      z < 2674777890806025945115 + 2^74*d := by
  have h := word_uniform_descent full_word_32
    (show 2510011772278075710859 < 2674777890806025945115 by norm_num)
    (show 3^word_32.length < 2^word_32.sum by norm_num [word_32, sharedPrefix, suffix_32]) d
  simpa [word_sum_32] using h

/-- Certificate 33; shared prefix plus independently witnessed suffix. -/
def suffix_33 : List Nat := [2, 1, 1, 6, 3, 3]
def word_33 : List Nat := sharedPrefix ++ suffix_33
theorem suffix_proof_33 : Word suffix_33 1307970280752163858199753 14549413065617789499323 := by
  unfold suffix_33
  exact Word.cons
        (show ExactStep 1307970280752163858199753 980977710564122893649815 2 from by
          refine ⟨by norm_num, ⟨653985140376081929099876, by norm_num⟩, by norm_num, ⟨490488855282061446824907, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 980977710564122893649815 1471466565846184340474723 1 from by
          refine ⟨by norm_num, ⟨490488855282061446824907, by norm_num⟩, by norm_num, ⟨735733282923092170237361, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1471466565846184340474723 2207199848769276510712085 1 from by
          refine ⟨by norm_num, ⟨735733282923092170237361, by norm_num⟩, by norm_num, ⟨1103599924384638255356042, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2207199848769276510712085 103462492911059836439629 6 from by
          refine ⟨by norm_num, ⟨1103599924384638255356042, by norm_num⟩, by norm_num, ⟨51731246455529918219814, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 103462492911059836439629 38798434841647438664861 3 from by
          refine ⟨by norm_num, ⟨51731246455529918219814, by norm_num⟩, by norm_num, ⟨19399217420823719332430, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 38798434841647438664861 14549413065617789499323 3 from by
          refine ⟨by norm_num, ⟨19399217420823719332430, by norm_num⟩, by norm_num, ⟨7274706532808894749661, by norm_num⟩⟩)
        (Word.nil 14549413065617789499323))))))
theorem full_word_33 : Word word_33 31008976788023897227291 14549413065617789499323 := by
  unfold word_33
  have hp := shared_prefix_all 53792
  have ht := suffix_proof_33
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_33 : word_33.length = 46 := by decide
theorem word_sum_33 : word_33.sum = 74 := by decide
theorem infinite_family_33 (d : Nat) :
    ∃ z : Nat, Word word_33 (31008976788023897227291 + 2^75*d) z ∧
      z < 31008976788023897227291 + 2^75*d := by
  have h := word_uniform_descent full_word_33
    (show 14549413065617789499323 < 31008976788023897227291 by norm_num)
    (show 3^word_33.length < 2^word_33.sum by norm_num [word_33, sharedPrefix, suffix_33]) d
  simpa [word_sum_33] using h

/-- Certificate 34; shared prefix plus independently witnessed suffix. -/
def suffix_34 : List Nat := [2, 1, 1, 6, 2, 4]
def word_34 : List Nat := sharedPrefix ++ suffix_34
theorem suffix_proof_34 : Word suffix_34 162620933185328709715145 1808939518617319173925 := by
  unfold suffix_34
  exact Word.cons
        (show ExactStep 162620933185328709715145 121965699888996532286359 2 from by
          refine ⟨by norm_num, ⟨81310466592664354857572, by norm_num⟩, by norm_num, ⟨60982849944498266143179, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 121965699888996532286359 182948549833494798429539 1 from by
          refine ⟨by norm_num, ⟨60982849944498266143179, by norm_num⟩, by norm_num, ⟨91474274916747399214769, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 182948549833494798429539 274422824750242197644309 1 from by
          refine ⟨by norm_num, ⟨91474274916747399214769, by norm_num⟩, by norm_num, ⟨137211412375121098822154, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 274422824750242197644309 12863569910167603014577 6 from by
          refine ⟨by norm_num, ⟨137211412375121098822154, by norm_num⟩, by norm_num, ⟨6431784955083801507288, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 12863569910167603014577 9647677432625702260933 2 from by
          refine ⟨by norm_num, ⟨6431784955083801507288, by norm_num⟩, by norm_num, ⟨4823838716312851130466, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 9647677432625702260933 1808939518617319173925 4 from by
          refine ⟨by norm_num, ⟨4823838716312851130466, by norm_num⟩, by norm_num, ⟨904469759308659586962, by norm_num⟩⟩)
        (Word.nil 1808939518617319173925))))))
theorem full_word_34 : Word word_34 3855369511523437248539 1808939518617319173925 := by
  unfold word_34
  have hp := shared_prefix_all 6688
  have ht := suffix_proof_34
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_34 : word_34.length = 46 := by decide
theorem word_sum_34 : word_34.sum = 74 := by decide
theorem infinite_family_34 (d : Nat) :
    ∃ z : Nat, Word word_34 (3855369511523437248539 + 2^75*d) z ∧
      z < 3855369511523437248539 + 2^75*d := by
  have h := word_uniform_descent full_word_34
    (show 1808939518617319173925 < 3855369511523437248539 by norm_num)
    (show 3^word_34.length < 2^word_34.sum by norm_num [word_34, sharedPrefix, suffix_34]) d
  simpa [word_sum_34] using h

/-- Certificate 35; shared prefix plus independently witnessed suffix. -/
def suffix_35 : List Nat := [2, 1, 1, 6, 2, 3]
def word_35 : List Nat := sharedPrefix ++ suffix_35
theorem suffix_proof_35 : Word suffix_35 561003314947706152666313 12480817156887139443779 := by
  unfold suffix_35
  exact Word.cons
        (show ExactStep 561003314947706152666313 420752486210779614499735 2 from by
          refine ⟨by norm_num, ⟨280501657473853076333156, by norm_num⟩, by norm_num, ⟨210376243105389807249867, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 420752486210779614499735 631128729316169421749603 1 from by
          refine ⟨by norm_num, ⟨210376243105389807249867, by norm_num⟩, by norm_num, ⟨315564364658084710874801, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 631128729316169421749603 946693093974254132624405 1 from by
          refine ⟨by norm_num, ⟨315564364658084710874801, by norm_num⟩, by norm_num, ⟨473346546987127066312202, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 946693093974254132624405 44376238780043162466769 6 from by
          refine ⟨by norm_num, ⟨473346546987127066312202, by norm_num⟩, by norm_num, ⟨22188119390021581233384, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 44376238780043162466769 33282179085032371850077 2 from by
          refine ⟨by norm_num, ⟨22188119390021581233384, by norm_num⟩, by norm_num, ⟨16641089542516185925038, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 33282179085032371850077 12480817156887139443779 3 from by
          refine ⟨by norm_num, ⟨16641089542516185925038, by norm_num⟩, by norm_num, ⟨6240408578443569721889, by norm_num⟩⟩)
        (Word.nil 12480817156887139443779))))))
theorem full_word_35 : Word word_35 13300102477262727675931 12480817156887139443779 := by
  unfold word_35
  have hp := shared_prefix_all 23072
  have ht := suffix_proof_35
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_35 : word_35.length = 46 := by decide
theorem word_sum_35 : word_35.sum = 73 := by decide
theorem infinite_family_35 (d : Nat) :
    ∃ z : Nat, Word word_35 (13300102477262727675931 + 2^74*d) z ∧
      z < 13300102477262727675931 + 2^74*d := by
  have h := word_uniform_descent full_word_35
    (show 12480817156887139443779 < 13300102477262727675931 by norm_num)
    (show 3^word_35.length < 2^word_35.sum by norm_num [word_35, sharedPrefix, suffix_35]) d
  simpa [word_sum_35] using h

/-- Certificate 36; shared prefix plus independently witnessed suffix. -/
def suffix_36 : List Nat := [2, 1, 1, 6, 1, 5]
def word_36 : List Nat := sharedPrefix ++ suffix_36
theorem suffix_proof_36 : Word suffix_36 386711022926666021375177 4301640864769585107155 := by
  unfold suffix_36
  exact Word.cons
        (show ExactStep 386711022926666021375177 290033267194999516031383 2 from by
          refine ⟨by norm_num, ⟨193355511463333010687588, by norm_num⟩, by norm_num, ⟨145016633597499758015691, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 290033267194999516031383 435049900792499274047075 1 from by
          refine ⟨by norm_num, ⟨145016633597499758015691, by norm_num⟩, by norm_num, ⟨217524950396249637023537, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 435049900792499274047075 652574851188748911070613 1 from by
          refine ⟨by norm_num, ⟨217524950396249637023537, by norm_num⟩, by norm_num, ⟨326287425594374455535306, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 652574851188748911070613 30589446149472605206435 6 from by
          refine ⟨by norm_num, ⟨326287425594374455535306, by norm_num⟩, by norm_num, ⟨15294723074736302603217, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 30589446149472605206435 45884169224208907809653 1 from by
          refine ⟨by norm_num, ⟨15294723074736302603217, by norm_num⟩, by norm_num, ⟨22942084612104453904826, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 45884169224208907809653 4301640864769585107155 5 from by
          refine ⟨by norm_num, ⟨22942084612104453904826, by norm_num⟩, by norm_num, ⟨2150820432384792553577, by norm_num⟩⟩)
        (Word.nil 4301640864769585107155))))))
theorem full_word_36 : Word word_36 9168031804751788113947 4301640864769585107155 := by
  unfold word_36
  have hp := shared_prefix_all 15904
  have ht := suffix_proof_36
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_36 : word_36.length = 46 := by decide
theorem word_sum_36 : word_36.sum = 74 := by decide
theorem infinite_family_36 (d : Nat) :
    ∃ z : Nat, Word word_36 (9168031804751788113947 + 2^75*d) z ∧
      z < 9168031804751788113947 + 2^75*d := by
  have h := word_uniform_descent full_word_36
    (show 4301640864769585107155 < 9168031804751788113947 by norm_num)
    (show 3^word_36.length < 2^word_36.sum by norm_num [word_36, sharedPrefix, suffix_36]) d
  simpa [word_sum_36] using h

/-- Certificate 37; shared prefix plus independently witnessed suffix. -/
def suffix_37 : List Nat := [2, 1, 1, 6, 1, 4]
def word_37 : List Nat := sharedPrefix ++ suffix_37
theorem suffix_proof_37 : Word suffix_37 785093404689043464326345 17466219849191671310239 := by
  unfold suffix_37
  exact Word.cons
        (show ExactStep 785093404689043464326345 588820053516782598244759 2 from by
          refine ⟨by norm_num, ⟨392546702344521732163172, by norm_num⟩, by norm_num, ⟨294410026758391299122379, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 588820053516782598244759 883230080275173897367139 1 from by
          refine ⟨by norm_num, ⟨294410026758391299122379, by norm_num⟩, by norm_num, ⟨441615040137586948683569, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 883230080275173897367139 1324845120412760846050709 1 from by
          refine ⟨by norm_num, ⟨441615040137586948683569, by norm_num⟩, by norm_num, ⟨662422560206380423025354, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1324845120412760846050709 62102115019348164658627 6 from by
          refine ⟨by norm_num, ⟨662422560206380423025354, by norm_num⟩, by norm_num, ⟨31051057509674082329313, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 62102115019348164658627 93153172529022246987941 1 from by
          refine ⟨by norm_num, ⟨31051057509674082329313, by norm_num⟩, by norm_num, ⟨46576586264511123493970, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 93153172529022246987941 17466219849191671310239 4 from by
          refine ⟨by norm_num, ⟨46576586264511123493970, by norm_num⟩, by norm_num, ⟨8733109924595835655119, by norm_num⟩⟩)
        (Word.nil 17466219849191671310239))))))
theorem full_word_37 : Word word_37 18612764770491078541339 17466219849191671310239 := by
  unfold word_37
  have hp := shared_prefix_all 32288
  have ht := suffix_proof_37
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_37 : word_37.length = 46 := by decide
theorem word_sum_37 : word_37.sum = 73 := by decide
theorem infinite_family_37 (d : Nat) :
    ∃ z : Nat, Word word_37 (18612764770491078541339 + 2^74*d) z ∧
      z < 18612764770491078541339 + 2^74*d := by
  have h := word_uniform_descent full_word_37
    (show 17466219849191671310239 < 18612764770491078541339 by norm_num)
    (show 3^word_37.length < 2^word_37.sum by norm_num [word_37, sharedPrefix, suffix_37]) d
  simpa [word_sum_37] using h

/-- Certificate 38; shared prefix plus independently witnessed suffix. -/
def suffix_38 : List Nat := [2, 1, 1, 5, 2, 5]
def word_38 : List Nat := sharedPrefix ++ suffix_38
theorem suffix_proof_38 : Word suffix_38 156396208470291562169033 1739697814557534009113 := by
  unfold suffix_38
  exact Word.cons
        (show ExactStep 156396208470291562169033 117297156352718671626775 2 from by
          refine ⟨by norm_num, ⟨78198104235145781084516, by norm_num⟩, by norm_num, ⟨58648578176359335813387, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 117297156352718671626775 175945734529078007440163 1 from by
          refine ⟨by norm_num, ⟨58648578176359335813387, by norm_num⟩, by norm_num, ⟨87972867264539003720081, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 175945734529078007440163 263918601793617011160245 1 from by
          refine ⟨by norm_num, ⟨87972867264539003720081, by norm_num⟩, by norm_num, ⟨131959300896808505580122, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 263918601793617011160245 24742368918151594796273 5 from by
          refine ⟨by norm_num, ⟨131959300896808505580122, by norm_num⟩, by norm_num, ⟨12371184459075797398136, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 24742368918151594796273 18556776688613696097205 2 from by
          refine ⟨by norm_num, ⟨12371184459075797398136, by norm_num⟩, by norm_num, ⟨9278388344306848048602, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 18556776688613696097205 1739697814557534009113 5 from by
          refine ⟨by norm_num, ⟨9278388344306848048602, by norm_num⟩, by norm_num, ⟨869848907278767004556, by norm_num⟩⟩)
        (Word.nil 1739697814557534009113))))))
theorem full_word_38 : Word word_38 3707795558933760835611 1739697814557534009113 := by
  unfold word_38
  have hp := shared_prefix_all 6432
  have ht := suffix_proof_38
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_38 : word_38.length = 46 := by decide
theorem word_sum_38 : word_38.sum = 74 := by decide
theorem infinite_family_38 (d : Nat) :
    ∃ z : Nat, Word word_38 (3707795558933760835611 + 2^75*d) z ∧
      z < 3707795558933760835611 + 2^75*d := by
  have h := word_uniform_descent full_word_38
    (show 1739697814557534009113 < 3707795558933760835611 by norm_num)
    (show 3^word_38.length < 2^word_38.sum by norm_num [word_38, sharedPrefix, suffix_38]) d
  simpa [word_sum_38] using h

/-- Certificate 39; shared prefix plus independently witnessed suffix. -/
def suffix_39 : List Nat := [2, 1, 1, 5, 2, 4]
def word_39 : List Nat := sharedPrefix ++ suffix_39
theorem suffix_proof_39 : Word suffix_39 554778590232669005120201 12342333748767569114155 := by
  unfold suffix_39
  exact Word.cons
        (show ExactStep 554778590232669005120201 416083942674501753840151 2 from by
          refine ⟨by norm_num, ⟨277389295116334502560100, by norm_num⟩, by norm_num, ⟨208041971337250876920075, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 416083942674501753840151 624125914011752630760227 1 from by
          refine ⟨by norm_num, ⟨208041971337250876920075, by norm_num⟩, by norm_num, ⟨312062957005876315380113, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 624125914011752630760227 936188871017628946140341 1 from by
          refine ⟨by norm_num, ⟨312062957005876315380113, by norm_num⟩, by norm_num, ⟨468094435508814473070170, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 936188871017628946140341 87767706657902713700657 5 from by
          refine ⟨by norm_num, ⟨468094435508814473070170, by norm_num⟩, by norm_num, ⟨43883853328951356850328, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 87767706657902713700657 65825779993427035275493 2 from by
          refine ⟨by norm_num, ⟨43883853328951356850328, by norm_num⟩, by norm_num, ⟨32912889996713517637746, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 65825779993427035275493 12342333748767569114155 4 from by
          refine ⟨by norm_num, ⟨32912889996713517637746, by norm_num⟩, by norm_num, ⟨6171166874383784557077, by norm_num⟩⟩)
        (Word.nil 12342333748767569114155))))))
theorem full_word_39 : Word word_39 13152528524673051263003 12342333748767569114155 := by
  unfold word_39
  have hp := shared_prefix_all 22816
  have ht := suffix_proof_39
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_39 : word_39.length = 46 := by decide
theorem word_sum_39 : word_39.sum = 73 := by decide
theorem infinite_family_39 (d : Nat) :
    ∃ z : Nat, Word word_39 (13152528524673051263003 + 2^74*d) z ∧
      z < 13152528524673051263003 + 2^74*d := by
  have h := word_uniform_descent full_word_39
    (show 12342333748767569114155 < 13152528524673051263003 by norm_num)
    (show 3^word_39.length < 2^word_39.sum by norm_num [word_39, sharedPrefix, suffix_39]) d
  simpa [word_sum_39] using h

/-- Certificate 40; shared prefix plus independently witnessed suffix. -/
def suffix_40 : List Nat := [2, 1, 1, 5, 3, 3]
def word_40 : List Nat := sharedPrefix ++ suffix_40
theorem suffix_proof_40 : Word suffix_40 330688500491331693460169 7356931056463037247695 := by
  unfold suffix_40
  exact Word.cons
        (show ExactStep 330688500491331693460169 248016375368498770095127 2 from by
          refine ⟨by norm_num, ⟨165344250245665846730084, by norm_num⟩, by norm_num, ⟨124008187684249385047563, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 248016375368498770095127 372024563052748155142691 1 from by
          refine ⟨by norm_num, ⟨124008187684249385047563, by norm_num⟩, by norm_num, ⟨186012281526374077571345, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 372024563052748155142691 558036844579122232714037 1 from by
          refine ⟨by norm_num, ⟨186012281526374077571345, by norm_num⟩, by norm_num, ⟨279018422289561116357018, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 558036844579122232714037 52315954179292709316941 5 from by
          refine ⟨by norm_num, ⟨279018422289561116357018, by norm_num⟩, by norm_num, ⟨26157977089646354658470, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 52315954179292709316941 19618482817234765993853 3 from by
          refine ⟨by norm_num, ⟨26157977089646354658470, by norm_num⟩, by norm_num, ⟨9809241408617382996926, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 19618482817234765993853 7356931056463037247695 3 from by
          refine ⟨by norm_num, ⟨9809241408617382996926, by norm_num⟩, by norm_num, ⟨3678465528231518623847, by norm_num⟩⟩)
        (Word.nil 7356931056463037247695))))))
theorem full_word_40 : Word word_40 7839866231444700397595 7356931056463037247695 := by
  unfold word_40
  have hp := shared_prefix_all 13600
  have ht := suffix_proof_40
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_40 : word_40.length = 46 := by decide
theorem word_sum_40 : word_40.sum = 73 := by decide
theorem infinite_family_40 (d : Nat) :
    ∃ z : Nat, Word word_40 (7839866231444700397595 + 2^74*d) z ∧
      z < 7839866231444700397595 + 2^74*d := by
  have h := word_uniform_descent full_word_40
    (show 7356931056463037247695 < 7839866231444700397595 by norm_num)
    (show 3^word_40.length < 2^word_40.sum by norm_num [word_40, sharedPrefix, suffix_40]) d
  simpa [word_sum_40] using h

/-- Certificate 41; shared prefix plus independently witnessed suffix. -/
def suffix_41 : List Nat := [2, 1, 1, 5, 3, 4]
def word_41 : List Nat := sharedPrefix ++ suffix_41
theorem suffix_proof_41 : Word suffix_41 1525835645778464022313673 16972872707710270267741 := by
  unfold suffix_41
  exact Word.cons
        (show ExactStep 1525835645778464022313673 1144376734333848016735255 2 from by
          refine ⟨by norm_num, ⟨762917822889232011156836, by norm_num⟩, by norm_num, ⟨572188367166924008367627, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1144376734333848016735255 1716565101500772025102883 1 from by
          refine ⟨by norm_num, ⟨572188367166924008367627, by norm_num⟩, by norm_num, ⟨858282550750386012551441, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1716565101500772025102883 2574847652251158037654325 1 from by
          refine ⟨by norm_num, ⟨858282550750386012551441, by norm_num⟩, by norm_num, ⟨1287423826125579018827162, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2574847652251158037654325 241391967398546066030093 5 from by
          refine ⟨by norm_num, ⟨1287423826125579018827162, by norm_num⟩, by norm_num, ⟨120695983699273033015046, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 241391967398546066030093 90521987774454774761285 3 from by
          refine ⟨by norm_num, ⟨120695983699273033015046, by norm_num⟩, by norm_num, ⟨45260993887227387380642, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 90521987774454774761285 16972872707710270267741 4 from by
          refine ⟨by norm_num, ⟨45260993887227387380642, by norm_num⟩, by norm_num, ⟨8486436353855135133870, by norm_num⟩⟩)
        (Word.nil 16972872707710270267741))))))
theorem full_word_41 : Word word_41 36174065128662571679771 16972872707710270267741 := by
  unfold word_41
  have hp := shared_prefix_all 62752
  have ht := suffix_proof_41
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_41 : word_41.length = 46 := by decide
theorem word_sum_41 : word_41.sum = 74 := by decide
theorem infinite_family_41 (d : Nat) :
    ∃ z : Nat, Word word_41 (36174065128662571679771 + 2^75*d) z ∧
      z < 36174065128662571679771 + 2^75*d := by
  have h := word_uniform_descent full_word_41
    (show 16972872707710270267741 < 36174065128662571679771 by norm_num)
    (show 3^word_41.length < 2^word_41.sum by norm_num [word_41, sharedPrefix, suffix_41]) d
  simpa [word_sum_41] using h

/-- Certificate 42; shared prefix plus independently witnessed suffix. -/
def suffix_42 : List Nat := [2, 1, 1, 5, 4, 3]
def word_42 : List Nat := sharedPrefix ++ suffix_42
theorem suffix_proof_42 : Word suffix_42 1077655466295789398993609 11987470015405738401281 := by
  unfold suffix_42
  exact Word.cons
        (show ExactStep 1077655466295789398993609 808241599721842049245207 2 from by
          refine ⟨by norm_num, ⟨538827733147894699496804, by norm_num⟩, by norm_num, ⟨404120799860921024622603, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 808241599721842049245207 1212362399582763073867811 1 from by
          refine ⟨by norm_num, ⟨404120799860921024622603, by norm_num⟩, by norm_num, ⟨606181199791381536933905, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1212362399582763073867811 1818543599374144610801717 1 from by
          refine ⟨by norm_num, ⟨606181199791381536933905, by norm_num⟩, by norm_num, ⟨909271799687072305400858, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1818543599374144610801717 170488462441326057262661 5 from by
          refine ⟨by norm_num, ⟨909271799687072305400858, by norm_num⟩, by norm_num, ⟨85244231220663028631330, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 170488462441326057262661 31966586707748635736749 4 from by
          refine ⟨by norm_num, ⟨85244231220663028631330, by norm_num⟩, by norm_num, ⟨15983293353874317868374, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 31966586707748635736749 11987470015405738401281 3 from by
          refine ⟨by norm_num, ⟨15983293353874317868374, by norm_num⟩, by norm_num, ⟨5993735007702869200640, by norm_num⟩⟩)
        (Word.nil 11987470015405738401281))))))
theorem full_word_42 : Word word_42 25548740542205869948955 11987470015405738401281 := by
  unfold word_42
  have hp := shared_prefix_all 44320
  have ht := suffix_proof_42
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_42 : word_42.length = 46 := by decide
theorem word_sum_42 : word_42.sum = 74 := by decide
theorem infinite_family_42 (d : Nat) :
    ∃ z : Nat, Word word_42 (25548740542205869948955 + 2^75*d) z ∧
      z < 25548740542205869948955 + 2^75*d := by
  have h := word_uniform_descent full_word_42
    (show 11987470015405738401281 < 25548740542205869948955 by norm_num)
    (show 3^word_42.length < 2^word_42.sum by norm_num [word_42, sharedPrefix, suffix_42]) d
  simpa [word_sum_42] using h

/-- Certificate 43; shared prefix plus independently witnessed suffix. -/
def suffix_43 : List Nat := [2, 1, 1, 5, 4, 2]
def word_43 : List Nat := sharedPrefix ++ suffix_43
theorem suffix_proof_43 : Word suffix_43 679273084533411956042441 15112001911158975706633 := by
  unfold suffix_43
  exact Word.cons
        (show ExactStep 679273084533411956042441 509454813400058967031831 2 from by
          refine ⟨by norm_num, ⟨339636542266705978021220, by norm_num⟩, by norm_num, ⟨254727406700029483515915, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 509454813400058967031831 764182220100088450547747 1 from by
          refine ⟨by norm_num, ⟨254727406700029483515915, by norm_num⟩, by norm_num, ⟨382091110050044225273873, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 764182220100088450547747 1146273330150132675821621 1 from by
          refine ⟨by norm_num, ⟨382091110050044225273873, by norm_num⟩, by norm_num, ⟨573136665075066337910810, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1146273330150132675821621 107463124701574938358277 5 from by
          refine ⟨by norm_num, ⟨573136665075066337910810, by norm_num⟩, by norm_num, ⟨53731562350787469179138, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 107463124701574938358277 20149335881545300942177 4 from by
          refine ⟨by norm_num, ⟨53731562350787469179138, by norm_num⟩, by norm_num, ⟨10074667940772650471088, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 20149335881545300942177 15112001911158975706633 2 from by
          refine ⟨by norm_num, ⟨10074667940772650471088, by norm_num⟩, by norm_num, ⟨7556000955579487853316, by norm_num⟩⟩)
        (Word.nil 15112001911158975706633))))))
theorem full_word_43 : Word word_43 16104007576466579521563 15112001911158975706633 := by
  unfold word_43
  have hp := shared_prefix_all 27936
  have ht := suffix_proof_43
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_43 : word_43.length = 46 := by decide
theorem word_sum_43 : word_43.sum = 73 := by decide
theorem infinite_family_43 (d : Nat) :
    ∃ z : Nat, Word word_43 (16104007576466579521563 + 2^74*d) z ∧
      z < 16104007576466579521563 + 2^74*d := by
  have h := word_uniform_descent full_word_43
    (show 15112001911158975706633 < 16104007576466579521563 by norm_num)
    (show 3^word_43.length < 2^word_43.sum by norm_num [word_43, sharedPrefix, suffix_43]) d
  simpa [word_sum_43] using h

/-- Certificate 44; shared prefix plus independently witnessed suffix. -/
def suffix_44 : List Nat := [2, 1, 1, 5, 5]
def word_44 : List Nat := sharedPrefix ++ suffix_44
theorem suffix_proof_44 : Word suffix_44 181295107330440152353481 2688886174395566224481 := by
  unfold suffix_44
  exact Word.cons
        (show ExactStep 181295107330440152353481 135971330497830114265111 2 from by
          refine ⟨by norm_num, ⟨90647553665220076176740, by norm_num⟩, by norm_num, ⟨67985665248915057132555, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 135971330497830114265111 203956995746745171397667 1 from by
          refine ⟨by norm_num, ⟨67985665248915057132555, by norm_num⟩, by norm_num, ⟨101978497873372585698833, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 203956995746745171397667 305935493620117757096501 1 from by
          refine ⟨by norm_num, ⟨101978497873372585698833, by norm_num⟩, by norm_num, ⟨152967746810058878548250, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 305935493620117757096501 28681452526886039727797 5 from by
          refine ⟨by norm_num, ⟨152967746810058878548250, by norm_num⟩, by norm_num, ⟨14340726263443019863898, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 28681452526886039727797 2688886174395566224481 5 from by
          refine ⟨by norm_num, ⟨14340726263443019863898, by norm_num⟩, by norm_num, ⟨1344443087197783112240, by norm_num⟩⟩)
        (Word.nil 2688886174395566224481)))))
theorem full_word_44 : Word word_44 4298091369292466487323 2688886174395566224481 := by
  unfold word_44
  have hp := shared_prefix_all 7456
  have ht := suffix_proof_44
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_44 : word_44.length = 45 := by decide
theorem word_sum_44 : word_44.sum = 72 := by decide
theorem infinite_family_44 (d : Nat) :
    ∃ z : Nat, Word word_44 (4298091369292466487323 + 2^73*d) z ∧
      z < 4298091369292466487323 + 2^73*d := by
  have h := word_uniform_descent full_word_44
    (show 2688886174395566224481 < 4298091369292466487323 by norm_num)
    (show 3^word_44.length < 2^word_44.sum by norm_num [word_44, sharedPrefix, suffix_44]) d
  simpa [word_sum_44] using h

/-- Certificate 45; shared prefix plus independently witnessed suffix. -/
def suffix_45 : List Nat := [2, 1, 1, 5, 7]
def word_45 : List Nat := sharedPrefix ++ suffix_45
theorem suffix_proof_45 : Word suffix_45 380486298211628873829065 1410799720236599980781 := by
  unfold suffix_45
  exact Word.cons
        (show ExactStep 380486298211628873829065 285364723658721655371799 2 from by
          refine ⟨by norm_num, ⟨190243149105814436914532, by norm_num⟩, by norm_num, ⟨142682361829360827685899, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 285364723658721655371799 428047085488082483057699 1 from by
          refine ⟨by norm_num, ⟨142682361829360827685899, by norm_num⟩, by norm_num, ⟨214023542744041241528849, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 428047085488082483057699 642070628232123724586549 1 from by
          refine ⟨by norm_num, ⟨214023542744041241528849, by norm_num⟩, by norm_num, ⟨321035314116061862293274, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 642070628232123724586549 60194121396761599179989 5 from by
          refine ⟨by norm_num, ⟨321035314116061862293274, by norm_num⟩, by norm_num, ⟨30097060698380799589994, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 60194121396761599179989 1410799720236599980781 7 from by
          refine ⟨by norm_num, ⟨30097060698380799589994, by norm_num⟩, by norm_num, ⟨705399860118299990390, by norm_num⟩⟩)
        (Word.nil 1410799720236599980781)))))
theorem full_word_45 : Word word_45 9020457852162111701019 1410799720236599980781 := by
  unfold word_45
  have hp := shared_prefix_all 15648
  have ht := suffix_proof_45
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_45 : word_45.length = 45 := by decide
theorem word_sum_45 : word_45.sum = 74 := by decide
theorem infinite_family_45 (d : Nat) :
    ∃ z : Nat, Word word_45 (9020457852162111701019 + 2^75*d) z ∧
      z < 9020457852162111701019 + 2^75*d := by
  have h := word_uniform_descent full_word_45
    (show 1410799720236599980781 < 9020457852162111701019 by norm_num)
    (show 3^word_45.length < 2^word_45.sum by norm_num [word_45, sharedPrefix, suffix_45]) d
  simpa [word_sum_45] using h

/-- Certificate 46; shared prefix plus independently witnessed suffix. -/
def suffix_46 : List Nat := [2, 1, 1, 5, 6]
def word_46 : List Nat := sharedPrefix ++ suffix_46
theorem suffix_proof_46 : Word suffix_46 778868679974006316780233 5775912147024033660205 := by
  unfold suffix_46
  exact Word.cons
        (show ExactStep 778868679974006316780233 584151509980504737585175 2 from by
          refine ⟨by norm_num, ⟨389434339987003158390116, by norm_num⟩, by norm_num, ⟨292075754990252368792587, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 584151509980504737585175 876227264970757106377763 1 from by
          refine ⟨by norm_num, ⟨292075754990252368792587, by norm_num⟩, by norm_num, ⟨438113632485378553188881, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 876227264970757106377763 1314340897456135659566645 1 from by
          refine ⟨by norm_num, ⟨438113632485378553188881, by norm_num⟩, by norm_num, ⟨657170448728067829783322, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1314340897456135659566645 123219459136512718084373 5 from by
          refine ⟨by norm_num, ⟨657170448728067829783322, by norm_num⟩, by norm_num, ⟨61609729568256359042186, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 123219459136512718084373 5775912147024033660205 6 from by
          refine ⟨by norm_num, ⟨61609729568256359042186, by norm_num⟩, by norm_num, ⟨2887956073512016830102, by norm_num⟩⟩)
        (Word.nil 5775912147024033660205)))))
theorem full_word_46 : Word word_46 18465190817901402128411 5775912147024033660205 := by
  unfold word_46
  have hp := shared_prefix_all 32032
  have ht := suffix_proof_46
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_46 : word_46.length = 45 := by decide
theorem word_sum_46 : word_46.sum = 73 := by decide
theorem infinite_family_46 (d : Nat) :
    ∃ z : Nat, Word word_46 (18465190817901402128411 + 2^74*d) z ∧
      z < 18465190817901402128411 + 2^74*d := by
  have h := word_uniform_descent full_word_46
    (show 5775912147024033660205 < 18465190817901402128411 by norm_num)
    (show 3^word_46.length < 2^word_46.sum by norm_num [word_46, sharedPrefix, suffix_46]) d
  simpa [word_sum_46] using h

/-- Certificate 47; shared prefix plus independently witnessed suffix. -/
def suffix_47 : List Nat := [2, 1, 1, 5, 1, 6]
def word_47 : List Nat := sharedPrefix ++ suffix_47
theorem suffix_proof_47 : Word suffix_47 1065206016865715103901385 11848986607286168071657 := by
  unfold suffix_47
  exact Word.cons
        (show ExactStep 1065206016865715103901385 798904512649286327926039 2 from by
          refine ⟨by norm_num, ⟨532603008432857551950692, by norm_num⟩, by norm_num, ⟨399452256324643163963019, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 798904512649286327926039 1198356768973929491889059 1 from by
          refine ⟨by norm_num, ⟨399452256324643163963019, by norm_num⟩, by norm_num, ⟨599178384486964745944529, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1198356768973929491889059 1797535153460894237833589 1 from by
          refine ⟨by norm_num, ⟨599178384486964745944529, by norm_num⟩, by norm_num, ⟨898767576730447118916794, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1797535153460894237833589 168518920636958834796899 5 from by
          refine ⟨by norm_num, ⟨898767576730447118916794, by norm_num⟩, by norm_num, ⟨84259460318479417398449, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 168518920636958834796899 252778380955438252195349 1 from by
          refine ⟨by norm_num, ⟨84259460318479417398449, by norm_num⟩, by norm_num, ⟨126389190477719126097674, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 252778380955438252195349 11848986607286168071657 6 from by
          refine ⟨by norm_num, ⟨126389190477719126097674, by norm_num⟩, by norm_num, ⟨5924493303643084035828, by norm_num⟩⟩)
        (Word.nil 11848986607286168071657))))))
theorem full_word_47 : Word word_47 25253592637026517123099 11848986607286168071657 := by
  unfold word_47
  have hp := shared_prefix_all 43808
  have ht := suffix_proof_47
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_47 : word_47.length = 46 := by decide
theorem word_sum_47 : word_47.sum = 74 := by decide
theorem infinite_family_47 (d : Nat) :
    ∃ z : Nat, Word word_47 (25253592637026517123099 + 2^75*d) z ∧
      z < 25253592637026517123099 + 2^75*d := by
  have h := word_uniform_descent full_word_47
    (show 11848986607286168071657 < 25253592637026517123099 by norm_num)
    (show 3^word_47.length < 2^word_47.sum by norm_num [word_47, sharedPrefix, suffix_47]) d
  simpa [word_sum_47] using h

/-- Certificate 48; shared prefix plus independently witnessed suffix. -/
def suffix_48 : List Nat := [2, 1, 1, 5, 1, 5]
def word_48 : List Nat := sharedPrefix ++ suffix_48
theorem suffix_proof_48 : Word suffix_48 666823635103337660950217 14835035094919835047385 := by
  unfold suffix_48
  exact Word.cons
        (show ExactStep 666823635103337660950217 500117726327503245712663 2 from by
          refine ⟨by norm_num, ⟨333411817551668830475108, by norm_num⟩, by norm_num, ⟨250058863163751622856331, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 500117726327503245712663 750176589491254868568995 1 from by
          refine ⟨by norm_num, ⟨250058863163751622856331, by norm_num⟩, by norm_num, ⟨375088294745627434284497, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 750176589491254868568995 1125264884236882302853493 1 from by
          refine ⟨by norm_num, ⟨375088294745627434284497, by norm_num⟩, by norm_num, ⟨562632442118441151426746, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1125264884236882302853493 105493582897207715892515 5 from by
          refine ⟨by norm_num, ⟨562632442118441151426746, by norm_num⟩, by norm_num, ⟨52746791448603857946257, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 105493582897207715892515 158240374345811573838773 1 from by
          refine ⟨by norm_num, ⟨52746791448603857946257, by norm_num⟩, by norm_num, ⟨79120187172905786919386, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 158240374345811573838773 14835035094919835047385 5 from by
          refine ⟨by norm_num, ⟨79120187172905786919386, by norm_num⟩, by norm_num, ⟨7417517547459917523692, by norm_num⟩⟩)
        (Word.nil 14835035094919835047385))))))
theorem full_word_48 : Word word_48 15808859671287226695707 14835035094919835047385 := by
  unfold word_48
  have hp := shared_prefix_all 27424
  have ht := suffix_proof_48
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_48 : word_48.length = 46 := by decide
theorem word_sum_48 : word_48.sum = 73 := by decide
theorem infinite_family_48 (d : Nat) :
    ∃ z : Nat, Word word_48 (15808859671287226695707 + 2^74*d) z ∧
      z < 15808859671287226695707 + 2^74*d := by
  have h := word_uniform_descent full_word_48
    (show 14835035094919835047385 < 15808859671287226695707 by norm_num)
    (show 3^word_48.length < 2^word_48.sum by norm_num [word_48, sharedPrefix, suffix_48]) d
  simpa [word_sum_48] using h

/-- Certificate 49; shared prefix plus independently witnessed suffix. -/
def suffix_49 : List Nat := [2, 1, 1, 4, 2, 6]
def word_49 : List Nat := sharedPrefix ++ suffix_49
theorem suffix_proof_49 : Word suffix_49 153283846112772988395977 1705076962527641426707 := by
  unfold suffix_49
  exact Word.cons
        (show ExactStep 153283846112772988395977 114962884584579741296983 2 from by
          refine ⟨by norm_num, ⟨76641923056386494197988, by norm_num⟩, by norm_num, ⟨57481442292289870648491, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 114962884584579741296983 172444326876869611945475 1 from by
          refine ⟨by norm_num, ⟨57481442292289870648491, by norm_num⟩, by norm_num, ⟨86222163438434805972737, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 172444326876869611945475 258666490315304417918213 1 from by
          refine ⟨by norm_num, ⟨86222163438434805972737, by norm_num⟩, by norm_num, ⟨129333245157652208959106, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 258666490315304417918213 48499966934119578359665 4 from by
          refine ⟨by norm_num, ⟨129333245157652208959106, by norm_num⟩, by norm_num, ⟨24249983467059789179832, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 48499966934119578359665 36374975200589683769749 2 from by
          refine ⟨by norm_num, ⟨24249983467059789179832, by norm_num⟩, by norm_num, ⟨18187487600294841884874, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 36374975200589683769749 1705076962527641426707 6 from by
          refine ⟨by norm_num, ⟨18187487600294841884874, by norm_num⟩, by norm_num, ⟨852538481263820713353, by norm_num⟩⟩)
        (Word.nil 1705076962527641426707))))))
theorem full_word_49 : Word word_49 3634008582638922629147 1705076962527641426707 := by
  unfold word_49
  have hp := shared_prefix_all 6304
  have ht := suffix_proof_49
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_49 : word_49.length = 46 := by decide
theorem word_sum_49 : word_49.sum = 74 := by decide
theorem infinite_family_49 (d : Nat) :
    ∃ z : Nat, Word word_49 (3634008582638922629147 + 2^75*d) z ∧
      z < 3634008582638922629147 + 2^75*d := by
  have h := word_uniform_descent full_word_49
    (show 1705076962527641426707 < 3634008582638922629147 by norm_num)
    (show 3^word_49.length < 2^word_49.sum by norm_num [word_49, sharedPrefix, suffix_49]) d
  simpa [word_sum_49] using h

/-- Certificate 50; shared prefix plus independently witnessed suffix. -/
def suffix_50 : List Nat := [2, 1, 1, 4, 2, 5]
def word_50 : List Nat := sharedPrefix ++ suffix_50
theorem suffix_proof_50 : Word suffix_50 551666227875150431347145 12273092044707783949343 := by
  unfold suffix_50
  exact Word.cons
        (show ExactStep 551666227875150431347145 413749670906362823510359 2 from by
          refine ⟨by norm_num, ⟨275833113937575215673572, by norm_num⟩, by norm_num, ⟨206874835453181411755179, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 413749670906362823510359 620624506359544235265539 1 from by
          refine ⟨by norm_num, ⟨206874835453181411755179, by norm_num⟩, by norm_num, ⟨310312253179772117632769, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 620624506359544235265539 930936759539316352898309 1 from by
          refine ⟨by norm_num, ⟨310312253179772117632769, by norm_num⟩, by norm_num, ⟨465468379769658176449154, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 930936759539316352898309 174550642413621816168433 4 from by
          refine ⟨by norm_num, ⟨465468379769658176449154, by norm_num⟩, by norm_num, ⟨87275321206810908084216, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 174550642413621816168433 130912981810216362126325 2 from by
          refine ⟨by norm_num, ⟨87275321206810908084216, by norm_num⟩, by norm_num, ⟨65456490905108181063162, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 130912981810216362126325 12273092044707783949343 5 from by
          refine ⟨by norm_num, ⟨65456490905108181063162, by norm_num⟩, by norm_num, ⟨6136546022353891974671, by norm_num⟩⟩)
        (Word.nil 12273092044707783949343))))))
theorem full_word_50 : Word word_50 13078741548378213056539 12273092044707783949343 := by
  unfold word_50
  have hp := shared_prefix_all 22688
  have ht := suffix_proof_50
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_50 : word_50.length = 46 := by decide
theorem word_sum_50 : word_50.sum = 73 := by decide
theorem infinite_family_50 (d : Nat) :
    ∃ z : Nat, Word word_50 (13078741548378213056539 + 2^74*d) z ∧
      z < 13078741548378213056539 + 2^74*d := by
  have h := word_uniform_descent full_word_50
    (show 12273092044707783949343 < 13078741548378213056539 by norm_num)
    (show 3^word_50.length < 2^word_50.sum by norm_num [word_50, sharedPrefix, suffix_50]) d
  simpa [word_sum_50] using h

/-- Certificate 51; shared prefix plus independently witnessed suffix. -/
def suffix_51 : List Nat := [2, 1, 1, 4, 4, 3]
def word_51 : List Nat := sharedPrefix ++ suffix_51
theorem suffix_proof_51 : Word suffix_51 215531093263144463857097 4794988006250986149653 := by
  unfold suffix_51
  exact Word.cons
        (show ExactStep 215531093263144463857097 161648319947358347892823 2 from by
          refine ⟨by norm_num, ⟨107765546631572231928548, by norm_num⟩, by norm_num, ⟨80824159973679173946411, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 161648319947358347892823 242472479921037521839235 1 from by
          refine ⟨by norm_num, ⟨80824159973679173946411, by norm_num⟩, by norm_num, ⟨121236239960518760919617, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 242472479921037521839235 363708719881556282758853 1 from by
          refine ⟨by norm_num, ⟨121236239960518760919617, by norm_num⟩, by norm_num, ⟨181854359940778141379426, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 363708719881556282758853 68195384977791803017285 4 from by
          refine ⟨by norm_num, ⟨181854359940778141379426, by norm_num⟩, by norm_num, ⟨34097692488895901508642, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 68195384977791803017285 12786634683335963065741 4 from by
          refine ⟨by norm_num, ⟨34097692488895901508642, by norm_num⟩, by norm_num, ⟨6393317341667981532870, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 12786634683335963065741 4794988006250986149653 3 from by
          refine ⟨by norm_num, ⟨6393317341667981532870, by norm_num⟩, by norm_num, ⟨2397494003125493074826, by norm_num⟩⟩)
        (Word.nil 4794988006250986149653))))))
theorem full_word_51 : Word word_51 5109748108535686758427 4794988006250986149653 := by
  unfold word_51
  have hp := shared_prefix_all 8864
  have ht := suffix_proof_51
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_51 : word_51.length = 46 := by decide
theorem word_sum_51 : word_51.sum = 73 := by decide
theorem infinite_family_51 (d : Nat) :
    ∃ z : Nat, Word word_51 (5109748108535686758427 + 2^74*d) z ∧
      z < 5109748108535686758427 + 2^74*d := by
  have h := word_uniform_descent full_word_51
    (show 4794988006250986149653 < 5109748108535686758427 by norm_num)
    (show 3^word_51.length < 2^word_51.sum by norm_num [word_51, sharedPrefix, suffix_51]) d
  simpa [word_sum_51] using h

/-- Certificate 52; shared prefix plus independently witnessed suffix. -/
def suffix_52 : List Nat := [2, 1, 1, 4, 4, 4]
def word_52 : List Nat := sharedPrefix ++ suffix_52
theorem suffix_proof_52 : Word suffix_52 613913475025521906808265 6828963062951743622791 := by
  unfold suffix_52
  exact Word.cons
        (show ExactStep 613913475025521906808265 460435106269141430106199 2 from by
          refine ⟨by norm_num, ⟨306956737512760953404132, by norm_num⟩, by norm_num, ⟨230217553134570715053099, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 460435106269141430106199 690652659403712145159299 1 from by
          refine ⟨by norm_num, ⟨230217553134570715053099, by norm_num⟩, by norm_num, ⟨345326329701856072579649, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 690652659403712145159299 1035978989105568217738949 1 from by
          refine ⟨by norm_num, ⟨345326329701856072579649, by norm_num⟩, by norm_num, ⟨517989494552784108869474, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1035978989105568217738949 194246060457294040826053 4 from by
          refine ⟨by norm_num, ⟨517989494552784108869474, by norm_num⟩, by norm_num, ⟨97123030228647020413026, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 194246060457294040826053 36421136335742632654885 4 from by
          refine ⟨by norm_num, ⟨97123030228647020413026, by norm_num⟩, by norm_num, ⟨18210568167871316327442, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 36421136335742632654885 6828963062951743622791 4 from by
          refine ⟨by norm_num, ⟨18210568167871316327442, by norm_num⟩, by norm_num, ⟨3414481531475871811395, by norm_num⟩⟩)
        (Word.nil 6828963062951743622791))))))
theorem full_word_52 : Word word_52 14554481074274977185819 6828963062951743622791 := by
  unfold word_52
  have hp := shared_prefix_all 25248
  have ht := suffix_proof_52
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_52 : word_52.length = 46 := by decide
theorem word_sum_52 : word_52.sum = 74 := by decide
theorem infinite_family_52 (d : Nat) :
    ∃ z : Nat, Word word_52 (14554481074274977185819 + 2^75*d) z ∧
      z < 14554481074274977185819 + 2^75*d := by
  have h := word_uniform_descent full_word_52
    (show 6828963062951743622791 < 14554481074274977185819 by norm_num)
    (show 3^word_52.length < 2^word_52.sum by norm_num [word_52, sharedPrefix, suffix_52]) d
  simpa [word_sum_52] using h

/-- Certificate 53; shared prefix plus independently witnessed suffix. -/
def suffix_53 : List Nat := [2, 1, 1, 4, 6]
def word_53 : List Nat := sharedPrefix ++ suffix_53
theorem suffix_proof_53 : Word suffix_53 66137700102252922750409 980924140920865492453 := by
  unfold suffix_53
  exact Word.cons
        (show ExactStep 66137700102252922750409 49603275076689692062807 2 from by
          refine ⟨by norm_num, ⟨33068850051126461375204, by norm_num⟩, by norm_num, ⟨24801637538344846031403, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 49603275076689692062807 74404912615034538094211 1 from by
          refine ⟨by norm_num, ⟨24801637538344846031403, by norm_num⟩, by norm_num, ⟨37202456307517269047105, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 74404912615034538094211 111607368922551807141317 1 from by
          refine ⟨by norm_num, ⟨37202456307517269047105, by norm_num⟩, by norm_num, ⟨55803684461275903570658, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 111607368922551807141317 20926381672978463838997 4 from by
          refine ⟨by norm_num, ⟨55803684461275903570658, by norm_num⟩, by norm_num, ⟨10463190836489231919498, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 20926381672978463838997 980924140920865492453 6 from by
          refine ⟨by norm_num, ⟨10463190836489231919498, by norm_num⟩, by norm_num, ⟨490462070460432746226, by norm_num⟩⟩)
        (Word.nil 980924140920865492453)))))
theorem full_word_53 : Word word_53 1567973246383452848155 980924140920865492453 := by
  unfold word_53
  have hp := shared_prefix_all 2720
  have ht := suffix_proof_53
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_53 : word_53.length = 45 := by decide
theorem word_sum_53 : word_53.sum = 72 := by decide
theorem infinite_family_53 (d : Nat) :
    ∃ z : Nat, Word word_53 (1567973246383452848155 + 2^73*d) z ∧
      z < 1567973246383452848155 + 2^73*d := by
  have h := word_uniform_descent full_word_53
    (show 980924140920865492453 < 1567973246383452848155 by norm_num)
    (show 3^word_53.length < 2^word_53.sum by norm_num [word_53, sharedPrefix, suffix_53]) d
  simpa [word_sum_53] using h

/-- Certificate 54; shared prefix plus independently witnessed suffix. -/
def suffix_54 : List Nat := [2, 1, 1, 4, 8]
def word_54 : List Nat := sharedPrefix ++ suffix_54
theorem suffix_proof_54 : Word suffix_54 1062093654508196530128329 3938121918418758496417 := by
  unfold suffix_54
  exact Word.cons
        (show ExactStep 1062093654508196530128329 796570240881147397596247 2 from by
          refine ⟨by norm_num, ⟨531046827254098265064164, by norm_num⟩, by norm_num, ⟨398285120440573698798123, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 796570240881147397596247 1194855361321721096394371 1 from by
          refine ⟨by norm_num, ⟨398285120440573698798123, by norm_num⟩, by norm_num, ⟨597427680660860548197185, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1194855361321721096394371 1792283041982581644591557 1 from by
          refine ⟨by norm_num, ⟨597427680660860548197185, by norm_num⟩, by norm_num, ⟨896141520991290822295778, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1792283041982581644591557 336053070371734058360917 4 from by
          refine ⟨by norm_num, ⟨896141520991290822295778, by norm_num⟩, by norm_num, ⟨168026535185867029180458, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 336053070371734058360917 3938121918418758496417 8 from by
          refine ⟨by norm_num, ⟨168026535185867029180458, by norm_num⟩, by norm_num, ⟨1969060959209379248208, by norm_num⟩⟩)
        (Word.nil 3938121918418758496417)))))
theorem full_word_54 : Word word_54 25179805660731678916635 3938121918418758496417 := by
  unfold word_54
  have hp := shared_prefix_all 43680
  have ht := suffix_proof_54
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_54 : word_54.length = 45 := by decide
theorem word_sum_54 : word_54.sum = 74 := by decide
theorem infinite_family_54 (d : Nat) :
    ∃ z : Nat, Word word_54 (25179805660731678916635 + 2^75*d) z ∧
      z < 25179805660731678916635 + 2^75*d := by
  have h := word_uniform_descent full_word_54
    (show 3938121918418758496417 < 25179805660731678916635 by norm_num)
    (show 3^word_54.length < 2^word_54.sum by norm_num [word_54, sharedPrefix, suffix_54]) d
  simpa [word_sum_54] using h

/-- Certificate 55; shared prefix plus independently witnessed suffix. -/
def suffix_55 : List Nat := [2, 1, 1, 4, 7]
def word_55 : List Nat := sharedPrefix ++ suffix_55
theorem suffix_proof_55 : Word suffix_55 663711272745819087177161 4921931130286683294191 := by
  unfold suffix_55
  exact Word.cons
        (show ExactStep 663711272745819087177161 497783454559364315382871 2 from by
          refine ⟨by norm_num, ⟨331855636372909543588580, by norm_num⟩, by norm_num, ⟨248891727279682157691435, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 497783454559364315382871 746675181839046473074307 1 from by
          refine ⟨by norm_num, ⟨248891727279682157691435, by norm_num⟩, by norm_num, ⟨373337590919523236537153, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 746675181839046473074307 1120012772758569709611461 1 from by
          refine ⟨by norm_num, ⟨373337590919523236537153, by norm_num⟩, by norm_num, ⟨560006386379284854805730, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1120012772758569709611461 210002394892231820552149 4 from by
          refine ⟨by norm_num, ⟨560006386379284854805730, by norm_num⟩, by norm_num, ⟨105001197446115910276074, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 210002394892231820552149 4921931130286683294191 7 from by
          refine ⟨by norm_num, ⟨105001197446115910276074, by norm_num⟩, by norm_num, ⟨2460965565143341647095, by norm_num⟩⟩)
        (Word.nil 4921931130286683294191)))))
theorem full_word_55 : Word word_55 15735072694992388489243 4921931130286683294191 := by
  unfold word_55
  have hp := shared_prefix_all 27296
  have ht := suffix_proof_55
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_55 : word_55.length = 45 := by decide
theorem word_sum_55 : word_55.sum = 73 := by decide
theorem infinite_family_55 (d : Nat) :
    ∃ z : Nat, Word word_55 (15735072694992388489243 + 2^74*d) z ∧
      z < 15735072694992388489243 + 2^74*d := by
  have h := word_uniform_descent full_word_55
    (show 4921931130286683294191 < 15735072694992388489243 by norm_num)
    (show 3^word_55.length < 2^word_55.sum by norm_num [word_55, sharedPrefix, suffix_55]) d
  simpa [word_sum_55] using h

/-- Certificate 56; shared prefix plus independently witnessed suffix. -/
def suffix_56 : List Nat := [2, 1, 1, 4, 5, 3]
def word_56 : List Nat := sharedPrefix ++ suffix_56
theorem suffix_proof_56 : Word suffix_56 165733295542847283488201 1843560370647211756331 := by
  unfold suffix_56
  exact Word.cons
        (show ExactStep 165733295542847283488201 124299971657135462616151 2 from by
          refine ⟨by norm_num, ⟨82866647771423641744100, by norm_num⟩, by norm_num, ⟨62149985828567731308075, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 124299971657135462616151 186449957485703193924227 1 from by
          refine ⟨by norm_num, ⟨62149985828567731308075, by norm_num⟩, by norm_num, ⟨93224978742851596962113, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 186449957485703193924227 279674936228554790886341 1 from by
          refine ⟨by norm_num, ⟨93224978742851596962113, by norm_num⟩, by norm_num, ⟨139837468114277395443170, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 279674936228554790886341 52439050542854023291189 4 from by
          refine ⟨by norm_num, ⟨139837468114277395443170, by norm_num⟩, by norm_num, ⟨26219525271427011645594, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 52439050542854023291189 4916160988392564683549 5 from by
          refine ⟨by norm_num, ⟨26219525271427011645594, by norm_num⟩, by norm_num, ⟨2458080494196282341774, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 4916160988392564683549 1843560370647211756331 3 from by
          refine ⟨by norm_num, ⟨2458080494196282341774, by norm_num⟩, by norm_num, ⟨921780185323605878165, by norm_num⟩⟩)
        (Word.nil 1843560370647211756331))))))
theorem full_word_56 : Word word_56 3929156487818275455003 1843560370647211756331 := by
  unfold word_56
  have hp := shared_prefix_all 6816
  have ht := suffix_proof_56
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_56 : word_56.length = 46 := by decide
theorem word_sum_56 : word_56.sum = 74 := by decide
theorem infinite_family_56 (d : Nat) :
    ∃ z : Nat, Word word_56 (3929156487818275455003 + 2^75*d) z ∧
      z < 3929156487818275455003 + 2^75*d := by
  have h := word_uniform_descent full_word_56
    (show 1843560370647211756331 < 3929156487818275455003 by norm_num)
    (show 3^word_56.length < 2^word_56.sum by norm_num [word_56, sharedPrefix, suffix_56]) d
  simpa [word_sum_56] using h

/-- Certificate 57; shared prefix plus independently witnessed suffix. -/
def suffix_57 : List Nat := [2, 1, 1, 4, 5, 2]
def word_57 : List Nat := sharedPrefix ++ suffix_57
theorem suffix_proof_57 : Word suffix_57 564115677305224726439369 12550058860946924608591 := by
  unfold suffix_57
  exact Word.cons
        (show ExactStep 564115677305224726439369 423086757978918544829527 2 from by
          refine ⟨by norm_num, ⟨282057838652612363219684, by norm_num⟩, by norm_num, ⟨211543378989459272414763, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 423086757978918544829527 634630136968377817244291 1 from by
          refine ⟨by norm_num, ⟨211543378989459272414763, by norm_num⟩, by norm_num, ⟨317315068484188908622145, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 634630136968377817244291 951945205452566725866437 1 from by
          refine ⟨by norm_num, ⟨317315068484188908622145, by norm_num⟩, by norm_num, ⟨475972602726283362933218, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 951945205452566725866437 178489726022356261099957 4 from by
          refine ⟨by norm_num, ⟨475972602726283362933218, by norm_num⟩, by norm_num, ⟨89244863011178130549978, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 178489726022356261099957 16733411814595899478121 5 from by
          refine ⟨by norm_num, ⟨89244863011178130549978, by norm_num⟩, by norm_num, ⟨8366705907297949739060, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 16733411814595899478121 12550058860946924608591 2 from by
          refine ⟨by norm_num, ⟨8366705907297949739060, by norm_num⟩, by norm_num, ⟨6275029430473462304295, by norm_num⟩⟩)
        (Word.nil 12550058860946924608591))))))
theorem full_word_57 : Word word_57 13373889453557565882395 12550058860946924608591 := by
  unfold word_57
  have hp := shared_prefix_all 23200
  have ht := suffix_proof_57
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_57 : word_57.length = 46 := by decide
theorem word_sum_57 : word_57.sum = 73 := by decide
theorem infinite_family_57 (d : Nat) :
    ∃ z : Nat, Word word_57 (13373889453557565882395 + 2^74*d) z ∧
      z < 13373889453557565882395 + 2^74*d := by
  have h := word_uniform_descent full_word_57
    (show 12550058860946924608591 < 13373889453557565882395 by norm_num)
    (show 3^word_57.length < 2^word_57.sum by norm_num [word_57, sharedPrefix, suffix_57]) d
  simpa [word_sum_57] using h

/-- Certificate 58; shared prefix plus independently witnessed suffix. -/
def suffix_58 : List Nat := [2, 1, 1, 4, 3, 5]
def word_58 : List Nat := sharedPrefix ++ suffix_58
theorem suffix_proof_58 : Word suffix_58 838003564766859218468297 9321664409104009556021 := by
  unfold suffix_58
  exact Word.cons
        (show ExactStep 838003564766859218468297 628502673575144413851223 2 from by
          refine ⟨by norm_num, ⟨419001782383429609234148, by norm_num⟩, by norm_num, ⟨314251336787572206925611, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 628502673575144413851223 942754010362716620776835 1 from by
          refine ⟨by norm_num, ⟨314251336787572206925611, by norm_num⟩, by norm_num, ⟨471377005181358310388417, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 942754010362716620776835 1414131015544074931165253 1 from by
          refine ⟨by norm_num, ⟨471377005181358310388417, by norm_num⟩, by norm_num, ⟨707065507772037465582626, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1414131015544074931165253 265149565414514049593485 4 from by
          refine ⟨by norm_num, ⟨707065507772037465582626, by norm_num⟩, by norm_num, ⟨132574782707257024796742, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 265149565414514049593485 99431087030442768597557 3 from by
          refine ⟨by norm_num, ⟨132574782707257024796742, by norm_num⟩, by norm_num, ⟨49715543515221384298778, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 99431087030442768597557 9321664409104009556021 5 from by
          refine ⟨by norm_num, ⟨49715543515221384298778, by norm_num⟩, by norm_num, ⟨4660832204552004778010, by norm_num⟩⟩)
        (Word.nil 9321664409104009556021))))))
theorem full_word_58 : Word word_58 19867143367503328051227 9321664409104009556021 := by
  unfold word_58
  have hp := shared_prefix_all 34464
  have ht := suffix_proof_58
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_58 : word_58.length = 46 := by decide
theorem word_sum_58 : word_58.sum = 74 := by decide
theorem infinite_family_58 (d : Nat) :
    ∃ z : Nat, Word word_58 (19867143367503328051227 + 2^75*d) z ∧
      z < 19867143367503328051227 + 2^75*d := by
  have h := word_uniform_descent full_word_58
    (show 9321664409104009556021 < 19867143367503328051227 by norm_num)
    (show 3^word_58.length < 2^word_58.sum by norm_num [word_58, sharedPrefix, suffix_58]) d
  simpa [word_sum_58] using h

/-- Certificate 59; shared prefix plus independently witnessed suffix. -/
def suffix_59 : List Nat := [2, 1, 1, 4, 3, 4]
def word_59 : List Nat := sharedPrefix ++ suffix_59
theorem suffix_proof_59 : Word suffix_59 439621183004481775517129 9780390698555518016113 := by
  unfold suffix_59
  exact Word.cons
        (show ExactStep 439621183004481775517129 329715887253361331637847 2 from by
          refine ⟨by norm_num, ⟨219810591502240887758564, by norm_num⟩, by norm_num, ⟨164857943626680665818923, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 329715887253361331637847 494573830880041997456771 1 from by
          refine ⟨by norm_num, ⟨164857943626680665818923, by norm_num⟩, by norm_num, ⟨247286915440020998728385, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 494573830880041997456771 741860746320062996185157 1 from by
          refine ⟨by norm_num, ⟨247286915440020998728385, by norm_num⟩, by norm_num, ⟨370930373160031498092578, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 741860746320062996185157 139098889935011811784717 4 from by
          refine ⟨by norm_num, ⟨370930373160031498092578, by norm_num⟩, by norm_num, ⟨69549444967505905892358, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 139098889935011811784717 52162083725629429419269 3 from by
          refine ⟨by norm_num, ⟨69549444967505905892358, by norm_num⟩, by norm_num, ⟨26081041862814714709634, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 52162083725629429419269 9780390698555518016113 4 from by
          refine ⟨by norm_num, ⟨26081041862814714709634, by norm_num⟩, by norm_num, ⟨4890195349277759008056, by norm_num⟩⟩)
        (Word.nil 9780390698555518016113))))))
theorem full_word_59 : Word word_59 10422410401764037623835 9780390698555518016113 := by
  unfold word_59
  have hp := shared_prefix_all 18080
  have ht := suffix_proof_59
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_59 : word_59.length = 46 := by decide
theorem word_sum_59 : word_59.sum = 73 := by decide
theorem infinite_family_59 (d : Nat) :
    ∃ z : Nat, Word word_59 (10422410401764037623835 + 2^74*d) z ∧
      z < 10422410401764037623835 + 2^74*d := by
  have h := word_uniform_descent full_word_59
    (show 9780390698555518016113 < 10422410401764037623835 by norm_num)
    (show 3^word_59.length < 2^word_59.sum by norm_num [word_59, sharedPrefix, suffix_59]) d
  simpa [word_sum_59] using h

/-- Certificate 60; shared prefix plus independently witnessed suffix. -/
def suffix_60 : List Nat := [2, 1, 1, 4, 1, 6]
def word_60 : List Nat := sharedPrefix ++ suffix_60
theorem suffix_proof_60 : Word suffix_60 209306368548107316310985 4656504598131415820029 := by
  unfold suffix_60
  exact Word.cons
        (show ExactStep 209306368548107316310985 156979776411080487233239 2 from by
          refine ⟨by norm_num, ⟨104653184274053658155492, by norm_num⟩, by norm_num, ⟨78489888205540243616619, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 156979776411080487233239 235469664616620730849859 1 from by
          refine ⟨by norm_num, ⟨78489888205540243616619, by norm_num⟩, by norm_num, ⟨117734832308310365424929, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 235469664616620730849859 353204496924931096274789 1 from by
          refine ⟨by norm_num, ⟨117734832308310365424929, by norm_num⟩, by norm_num, ⟨176602248462465548137394, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 353204496924931096274789 66225843173424580551523 4 from by
          refine ⟨by norm_num, ⟨176602248462465548137394, by norm_num⟩, by norm_num, ⟨33112921586712290275761, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 66225843173424580551523 99338764760136870827285 1 from by
          refine ⟨by norm_num, ⟨33112921586712290275761, by norm_num⟩, by norm_num, ⟨49669382380068435413642, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 99338764760136870827285 4656504598131415820029 6 from by
          refine ⟨by norm_num, ⟨49669382380068435413642, by norm_num⟩, by norm_num, ⟨2328252299065707910014, by norm_num⟩⟩)
        (Word.nil 4656504598131415820029))))))
theorem full_word_60 : Word word_60 4962174155946010345499 4656504598131415820029 := by
  unfold word_60
  have hp := shared_prefix_all 8608
  have ht := suffix_proof_60
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_60 : word_60.length = 46 := by decide
theorem word_sum_60 : word_60.sum = 73 := by decide
theorem infinite_family_60 (d : Nat) :
    ∃ z : Nat, Word word_60 (4962174155946010345499 + 2^74*d) z ∧
      z < 4962174155946010345499 + 2^74*d := by
  have h := word_uniform_descent full_word_60
    (show 4656504598131415820029 < 4962174155946010345499 by norm_num)
    (show 3^word_60.length < 2^word_60.sum by norm_num [word_60, sharedPrefix, suffix_60]) d
  simpa [word_sum_60] using h

/-- Certificate 61; shared prefix plus independently witnessed suffix. -/
def suffix_61 : List Nat := [2, 1, 1, 4, 1, 7]
def word_61 : List Nat := sharedPrefix ++ suffix_61
theorem suffix_proof_61 : Word suffix_61 607688750310484759262153 6759721358891958457979 := by
  unfold suffix_61
  exact Word.cons
        (show ExactStep 607688750310484759262153 455766562732863569446615 2 from by
          refine ⟨by norm_num, ⟨303844375155242379631076, by norm_num⟩, by norm_num, ⟨227883281366431784723307, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 455766562732863569446615 683649844099295354169923 1 from by
          refine ⟨by norm_num, ⟨227883281366431784723307, by norm_num⟩, by norm_num, ⟨341824922049647677084961, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 683649844099295354169923 1025474766148943031254885 1 from by
          refine ⟨by norm_num, ⟨341824922049647677084961, by norm_num⟩, by norm_num, ⟨512737383074471515627442, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1025474766148943031254885 192276518652926818360291 4 from by
          refine ⟨by norm_num, ⟨512737383074471515627442, by norm_num⟩, by norm_num, ⟨96138259326463409180145, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 192276518652926818360291 288414777979390227540437 1 from by
          refine ⟨by norm_num, ⟨96138259326463409180145, by norm_num⟩, by norm_num, ⟨144207388989695113770218, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 288414777979390227540437 6759721358891958457979 7 from by
          refine ⟨by norm_num, ⟨144207388989695113770218, by norm_num⟩, by norm_num, ⟨3379860679445979228989, by norm_num⟩⟩)
        (Word.nil 6759721358891958457979))))))
theorem full_word_61 : Word word_61 14406907121685300772891 6759721358891958457979 := by
  unfold word_61
  have hp := shared_prefix_all 24992
  have ht := suffix_proof_61
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_61 : word_61.length = 46 := by decide
theorem word_sum_61 : word_61.sum = 74 := by decide
theorem infinite_family_61 (d : Nat) :
    ∃ z : Nat, Word word_61 (14406907121685300772891 + 2^75*d) z ∧
      z < 14406907121685300772891 + 2^75*d := by
  have h := word_uniform_descent full_word_61
    (show 6759721358891958457979 < 14406907121685300772891 by norm_num)
    (show 3^word_61.length < 2^word_61.sum by norm_num [word_61, sharedPrefix, suffix_61]) d
  simpa [word_sum_61] using h

/-- Certificate 62; shared prefix plus independently witnessed suffix. -/
def suffix_62 : List Nat := [2, 1, 1, 3, 2, 7]
def word_62 : List Nat := sharedPrefix ++ suffix_62
theorem suffix_proof_62 : Word suffix_62 948492428458768587411785 10550704656165196231433 := by
  unfold suffix_62
  exact Word.cons
        (show ExactStep 948492428458768587411785 711369321344076440558839 2 from by
          refine ⟨by norm_num, ⟨474246214229384293705892, by norm_num⟩, by norm_num, ⟨355684660672038220279419, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 711369321344076440558839 1067053982016114660838259 1 from by
          refine ⟨by norm_num, ⟨355684660672038220279419, by norm_num⟩, by norm_num, ⟨533526991008057330419129, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1067053982016114660838259 1600580973024171991257389 1 from by
          refine ⟨by norm_num, ⟨533526991008057330419129, by norm_num⟩, by norm_num, ⟨800290486512085995628694, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1600580973024171991257389 600217864884064496721521 3 from by
          refine ⟨by norm_num, ⟨800290486512085995628694, by norm_num⟩, by norm_num, ⟨300108932442032248360760, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 600217864884064496721521 450163398663048372541141 2 from by
          refine ⟨by norm_num, ⟨300108932442032248360760, by norm_num⟩, by norm_num, ⟨225081699331524186270570, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 450163398663048372541141 10550704656165196231433 7 from by
          refine ⟨by norm_num, ⟨225081699331524186270570, by norm_num⟩, by norm_num, ⟨5275352328082598115716, by norm_num⟩⟩)
        (Word.nil 10550704656165196231433))))))
theorem full_word_62 : Word word_62 22486581025970084380699 10550704656165196231433 := by
  unfold word_62
  have hp := shared_prefix_all 39008
  have ht := suffix_proof_62
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_62 : word_62.length = 46 := by decide
theorem word_sum_62 : word_62.sum = 74 := by decide
theorem infinite_family_62 (d : Nat) :
    ∃ z : Nat, Word word_62 (22486581025970084380699 + 2^75*d) z ∧
      z < 22486581025970084380699 + 2^75*d := by
  have h := word_uniform_descent full_word_62
    (show 10550704656165196231433 < 22486581025970084380699 by norm_num)
    (show 3^word_62.length < 2^word_62.sum by norm_num [word_62, sharedPrefix, suffix_62]) d
  simpa [word_sum_62] using h

/-- Certificate 63; shared prefix plus independently witnessed suffix. -/
def suffix_63 : List Nat := [2, 1, 1, 3, 2, 6]
def word_63 : List Nat := sharedPrefix ++ suffix_63
theorem suffix_proof_63 : Word suffix_63 550110046696391144460617 12238471192677891366937 := by
  unfold suffix_63
  exact Word.cons
        (show ExactStep 550110046696391144460617 412582535022293358345463 2 from by
          refine ⟨by norm_num, ⟨275055023348195572230308, by norm_num⟩, by norm_num, ⟨206291267511146679172731, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 412582535022293358345463 618873802533440037518195 1 from by
          refine ⟨by norm_num, ⟨206291267511146679172731, by norm_num⟩, by norm_num, ⟨309436901266720018759097, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 618873802533440037518195 928310703800160056277293 1 from by
          refine ⟨by norm_num, ⟨309436901266720018759097, by norm_num⟩, by norm_num, ⟨464155351900080028138646, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 928310703800160056277293 348116513925060021103985 3 from by
          refine ⟨by norm_num, ⟨464155351900080028138646, by norm_num⟩, by norm_num, ⟨174058256962530010551992, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 348116513925060021103985 261087385443795015827989 2 from by
          refine ⟨by norm_num, ⟨174058256962530010551992, by norm_num⟩, by norm_num, ⟨130543692721897507913994, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 261087385443795015827989 12238471192677891366937 6 from by
          refine ⟨by norm_num, ⟨130543692721897507913994, by norm_num⟩, by norm_num, ⟨6119235596338945683468, by norm_num⟩⟩)
        (Word.nil 12238471192677891366937))))))
theorem full_word_63 : Word word_63 13041848060230793953307 12238471192677891366937 := by
  unfold word_63
  have hp := shared_prefix_all 22624
  have ht := suffix_proof_63
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_63 : word_63.length = 46 := by decide
theorem word_sum_63 : word_63.sum = 73 := by decide
theorem infinite_family_63 (d : Nat) :
    ∃ z : Nat, Word word_63 (13041848060230793953307 + 2^74*d) z ∧
      z < 13041848060230793953307 + 2^74*d := by
  have h := word_uniform_descent full_word_63
    (show 12238471192677891366937 < 13041848060230793953307 by norm_num)
    (show 3^word_63.length < 2^word_63.sum by norm_num [word_63, sharedPrefix, suffix_63]) d
  simpa [word_sum_63] using h

/-- Certificate 64; shared prefix plus independently witnessed suffix. -/
def suffix_64 : List Nat := [2, 1, 1, 3, 7]
def word_64 : List Nat := sharedPrefix ++ suffix_64
theorem suffix_proof_64 : Word suffix_64 8558996488159307948873 126943124183515126439 := by
  unfold suffix_64
  exact Word.cons
        (show ExactStep 8558996488159307948873 6419247366119480961655 2 from by
          refine ⟨by norm_num, ⟨4279498244079653974436, by norm_num⟩, by norm_num, ⟨3209623683059740480827, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 6419247366119480961655 9628871049179221442483 1 from by
          refine ⟨by norm_num, ⟨3209623683059740480827, by norm_num⟩, by norm_num, ⟨4814435524589610721241, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 9628871049179221442483 14443306573768832163725 1 from by
          refine ⟨by norm_num, ⟨4814435524589610721241, by norm_num⟩, by norm_num, ⟨7221653286884416081862, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 14443306573768832163725 5416239965163312061397 3 from by
          refine ⟨by norm_num, ⟨7221653286884416081862, by norm_num⟩, by norm_num, ⟨2708119982581656030698, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 5416239965163312061397 126943124183515126439 7 from by
          refine ⟨by norm_num, ⟨2708119982581656030698, by norm_num⟩, by norm_num, ⟨63471562091757563219, by norm_num⟩⟩)
        (Word.nil 126943124183515126439)))))
theorem full_word_64 : Word word_64 202914184928946028571 126943124183515126439 := by
  unfold word_64
  have hp := shared_prefix_all 352
  have ht := suffix_proof_64
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_64 : word_64.length = 45 := by decide
theorem word_sum_64 : word_64.sum = 72 := by decide
theorem infinite_family_64 (d : Nat) :
    ∃ z : Nat, Word word_64 (202914184928946028571 + 2^73*d) z ∧
      z < 202914184928946028571 + 2^73*d := by
  have h := word_uniform_descent full_word_64
    (show 126943124183515126439 < 202914184928946028571 by norm_num)
    (show 3^word_64.length < 2^word_64.sum by norm_num [word_64, sharedPrefix, suffix_64]) d
  simpa [word_sum_64] using h

/-- Certificate 65; shared prefix plus independently witnessed suffix. -/
def suffix_65 : List Nat := [2, 1, 1, 3, 8]
def word_65 : List Nat := sharedPrefix ++ suffix_65
theorem suffix_proof_65 : Word suffix_65 207750187369348029424457 1540627915367174412541 := by
  unfold suffix_65
  exact Word.cons
        (show ExactStep 207750187369348029424457 155812640527011022068343 2 from by
          refine ⟨by norm_num, ⟨103875093684674014712228, by norm_num⟩, by norm_num, ⟨77906320263505511034171, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 155812640527011022068343 233718960790516533102515 1 from by
          refine ⟨by norm_num, ⟨77906320263505511034171, by norm_num⟩, by norm_num, ⟨116859480395258266551257, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 233718960790516533102515 350578441185774799653773 1 from by
          refine ⟨by norm_num, ⟨116859480395258266551257, by norm_num⟩, by norm_num, ⟨175289220592887399826886, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 350578441185774799653773 131466915444665549870165 3 from by
          refine ⟨by norm_num, ⟨175289220592887399826886, by norm_num⟩, by norm_num, ⟨65733457722332774935082, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 131466915444665549870165 1540627915367174412541 8 from by
          refine ⟨by norm_num, ⟨65733457722332774935082, by norm_num⟩, by norm_num, ⟨770313957683587206270, by norm_num⟩⟩)
        (Word.nil 1540627915367174412541)))))
theorem full_word_65 : Word word_65 4925280667798591242267 1540627915367174412541 := by
  unfold word_65
  have hp := shared_prefix_all 8544
  have ht := suffix_proof_65
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_65 : word_65.length = 45 := by decide
theorem word_sum_65 : word_65.sum = 73 := by decide
theorem infinite_family_65 (d : Nat) :
    ∃ z : Nat, Word word_65 (4925280667798591242267 + 2^74*d) z ∧
      z < 4925280667798591242267 + 2^74*d := by
  have h := word_uniform_descent full_word_65
    (show 1540627915367174412541 < 4925280667798591242267 by norm_num)
    (show 3^word_65.length < 2^word_65.sum by norm_num [word_65, sharedPrefix, suffix_65]) d
  simpa [word_sum_65] using h

/-- Certificate 66; shared prefix plus independently witnessed suffix. -/
def suffix_66 : List Nat := [2, 1, 1, 3, 9]
def word_66 : List Nat := sharedPrefix ++ suffix_66
theorem suffix_proof_66 : Word suffix_66 1402897332656480358277961 5201783017509837754235 := by
  unfold suffix_66
  exact Word.cons
        (show ExactStep 1402897332656480358277961 1052172999492360268708471 2 from by
          refine ⟨by norm_num, ⟨701448666328240179138980, by norm_num⟩, by norm_num, ⟨526086499746180134354235, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1052172999492360268708471 1578259499238540403062707 1 from by
          refine ⟨by norm_num, ⟨526086499746180134354235, by norm_num⟩, by norm_num, ⟨789129749619270201531353, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1578259499238540403062707 2367389248857810604594061 1 from by
          refine ⟨by norm_num, ⟨789129749619270201531353, by norm_num⟩, by norm_num, ⟨1183694624428905302297030, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2367389248857810604594061 887770968321678976722773 3 from by
          refine ⟨by norm_num, ⟨1183694624428905302297030, by norm_num⟩, by norm_num, ⟨443885484160839488361386, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 887770968321678976722773 5201783017509837754235 9 from by
          refine ⟨by norm_num, ⟨443885484160839488361386, by norm_num⟩, by norm_num, ⟨2600891508754918877117, by norm_num⟩⟩)
        (Word.nil 5201783017509837754235)))))
theorem full_word_66 : Word word_66 33259479565016462524443 5201783017509837754235 := by
  unfold word_66
  have hp := shared_prefix_all 57696
  have ht := suffix_proof_66
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_66 : word_66.length = 45 := by decide
theorem word_sum_66 : word_66.sum = 74 := by decide
theorem infinite_family_66 (d : Nat) :
    ∃ z : Nat, Word word_66 (33259479565016462524443 + 2^75*d) z ∧
      z < 33259479565016462524443 + 2^75*d := by
  have h := word_uniform_descent full_word_66
    (show 5201783017509837754235 < 33259479565016462524443 by norm_num)
    (show 3^word_66.length < 2^word_66.sum by norm_num [word_66, sharedPrefix, suffix_66]) d
  simpa [word_sum_66] using h

/-- Certificate 67; shared prefix plus independently witnessed suffix. -/
def suffix_67 : List Nat := [2, 1, 1, 3, 6, 2]
def word_67 : List Nat := sharedPrefix ++ suffix_67
theorem suffix_proof_67 : Word suffix_67 108154591928753668686665 2406149216188397963641 := by
  unfold suffix_67
  exact Word.cons
        (show ExactStep 108154591928753668686665 81115943946565251514999 2 from by
          refine ⟨by norm_num, ⟨54077295964376834343332, by norm_num⟩, by norm_num, ⟨40557971973282625757499, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 81115943946565251514999 121673915919847877272499 1 from by
          refine ⟨by norm_num, ⟨40557971973282625757499, by norm_num⟩, by norm_num, ⟨60836957959923938636249, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 121673915919847877272499 182510873879771815908749 1 from by
          refine ⟨by norm_num, ⟨60836957959923938636249, by norm_num⟩, by norm_num, ⟨91255436939885907954374, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 182510873879771815908749 68441577704914430965781 3 from by
          refine ⟨by norm_num, ⟨91255436939885907954374, by norm_num⟩, by norm_num, ⟨34220788852457215482890, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 68441577704914430965781 3208198954917863951521 6 from by
          refine ⟨by norm_num, ⟨34220788852457215482890, by norm_num⟩, by norm_num, ⟨1604099477458931975760, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 3208198954917863951521 2406149216188397963641 2 from by
          refine ⟨by norm_num, ⟨1604099477458931975760, by norm_num⟩, by norm_num, ⟨1203074608094198981820, by norm_num⟩⟩)
        (Word.nil 2406149216188397963641))))))
theorem full_word_67 : Word word_67 2564097426363768635419 2406149216188397963641 := by
  unfold word_67
  have hp := shared_prefix_all 4448
  have ht := suffix_proof_67
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_67 : word_67.length = 46 := by decide
theorem word_sum_67 : word_67.sum = 73 := by decide
theorem infinite_family_67 (d : Nat) :
    ∃ z : Nat, Word word_67 (2564097426363768635419 + 2^74*d) z ∧
      z < 2564097426363768635419 + 2^74*d := by
  have h := word_uniform_descent full_word_67
    (show 2406149216188397963641 < 2564097426363768635419 by norm_num)
    (show 3^word_67.length < 2^word_67.sum by norm_num [word_67, sharedPrefix, suffix_67]) d
  simpa [word_sum_67] using h

/-- Certificate 68; shared prefix plus independently witnessed suffix. -/
def suffix_68 : List Nat := [2, 1, 1, 3, 6, 3]
def word_68 : List Nat := sharedPrefix ++ suffix_68
theorem suffix_proof_68 : Word suffix_68 506536973691131111637833 5634543667920449529785 := by
  unfold suffix_68
  exact Word.cons
        (show ExactStep 506536973691131111637833 379902730268348333728375 2 from by
          refine ⟨by norm_num, ⟨253268486845565555818916, by norm_num⟩, by norm_num, ⟨189951365134174166864187, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 379902730268348333728375 569854095402522500592563 1 from by
          refine ⟨by norm_num, ⟨189951365134174166864187, by norm_num⟩, by norm_num, ⟨284927047701261250296281, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 569854095402522500592563 854781143103783750888845 1 from by
          refine ⟨by norm_num, ⟨284927047701261250296281, by norm_num⟩, by norm_num, ⟨427390571551891875444422, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 854781143103783750888845 320542928663918906583317 3 from by
          refine ⟨by norm_num, ⟨427390571551891875444422, by norm_num⟩, by norm_num, ⟨160271464331959453291658, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 320542928663918906583317 15025449781121198746093 6 from by
          refine ⟨by norm_num, ⟨160271464331959453291658, by norm_num⟩, by norm_num, ⟨7512724890560599373046, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 15025449781121198746093 5634543667920449529785 3 from by
          refine ⟨by norm_num, ⟨7512724890560599373046, by norm_num⟩, by norm_num, ⟨2817271833960224764892, by norm_num⟩⟩)
        (Word.nil 5634543667920449529785))))))
theorem full_word_68 : Word word_68 12008830392103059062811 5634543667920449529785 := by
  unfold word_68
  have hp := shared_prefix_all 20832
  have ht := suffix_proof_68
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_68 : word_68.length = 46 := by decide
theorem word_sum_68 : word_68.sum = 74 := by decide
theorem infinite_family_68 (d : Nat) :
    ∃ z : Nat, Word word_68 (12008830392103059062811 + 2^75*d) z ∧
      z < 12008830392103059062811 + 2^75*d := by
  have h := word_uniform_descent full_word_68
    (show 5634543667920449529785 < 12008830392103059062811 by norm_num)
    (show 3^word_68.length < 2^word_68.sum by norm_num [word_68, sharedPrefix, suffix_68]) d
  simpa [word_sum_68] using h

/-- Certificate 69; shared prefix plus independently witnessed suffix. -/
def suffix_69 : List Nat := [2, 1, 1, 3, 5, 4]
def word_69 : List Nat := sharedPrefix ++ suffix_69
theorem suffix_proof_69 : Word suffix_69 954717153173805734957897 10619946360224981396245 := by
  unfold suffix_69
  exact Word.cons
        (show ExactStep 954717153173805734957897 716037864880354301218423 2 from by
          refine ⟨by norm_num, ⟨477358576586902867478948, by norm_num⟩, by norm_num, ⟨358018932440177150609211, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 716037864880354301218423 1074056797320531451827635 1 from by
          refine ⟨by norm_num, ⟨358018932440177150609211, by norm_num⟩, by norm_num, ⟨537028398660265725913817, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1074056797320531451827635 1611085195980797177741453 1 from by
          refine ⟨by norm_num, ⟨537028398660265725913817, by norm_num⟩, by norm_num, ⟨805542597990398588870726, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1611085195980797177741453 604156948492798941653045 3 from by
          refine ⟨by norm_num, ⟨805542597990398588870726, by norm_num⟩, by norm_num, ⟨302078474246399470826522, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 604156948492798941653045 56639713921199900779973 5 from by
          refine ⟨by norm_num, ⟨302078474246399470826522, by norm_num⟩, by norm_num, ⟨28319856960599950389986, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 56639713921199900779973 10619946360224981396245 4 from by
          refine ⟨by norm_num, ⟨28319856960599950389986, by norm_num⟩, by norm_num, ⟨5309973180112490698122, by norm_num⟩⟩)
        (Word.nil 10619946360224981396245))))))
theorem full_word_69 : Word word_69 22634154978559760793627 10619946360224981396245 := by
  unfold word_69
  have hp := shared_prefix_all 39264
  have ht := suffix_proof_69
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_69 : word_69.length = 46 := by decide
theorem word_sum_69 : word_69.sum = 74 := by decide
theorem infinite_family_69 (d : Nat) :
    ∃ z : Nat, Word word_69 (22634154978559760793627 + 2^75*d) z ∧
      z < 22634154978559760793627 + 2^75*d := by
  have h := word_uniform_descent full_word_69
    (show 10619946360224981396245 < 22634154978559760793627 by norm_num)
    (show 3^word_69.length < 2^word_69.sum by norm_num [word_69, sharedPrefix, suffix_69]) d
  simpa [word_sum_69] using h

/-- Certificate 70; shared prefix plus independently witnessed suffix. -/
def suffix_70 : List Nat := [2, 1, 1, 3, 5, 3]
def word_70 : List Nat := sharedPrefix ++ suffix_70
theorem suffix_proof_70 : Word suffix_70 556334771411428292006729 12376954600797461696561 := by
  unfold suffix_70
  exact Word.cons
        (show ExactStep 556334771411428292006729 417251078558571219005047 2 from by
          refine ⟨by norm_num, ⟨278167385705714146003364, by norm_num⟩, by norm_num, ⟨208625539279285609502523, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 417251078558571219005047 625876617837856828507571 1 from by
          refine ⟨by norm_num, ⟨208625539279285609502523, by norm_num⟩, by norm_num, ⟨312938308918928414253785, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 625876617837856828507571 938814926756785242761357 1 from by
          refine ⟨by norm_num, ⟨312938308918928414253785, by norm_num⟩, by norm_num, ⟨469407463378392621380678, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 938814926756785242761357 352055597533794466035509 3 from by
          refine ⟨by norm_num, ⟨469407463378392621380678, by norm_num⟩, by norm_num, ⟨176027798766897233017754, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 352055597533794466035509 33005212268793231190829 5 from by
          refine ⟨by norm_num, ⟨176027798766897233017754, by norm_num⟩, by norm_num, ⟨16502606134396615595414, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 33005212268793231190829 12376954600797461696561 3 from by
          refine ⟨by norm_num, ⟨16502606134396615595414, by norm_num⟩, by norm_num, ⟨6188477300398730848280, by norm_num⟩⟩)
        (Word.nil 12376954600797461696561))))))
theorem full_word_70 : Word word_70 13189422012820470366235 12376954600797461696561 := by
  unfold word_70
  have hp := shared_prefix_all 22880
  have ht := suffix_proof_70
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_70 : word_70.length = 46 := by decide
theorem word_sum_70 : word_70.sum = 73 := by decide
theorem infinite_family_70 (d : Nat) :
    ∃ z : Nat, Word word_70 (13189422012820470366235 + 2^74*d) z ∧
      z < 13189422012820470366235 + 2^74*d := by
  have h := word_uniform_descent full_word_70
    (show 12376954600797461696561 < 13189422012820470366235 by norm_num)
    (show 3^word_70.length < 2^word_70.sum by norm_num [word_70, sharedPrefix, suffix_70]) d
  simpa [word_sum_70] using h

/-- Certificate 71; shared prefix plus independently witnessed suffix. -/
def suffix_71 : List Nat := [2, 1, 1, 3, 4, 5]
def word_71 : List Nat := sharedPrefix ++ suffix_71
theorem suffix_proof_71 : Word suffix_71 1178807242915143046617929 13112647706377247329475 := by
  unfold suffix_71
  exact Word.cons
        (show ExactStep 1178807242915143046617929 884105432186357284963447 2 from by
          refine ⟨by norm_num, ⟨589403621457571523308964, by norm_num⟩, by norm_num, ⟨442052716093178642481723, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 884105432186357284963447 1326158148279535927445171 1 from by
          refine ⟨by norm_num, ⟨442052716093178642481723, by norm_num⟩, by norm_num, ⟨663079074139767963722585, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1326158148279535927445171 1989237222419303891167757 1 from by
          refine ⟨by norm_num, ⟨663079074139767963722585, by norm_num⟩, by norm_num, ⟨994618611209651945583878, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1989237222419303891167757 745963958407238959187909 3 from by
          refine ⟨by norm_num, ⟨994618611209651945583878, by norm_num⟩, by norm_num, ⟨372981979203619479593954, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 745963958407238959187909 139868242201357304847733 4 from by
          refine ⟨by norm_num, ⟨372981979203619479593954, by norm_num⟩, by norm_num, ⟨69934121100678652423866, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 139868242201357304847733 13112647706377247329475 5 from by
          refine ⟨by norm_num, ⟨69934121100678652423866, by norm_num⟩, by norm_num, ⟨6556323853188623664737, by norm_num⟩⟩)
        (Word.nil 13112647706377247329475))))))
theorem full_word_71 : Word word_71 27946817271788111659035 13112647706377247329475 := by
  unfold word_71
  have hp := shared_prefix_all 48480
  have ht := suffix_proof_71
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_71 : word_71.length = 46 := by decide
theorem word_sum_71 : word_71.sum = 74 := by decide
theorem infinite_family_71 (d : Nat) :
    ∃ z : Nat, Word word_71 (27946817271788111659035 + 2^75*d) z ∧
      z < 27946817271788111659035 + 2^75*d := by
  have h := word_uniform_descent full_word_71
    (show 13112647706377247329475 < 27946817271788111659035 by norm_num)
    (show 3^word_71.length < 2^word_71.sum by norm_num [word_71, sharedPrefix, suffix_71]) d
  simpa [word_sum_71] using h

/-- Certificate 72; shared prefix plus independently witnessed suffix. -/
def suffix_72 : List Nat := [2, 1, 1, 3, 4, 4]
def word_72 : List Nat := sharedPrefix ++ suffix_72
theorem suffix_proof_72 : Word suffix_72 780424861152765603666761 17362357293101993563021 := by
  unfold suffix_72
  exact Word.cons
        (show ExactStep 780424861152765603666761 585318645864574202750071 2 from by
          refine ⟨by norm_num, ⟨390212430576382801833380, by norm_num⟩, by norm_num, ⟨292659322932287101375035, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 585318645864574202750071 877977968796861304125107 1 from by
          refine ⟨by norm_num, ⟨292659322932287101375035, by norm_num⟩, by norm_num, ⟨438988984398430652062553, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 877977968796861304125107 1316966953195291956187661 1 from by
          refine ⟨by norm_num, ⟨438988984398430652062553, by norm_num⟩, by norm_num, ⟨658483476597645978093830, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1316966953195291956187661 493862607448234483570373 3 from by
          refine ⟨by norm_num, ⟨658483476597645978093830, by norm_num⟩, by norm_num, ⟨246931303724117241785186, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 493862607448234483570373 92599238896543965669445 4 from by
          refine ⟨by norm_num, ⟨246931303724117241785186, by norm_num⟩, by norm_num, ⟨46299619448271982834722, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 92599238896543965669445 17362357293101993563021 4 from by
          refine ⟨by norm_num, ⟨46299619448271982834722, by norm_num⟩, by norm_num, ⟨8681178646550996781510, by norm_num⟩⟩)
        (Word.nil 17362357293101993563021))))))
theorem full_word_72 : Word word_72 18502084306048821231643 17362357293101993563021 := by
  unfold word_72
  have hp := shared_prefix_all 32096
  have ht := suffix_proof_72
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_72 : word_72.length = 46 := by decide
theorem word_sum_72 : word_72.sum = 73 := by decide
theorem infinite_family_72 (d : Nat) :
    ∃ z : Nat, Word word_72 (18502084306048821231643 + 2^74*d) z ∧
      z < 18502084306048821231643 + 2^74*d := by
  have h := word_uniform_descent full_word_72
    (show 17362357293101993563021 < 18502084306048821231643 by norm_num)
    (show 3^word_72.length < 2^word_72.sum by norm_num [word_72, sharedPrefix, suffix_72]) d
  simpa [word_sum_72] using h

/-- Certificate 73; shared prefix plus independently witnessed suffix. -/
def suffix_73 : List Nat := [2, 1, 1, 3, 3, 5]
def word_73 : List Nat := sharedPrefix ++ suffix_73
theorem suffix_proof_73 : Word suffix_73 95705142498679373594441 2129182399949257304393 := by
  unfold suffix_73
  exact Word.cons
        (show ExactStep 95705142498679373594441 71778856874009530195831 2 from by
          refine ⟨by norm_num, ⟨47852571249339686797220, by norm_num⟩, by norm_num, ⟨35889428437004765097915, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 71778856874009530195831 107668285311014295293747 1 from by
          refine ⟨by norm_num, ⟨35889428437004765097915, by norm_num⟩, by norm_num, ⟨53834142655507147646873, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 107668285311014295293747 161502427966521442940621 1 from by
          refine ⟨by norm_num, ⟨53834142655507147646873, by norm_num⟩, by norm_num, ⟨80751213983260721470310, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 161502427966521442940621 60563410487445541102733 3 from by
          refine ⟨by norm_num, ⟨80751213983260721470310, by norm_num⟩, by norm_num, ⟨30281705243722770551366, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 60563410487445541102733 22711278932792077913525 3 from by
          refine ⟨by norm_num, ⟨30281705243722770551366, by norm_num⟩, by norm_num, ⟨11355639466396038956762, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 22711278932792077913525 2129182399949257304393 5 from by
          refine ⟨by norm_num, ⟨11355639466396038956762, by norm_num⟩, by norm_num, ⟨1064591199974628652196, by norm_num⟩⟩)
        (Word.nil 2129182399949257304393))))))
theorem full_word_73 : Word word_73 2268949521184415809563 2129182399949257304393 := by
  unfold word_73
  have hp := shared_prefix_all 3936
  have ht := suffix_proof_73
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_73 : word_73.length = 46 := by decide
theorem word_sum_73 : word_73.sum = 73 := by decide
theorem infinite_family_73 (d : Nat) :
    ∃ z : Nat, Word word_73 (2268949521184415809563 + 2^74*d) z ∧
      z < 2268949521184415809563 + 2^74*d := by
  have h := word_uniform_descent full_word_73
    (show 2129182399949257304393 < 2268949521184415809563 by norm_num)
    (show 3^word_73.length < 2^word_73.sum by norm_num [word_73, sharedPrefix, suffix_73]) d
  simpa [word_sum_73] using h

/-- Certificate 74; shared prefix plus independently witnessed suffix. -/
def suffix_74 : List Nat := [2, 1, 1, 3, 3, 6]
def word_74 : List Nat := sharedPrefix ++ suffix_74
theorem suffix_proof_74 : Word suffix_74 494087524261056816545609 5496060259800879200161 := by
  unfold suffix_74
  exact Word.cons
        (show ExactStep 494087524261056816545609 370565643195792612409207 2 from by
          refine ⟨by norm_num, ⟨247043762130528408272804, by norm_num⟩, by norm_num, ⟨185282821597896306204603, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 370565643195792612409207 555848464793688918613811 1 from by
          refine ⟨by norm_num, ⟨185282821597896306204603, by norm_num⟩, by norm_num, ⟨277924232396844459306905, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 555848464793688918613811 833772697190533377920717 1 from by
          refine ⟨by norm_num, ⟨277924232396844459306905, by norm_num⟩, by norm_num, ⟨416886348595266688960358, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 833772697190533377920717 312664761446450016720269 3 from by
          refine ⟨by norm_num, ⟨416886348595266688960358, by norm_num⟩, by norm_num, ⟨156332380723225008360134, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 312664761446450016720269 117249285542418756270101 3 from by
          refine ⟨by norm_num, ⟨156332380723225008360134, by norm_num⟩, by norm_num, ⟨58624642771209378135050, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 117249285542418756270101 5496060259800879200161 6 from by
          refine ⟨by norm_num, ⟨58624642771209378135050, by norm_num⟩, by norm_num, ⟨2748030129900439600080, by norm_num⟩⟩)
        (Word.nil 5496060259800879200161))))))
theorem full_word_74 : Word word_74 11713682486923706236955 5496060259800879200161 := by
  unfold word_74
  have hp := shared_prefix_all 20320
  have ht := suffix_proof_74
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_74 : word_74.length = 46 := by decide
theorem word_sum_74 : word_74.sum = 74 := by decide
theorem infinite_family_74 (d : Nat) :
    ∃ z : Nat, Word word_74 (11713682486923706236955 + 2^75*d) z ∧
      z < 11713682486923706236955 + 2^75*d := by
  have h := word_uniform_descent full_word_74
    (show 5496060259800879200161 < 11713682486923706236955 by norm_num)
    (show 3^word_74.length < 2^word_74.sum by norm_num [word_74, sharedPrefix, suffix_74]) d
  simpa [word_sum_74] using h

/-- Certificate 75; shared prefix plus independently witnessed suffix. -/
def suffix_75 : List Nat := [2, 1, 1, 3, 1, 8]
def word_75 : List Nat := sharedPrefix ++ suffix_75
theorem suffix_proof_75 : Word suffix_75 1175694880557624472844873 13078026854347354747069 := by
  unfold suffix_75
  exact Word.cons
        (show ExactStep 1175694880557624472844873 881771160418218354633655 2 from by
          refine ⟨by norm_num, ⟨587847440278812236422436, by norm_num⟩, by norm_num, ⟨440885580209109177316827, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 881771160418218354633655 1322656740627327531950483 1 from by
          refine ⟨by norm_num, ⟨440885580209109177316827, by norm_num⟩, by norm_num, ⟨661328370313663765975241, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1322656740627327531950483 1983985110940991297925725 1 from by
          refine ⟨by norm_num, ⟨661328370313663765975241, by norm_num⟩, by norm_num, ⟨991992555470495648962862, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1983985110940991297925725 743994416602871736722147 3 from by
          refine ⟨by norm_num, ⟨991992555470495648962862, by norm_num⟩, by norm_num, ⟨371997208301435868361073, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 743994416602871736722147 1115991624904307605083221 1 from by
          refine ⟨by norm_num, ⟨371997208301435868361073, by norm_num⟩, by norm_num, ⟨557995812452153802541610, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1115991624904307605083221 13078026854347354747069 8 from by
          refine ⟨by norm_num, ⟨557995812452153802541610, by norm_num⟩, by norm_num, ⟨6539013427173677373534, by norm_num⟩⟩)
        (Word.nil 13078026854347354747069))))))
theorem full_word_75 : Word word_75 27873030295493273452571 13078026854347354747069 := by
  unfold word_75
  have hp := shared_prefix_all 48352
  have ht := suffix_proof_75
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_75 : word_75.length = 46 := by decide
theorem word_sum_75 : word_75.sum = 74 := by decide
theorem infinite_family_75 (d : Nat) :
    ∃ z : Nat, Word word_75 (27873030295493273452571 + 2^75*d) z ∧
      z < 27873030295493273452571 + 2^75*d := by
  have h := word_uniform_descent full_word_75
    (show 13078026854347354747069 < 27873030295493273452571 by norm_num)
    (show 3^word_75.length < 2^word_75.sum by norm_num [word_75, sharedPrefix, suffix_75]) d
  simpa [word_sum_75] using h

/-- Certificate 76; shared prefix plus independently witnessed suffix. -/
def suffix_76 : List Nat := [2, 1, 1, 3, 1, 7]
def word_76 : List Nat := sharedPrefix ++ suffix_76
theorem suffix_proof_76 : Word suffix_76 777312498795247029893705 17293115589042208398209 := by
  unfold suffix_76
  exact Word.cons
        (show ExactStep 777312498795247029893705 582984374096435272420279 2 from by
          refine ⟨by norm_num, ⟨388656249397623514946852, by norm_num⟩, by norm_num, ⟨291492187048217636210139, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 582984374096435272420279 874476561144652908630419 1 from by
          refine ⟨by norm_num, ⟨291492187048217636210139, by norm_num⟩, by norm_num, ⟨437238280572326454315209, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 874476561144652908630419 1311714841716979362945629 1 from by
          refine ⟨by norm_num, ⟨437238280572326454315209, by norm_num⟩, by norm_num, ⟨655857420858489681472814, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1311714841716979362945629 491893065643867261104611 3 from by
          refine ⟨by norm_num, ⟨655857420858489681472814, by norm_num⟩, by norm_num, ⟨245946532821933630552305, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 491893065643867261104611 737839598465800891656917 1 from by
          refine ⟨by norm_num, ⟨245946532821933630552305, by norm_num⟩, by norm_num, ⟨368919799232900445828458, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 737839598465800891656917 17293115589042208398209 7 from by
          refine ⟨by norm_num, ⟨368919799232900445828458, by norm_num⟩, by norm_num, ⟨8646557794521104199104, by norm_num⟩⟩)
        (Word.nil 17293115589042208398209))))))
theorem full_word_76 : Word word_76 18428297329753983025179 17293115589042208398209 := by
  unfold word_76
  have hp := shared_prefix_all 31968
  have ht := suffix_proof_76
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_76 : word_76.length = 46 := by decide
theorem word_sum_76 : word_76.sum = 73 := by decide
theorem infinite_family_76 (d : Nat) :
    ∃ z : Nat, Word word_76 (18428297329753983025179 + 2^74*d) z ∧
      z < 18428297329753983025179 + 2^74*d := by
  have h := word_uniform_descent full_word_76
    (show 17293115589042208398209 < 18428297329753983025179 by norm_num)
    (show 3^word_76.length < 2^word_76.sum by norm_num [word_76, sharedPrefix, suffix_76]) d
  simpa [word_sum_76] using h

/-- Certificate 77; shared prefix plus independently witnessed suffix. -/
def suffix_77 : List Nat := [2, 1, 1, 1, 1, 9]
def word_77 : List Nat := sharedPrefix ++ suffix_77
theorem suffix_proof_77 : Word suffix_77 8169951193469486227241 181759473267799544057 := by
  unfold suffix_77
  exact Word.cons
        (show ExactStep 8169951193469486227241 6127463395102114670431 2 from by
          refine ⟨by norm_num, ⟨4084975596734743113620, by norm_num⟩, by norm_num, ⟨3063731697551057335215, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 6127463395102114670431 9191195092653172005647 1 from by
          refine ⟨by norm_num, ⟨3063731697551057335215, by norm_num⟩, by norm_num, ⟨4595597546326586002823, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 9191195092653172005647 13786792638979758008471 1 from by
          refine ⟨by norm_num, ⟨4595597546326586002823, by norm_num⟩, by norm_num, ⟨6893396319489879004235, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 13786792638979758008471 20680188958469637012707 1 from by
          refine ⟨by norm_num, ⟨6893396319489879004235, by norm_num⟩, by norm_num, ⟨10340094479234818506353, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 20680188958469637012707 31020283437704455519061 1 from by
          refine ⟨by norm_num, ⟨10340094479234818506353, by norm_num⟩, by norm_num, ⟨15510141718852227759530, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 31020283437704455519061 181759473267799544057 9 from by
          refine ⟨by norm_num, ⟨15510141718852227759530, by norm_num⟩, by norm_num, ⟨90879736633899772028, by norm_num⟩⟩)
        (Word.nil 181759473267799544057))))))
theorem full_word_77 : Word word_77 193690812892091252763 181759473267799544057 := by
  unfold word_77
  have hp := shared_prefix_all 336
  have ht := suffix_proof_77
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_77 : word_77.length = 46 := by decide
theorem word_sum_77 : word_77.sum = 73 := by decide
theorem infinite_family_77 (d : Nat) :
    ∃ z : Nat, Word word_77 (193690812892091252763 + 2^74*d) z ∧
      z < 193690812892091252763 + 2^74*d := by
  have h := word_uniform_descent full_word_77
    (show 181759473267799544057 < 193690812892091252763 by norm_num)
    (show 3^word_77.length < 2^word_77.sum by norm_num [word_77, sharedPrefix, suffix_77]) d
  simpa [word_sum_77] using h

/-- Certificate 78; shared prefix plus independently witnessed suffix. -/
def suffix_78 : List Nat := [2, 1, 1, 1, 1, 10]
def word_78 : List Nat := sharedPrefix ++ suffix_78
theorem suffix_proof_78 : Word suffix_78 406552332955846929178409 4522348796460150319993 := by
  unfold suffix_78
  exact Word.cons
        (show ExactStep 406552332955846929178409 304914249716885196883807 2 from by
          refine ⟨by norm_num, ⟨203276166477923464589204, by norm_num⟩, by norm_num, ⟨152457124858442598441903, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 304914249716885196883807 457371374575327795325711 1 from by
          refine ⟨by norm_num, ⟨152457124858442598441903, by norm_num⟩, by norm_num, ⟨228685687287663897662855, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 457371374575327795325711 686057061862991692988567 1 from by
          refine ⟨by norm_num, ⟨228685687287663897662855, by norm_num⟩, by norm_num, ⟨343028530931495846494283, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 686057061862991692988567 1029085592794487539482851 1 from by
          refine ⟨by norm_num, ⟨343028530931495846494283, by norm_num⟩, by norm_num, ⟨514542796397243769741425, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1029085592794487539482851 1543628389191731309224277 1 from by
          refine ⟨by norm_num, ⟨514542796397243769741425, by norm_num⟩, by norm_num, ⟨771814194595865654612138, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1543628389191731309224277 4522348796460150319993 10 from by
          refine ⟨by norm_num, ⟨771814194595865654612138, by norm_num⟩, by norm_num, ⟨2261174398230075159996, by norm_num⟩⟩)
        (Word.nil 4522348796460150319993))))))
theorem full_word_78 : Word word_78 9638423778631381680155 4522348796460150319993 := by
  unfold word_78
  have hp := shared_prefix_all 16720
  have ht := suffix_proof_78
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_78 : word_78.length = 46 := by decide
theorem word_sum_78 : word_78.sum = 74 := by decide
theorem infinite_family_78 (d : Nat) :
    ∃ z : Nat, Word word_78 (9638423778631381680155 + 2^75*d) z ∧
      z < 9638423778631381680155 + 2^75*d := by
  have h := word_uniform_descent full_word_78
    (show 4522348796460150319993 < 9638423778631381680155 by norm_num)
    (show 3^word_78.length < 2^word_78.sum by norm_num [word_78, sharedPrefix, suffix_78]) d
  simpa [word_sum_78] using h

/-- Certificate 79; shared prefix plus independently witnessed suffix. -/
def suffix_79 : List Nat := [2, 1, 1, 1, 2, 9]
def word_79 : List Nat := sharedPrefix ++ suffix_79
theorem suffix_proof_79 : Word suffix_79 1146516483455887843722473 12753456366567111787013 := by
  unfold suffix_79
  exact Word.cons
        (show ExactStep 1146516483455887843722473 859887362591915882791855 2 from by
          refine ⟨by norm_num, ⟨573258241727943921861236, by norm_num⟩, by norm_num, ⟨429943681295957941395927, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 859887362591915882791855 1289831043887873824187783 1 from by
          refine ⟨by norm_num, ⟨429943681295957941395927, by norm_num⟩, by norm_num, ⟨644915521943936912093891, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1289831043887873824187783 1934746565831810736281675 1 from by
          refine ⟨by norm_num, ⟨644915521943936912093891, by norm_num⟩, by norm_num, ⟨967373282915905368140837, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1934746565831810736281675 2902119848747716104422513 1 from by
          refine ⟨by norm_num, ⟨967373282915905368140837, by norm_num⟩, by norm_num, ⟨1451059924373858052211256, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2902119848747716104422513 2176589886560787078316885 2 from by
          refine ⟨by norm_num, ⟨1451059924373858052211256, by norm_num⟩, by norm_num, ⟨1088294943280393539158442, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2176589886560787078316885 12753456366567111787013 9 from by
          refine ⟨by norm_num, ⟨1088294943280393539158442, by norm_num⟩, by norm_num, ⟨6376728183283555893506, by norm_num⟩⟩)
        (Word.nil 12753456366567111787013))))))
theorem full_word_79 : Word word_79 27181277392729165266971 12753456366567111787013 := by
  unfold word_79
  have hp := shared_prefix_all 47152
  have ht := suffix_proof_79
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_79 : word_79.length = 46 := by decide
theorem word_sum_79 : word_79.sum = 74 := by decide
theorem infinite_family_79 (d : Nat) :
    ∃ z : Nat, Word word_79 (27181277392729165266971 + 2^75*d) z ∧
      z < 27181277392729165266971 + 2^75*d := by
  have h := word_uniform_descent full_word_79
    (show 12753456366567111787013 < 27181277392729165266971 by norm_num)
    (show 3^word_79.length < 2^word_79.sum by norm_num [word_79, sharedPrefix, suffix_79]) d
  simpa [word_sum_79] using h

/-- Certificate 80; shared prefix plus independently witnessed suffix. -/
def suffix_80 : List Nat := [2, 1, 1, 1, 2, 8]
def word_80 : List Nat := sharedPrefix ++ suffix_80
theorem suffix_proof_80 : Word suffix_80 748134101693510400771305 16643974613481722478097 := by
  unfold suffix_80
  exact Word.cons
        (show ExactStep 748134101693510400771305 561100576270132800578479 2 from by
          refine ⟨by norm_num, ⟨374067050846755200385652, by norm_num⟩, by norm_num, ⟨280550288135066400289239, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 561100576270132800578479 841650864405199200867719 1 from by
          refine ⟨by norm_num, ⟨280550288135066400289239, by norm_num⟩, by norm_num, ⟨420825432202599600433859, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 841650864405199200867719 1262476296607798801301579 1 from by
          refine ⟨by norm_num, ⟨420825432202599600433859, by norm_num⟩, by norm_num, ⟨631238148303899400650789, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1262476296607798801301579 1893714444911698201952369 1 from by
          refine ⟨by norm_num, ⟨631238148303899400650789, by norm_num⟩, by norm_num, ⟨946857222455849100976184, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1893714444911698201952369 1420285833683773651464277 2 from by
          refine ⟨by norm_num, ⟨946857222455849100976184, by norm_num⟩, by norm_num, ⟨710142916841886825732138, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1420285833683773651464277 16643974613481722478097 8 from by
          refine ⟨by norm_num, ⟨710142916841886825732138, by norm_num⟩, by norm_num, ⟨8321987306740861239048, by norm_num⟩⟩)
        (Word.nil 16643974613481722478097))))))
theorem full_word_80 : Word word_80 17736544426989874839579 16643974613481722478097 := by
  unfold word_80
  have hp := shared_prefix_all 30768
  have ht := suffix_proof_80
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_80 : word_80.length = 46 := by decide
theorem word_sum_80 : word_80.sum = 73 := by decide
theorem infinite_family_80 (d : Nat) :
    ∃ z : Nat, Word word_80 (17736544426989874839579 + 2^74*d) z ∧
      z < 17736544426989874839579 + 2^74*d := by
  have h := word_uniform_descent full_word_80
    (show 16643974613481722478097 < 17736544426989874839579 by norm_num)
    (show 3^word_80.length < 2^word_80.sum by norm_num [word_80, sharedPrefix, suffix_80]) d
  simpa [word_sum_80] using h

/-- Certificate 81; shared prefix plus independently witnessed suffix. -/
def suffix_81 : List Nat := [2, 1, 1, 1, 5, 6]
def word_81 : List Nat := sharedPrefix ++ suffix_81
theorem suffix_proof_81 : Word suffix_81 351307901109892244706665 3907828672929556982287 := by
  unfold suffix_81
  exact Word.cons
        (show ExactStep 351307901109892244706665 263480925832419183529999 2 from by
          refine ⟨by norm_num, ⟨175653950554946122353332, by norm_num⟩, by norm_num, ⟨131740462916209591764999, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 263480925832419183529999 395221388748628775294999 1 from by
          refine ⟨by norm_num, ⟨131740462916209591764999, by norm_num⟩, by norm_num, ⟨197610694374314387647499, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 395221388748628775294999 592832083122943162942499 1 from by
          refine ⟨by norm_num, ⟨197610694374314387647499, by norm_num⟩, by norm_num, ⟨296416041561471581471249, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 592832083122943162942499 889248124684414744413749 1 from by
          refine ⟨by norm_num, ⟨296416041561471581471249, by norm_num⟩, by norm_num, ⟨444624062342207372206874, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 889248124684414744413749 83367011689163882288789 5 from by
          refine ⟨by norm_num, ⟨444624062342207372206874, by norm_num⟩, by norm_num, ⟨41683505844581941144394, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 83367011689163882288789 3907828672929556982287 6 from by
          refine ⟨by norm_num, ⟨41683505844581941144394, by norm_num⟩, by norm_num, ⟨1953914336464778491143, by norm_num⟩⟩)
        (Word.nil 3907828672929556982287))))))
theorem full_word_81 : Word word_81 8328704949398003515419 3907828672929556982287 := by
  unfold word_81
  have hp := shared_prefix_all 14448
  have ht := suffix_proof_81
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_81 : word_81.length = 46 := by decide
theorem word_sum_81 : word_81.sum = 74 := by decide
theorem infinite_family_81 (d : Nat) :
    ∃ z : Nat, Word word_81 (8328704949398003515419 + 2^75*d) z ∧
      z < 8328704949398003515419 + 2^75*d := by
  have h := word_uniform_descent full_word_81
    (show 3907828672929556982287 < 8328704949398003515419 by norm_num)
    (show 3^word_81.length < 2^word_81.sum by norm_num [word_81, sharedPrefix, suffix_81]) d
  simpa [word_sum_81] using h

/-- Certificate 82; shared prefix plus independently witnessed suffix. -/
def suffix_82 : List Nat := [2, 1, 1, 1, 5, 5]
def word_82 : List Nat := sharedPrefix ++ suffix_82
theorem suffix_proof_82 : Word suffix_82 749690282872269687657833 16678595465511615060503 := by
  unfold suffix_82
  exact Word.cons
        (show ExactStep 749690282872269687657833 562267712154202265743375 2 from by
          refine ⟨by norm_num, ⟨374845141436134843828916, by norm_num⟩, by norm_num, ⟨281133856077101132871687, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 562267712154202265743375 843401568231303398615063 1 from by
          refine ⟨by norm_num, ⟨281133856077101132871687, by norm_num⟩, by norm_num, ⟨421700784115651699307531, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 843401568231303398615063 1265102352346955097922595 1 from by
          refine ⟨by norm_num, ⟨421700784115651699307531, by norm_num⟩, by norm_num, ⟨632551176173477548961297, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1265102352346955097922595 1897653528520432646883893 1 from by
          refine ⟨by norm_num, ⟨632551176173477548961297, by norm_num⟩, by norm_num, ⟨948826764260216323441946, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1897653528520432646883893 177905018298790560645365 5 from by
          refine ⟨by norm_num, ⟨948826764260216323441946, by norm_num⟩, by norm_num, ⟨88952509149395280322682, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 177905018298790560645365 16678595465511615060503 5 from by
          refine ⟨by norm_num, ⟨88952509149395280322682, by norm_num⟩, by norm_num, ⟨8339297732755807530251, by norm_num⟩⟩)
        (Word.nil 16678595465511615060503))))))
theorem full_word_82 : Word word_82 17773437915137293942811 16678595465511615060503 := by
  unfold word_82
  have hp := shared_prefix_all 30832
  have ht := suffix_proof_82
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_82 : word_82.length = 46 := by decide
theorem word_sum_82 : word_82.sum = 73 := by decide
theorem infinite_family_82 (d : Nat) :
    ∃ z : Nat, Word word_82 (17773437915137293942811 + 2^74*d) z ∧
      z < 17773437915137293942811 + 2^74*d := by
  have h := word_uniform_descent full_word_82
    (show 16678595465511615060503 < 17773437915137293942811 by norm_num)
    (show 3^word_82.length < 2^word_82.sum by norm_num [word_82, sharedPrefix, suffix_82]) d
  simpa [word_sum_82] using h

/-- Certificate 83; shared prefix plus independently witnessed suffix. -/
def suffix_83 : List Nat := [2, 1, 1, 1, 7, 4]
def word_83 : List Nat := sharedPrefix ++ suffix_83
theorem suffix_proof_83 : Word suffix_83 811937530022641163118953 9031714773353659178371 := by
  unfold suffix_83
  exact Word.cons
        (show ExactStep 811937530022641163118953 608953147516980872339215 2 from by
          refine ⟨by norm_num, ⟨405968765011320581559476, by norm_num⟩, by norm_num, ⟨304476573758490436169607, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 608953147516980872339215 913429721275471308508823 1 from by
          refine ⟨by norm_num, ⟨304476573758490436169607, by norm_num⟩, by norm_num, ⟨456714860637735654254411, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 913429721275471308508823 1370144581913206962763235 1 from by
          refine ⟨by norm_num, ⟨456714860637735654254411, by norm_num⟩, by norm_num, ⟨685072290956603481381617, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1370144581913206962763235 2055216872869810444144853 1 from by
          refine ⟨by norm_num, ⟨685072290956603481381617, by norm_num⟩, by norm_num, ⟨1027608436434905222072426, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2055216872869810444144853 48169145457886182284645 7 from by
          refine ⟨by norm_num, ⟨1027608436434905222072426, by norm_num⟩, by norm_num, ⟨24084572728943091142322, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 48169145457886182284645 9031714773353659178371 4 from by
          refine ⟨by norm_num, ⟨24084572728943091142322, by norm_num⟩, by norm_num, ⟨4515857386676829589185, by norm_num⟩⟩)
        (Word.nil 9031714773353659178371))))))
theorem full_word_83 : Word word_83 19249177441034058072091 9031714773353659178371 := by
  unfold word_83
  have hp := shared_prefix_all 33392
  have ht := suffix_proof_83
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_83 : word_83.length = 46 := by decide
theorem word_sum_83 : word_83.sum = 74 := by decide
theorem infinite_family_83 (d : Nat) :
    ∃ z : Nat, Word word_83 (19249177441034058072091 + 2^75*d) z ∧
      z < 19249177441034058072091 + 2^75*d := by
  have h := word_uniform_descent full_word_83
    (show 9031714773353659178371 < 19249177441034058072091 by norm_num)
    (show 3^word_83.length < 2^word_83.sum by norm_num [word_83, sharedPrefix, suffix_83]) d
  simpa [word_sum_83] using h

/-- Certificate 84; shared prefix plus independently witnessed suffix. -/
def suffix_84 : List Nat := [2, 1, 1, 1, 7, 3]
def word_84 : List Nat := sharedPrefix ++ suffix_84
theorem suffix_proof_84 : Word suffix_84 413555148260263720167785 9200491427054817260813 := by
  unfold suffix_84
  exact Word.cons
        (show ExactStep 413555148260263720167785 310166361195197790125839 2 from by
          refine ⟨by norm_num, ⟨206777574130131860083892, by norm_num⟩, by norm_num, ⟨155083180597598895062919, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 310166361195197790125839 465249541792796685188759 1 from by
          refine ⟨by norm_num, ⟨155083180597598895062919, by norm_num⟩, by norm_num, ⟨232624770896398342594379, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 465249541792796685188759 697874312689195027783139 1 from by
          refine ⟨by norm_num, ⟨232624770896398342594379, by norm_num⟩, by norm_num, ⟨348937156344597513891569, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 697874312689195027783139 1046811469033792541674709 1 from by
          refine ⟨by norm_num, ⟨348937156344597513891569, by norm_num⟩, by norm_num, ⟨523405734516896270837354, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1046811469033792541674709 24534643805479512695501 7 from by
          refine ⟨by norm_num, ⟨523405734516896270837354, by norm_num⟩, by norm_num, ⟨12267321902739756347750, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 24534643805479512695501 9200491427054817260813 3 from by
          refine ⟨by norm_num, ⟨12267321902739756347750, by norm_num⟩, by norm_num, ⟨4600245713527408630406, by norm_num⟩⟩)
        (Word.nil 9200491427054817260813))))))
theorem full_word_84 : Word word_84 9804444475294767644699 9200491427054817260813 := by
  unfold word_84
  have hp := shared_prefix_all 17008
  have ht := suffix_proof_84
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_84 : word_84.length = 46 := by decide
theorem word_sum_84 : word_84.sum = 73 := by decide
theorem infinite_family_84 (d : Nat) :
    ∃ z : Nat, Word word_84 (9804444475294767644699 + 2^74*d) z ∧
      z < 9804444475294767644699 + 2^74*d := by
  have h := word_uniform_descent full_word_84
    (show 9200491427054817260813 < 9804444475294767644699 by norm_num)
    (show 3^word_84.length < 2^word_84.sum by norm_num [word_84, sharedPrefix, suffix_84]) d
  simpa [word_sum_84] using h

/-- Certificate 85; shared prefix plus independently witnessed suffix. -/
def suffix_85 : List Nat := [2, 1, 1, 1, 10]
def word_85 : List Nat := sharedPrefix ++ suffix_85
theorem suffix_proof_85 : Word suffix_85 64970564218183457585513 481806857452959600625 := by
  unfold suffix_85
  exact Word.cons
        (show ExactStep 64970564218183457585513 48727923163637593189135 2 from by
          refine ⟨by norm_num, ⟨32485282109091728792756, by norm_num⟩, by norm_num, ⟨24363961581818796594567, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 48727923163637593189135 73091884745456389783703 1 from by
          refine ⟨by norm_num, ⟨24363961581818796594567, by norm_num⟩, by norm_num, ⟨36545942372728194891851, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 73091884745456389783703 109637827118184584675555 1 from by
          refine ⟨by norm_num, ⟨36545942372728194891851, by norm_num⟩, by norm_num, ⟨54818913559092292337777, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 109637827118184584675555 164456740677276877013333 1 from by
          refine ⟨by norm_num, ⟨54818913559092292337777, by norm_num⟩, by norm_num, ⟨82228370338638438506666, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 164456740677276877013333 481806857452959600625 10 from by
          refine ⟨by norm_num, ⟨82228370338638438506666, by norm_num⟩, by norm_num, ⟨240903428726479800312, by norm_num⟩⟩)
        (Word.nil 481806857452959600625)))))
theorem full_word_85 : Word word_85 1540303130272888520731 481806857452959600625 := by
  unfold word_85
  have hp := shared_prefix_all 2672
  have ht := suffix_proof_85
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_85 : word_85.length = 45 := by decide
theorem word_sum_85 : word_85.sum = 73 := by decide
theorem infinite_family_85 (d : Nat) :
    ∃ z : Nat, Word word_85 (1540303130272888520731 + 2^74*d) z ∧
      z < 1540303130272888520731 + 2^74*d := by
  have h := word_uniform_descent full_word_85
    (show 481806857452959600625 < 1540303130272888520731 by norm_num)
    (show 3^word_85.length < 2^word_85.sum by norm_num [word_85, sharedPrefix, suffix_85]) d
  simpa [word_sum_85] using h

/-- Certificate 86; shared prefix plus independently witnessed suffix. -/
def suffix_86 : List Nat := [2, 1, 1, 1, 11]
def word_86 : List Nat := sharedPrefix ++ suffix_86
theorem suffix_proof_86 : Word suffix_86 1260117709505315786439017 4672372488552730348277 := by
  unfold suffix_86
  exact Word.cons
        (show ExactStep 1260117709505315786439017 945088282128986839829263 2 from by
          refine ⟨by norm_num, ⟨630058854752657893219508, by norm_num⟩, by norm_num, ⟨472544141064493419914631, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 945088282128986839829263 1417632423193480259743895 1 from by
          refine ⟨by norm_num, ⟨472544141064493419914631, by norm_num⟩, by norm_num, ⟨708816211596740129871947, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1417632423193480259743895 2126448634790220389615843 1 from by
          refine ⟨by norm_num, ⟨708816211596740129871947, by norm_num⟩, by norm_num, ⟨1063224317395110194807921, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2126448634790220389615843 3189672952185330584423765 1 from by
          refine ⟨by norm_num, ⟨1063224317395110194807921, by norm_num⟩, by norm_num, ⟨1594836476092665292211882, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 3189672952185330584423765 4672372488552730348277 11 from by
          refine ⟨by norm_num, ⟨1594836476092665292211882, by norm_num⟩, by norm_num, ⟨2336186244276365174138, by norm_num⟩⟩)
        (Word.nil 4672372488552730348277)))))
theorem full_word_86 : Word word_86 29874502027490759802907 4672372488552730348277 := by
  unfold word_86
  have hp := shared_prefix_all 51824
  have ht := suffix_proof_86
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_86 : word_86.length = 45 := by decide
theorem word_sum_86 : word_86.sum = 74 := by decide
theorem infinite_family_86 (d : Nat) :
    ∃ z : Nat, Word word_86 (29874502027490759802907 + 2^75*d) z ∧
      z < 29874502027490759802907 + 2^75*d := by
  have h := word_uniform_descent full_word_86
    (show 4672372488552730348277 < 29874502027490759802907 by norm_num)
    (show 3^word_86.length < 2^word_86.sum by norm_num [word_86, sharedPrefix, suffix_86]) d
  simpa [word_sum_86] using h

/-- Certificate 87; shared prefix plus independently witnessed suffix. -/
def suffix_87 : List Nat := [2, 1, 1, 1, 9]
def word_87 : List Nat := sharedPrefix ++ suffix_87
theorem suffix_proof_87 : Word suffix_87 264161755099372179061097 3917926421456752899893 := by
  unfold suffix_87
  exact Word.cons
        (show ExactStep 264161755099372179061097 198121316324529134295823 2 from by
          refine ⟨by norm_num, ⟨132080877549686089530548, by norm_num⟩, by norm_num, ⟨99060658162264567147911, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 198121316324529134295823 297181974486793701443735 1 from by
          refine ⟨by norm_num, ⟨99060658162264567147911, by norm_num⟩, by norm_num, ⟨148590987243396850721867, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 297181974486793701443735 445772961730190552165603 1 from by
          refine ⟨by norm_num, ⟨148590987243396850721867, by norm_num⟩, by norm_num, ⟨222886480865095276082801, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 445772961730190552165603 668659442595285828248405 1 from by
          refine ⟨by norm_num, ⟨222886480865095276082801, by norm_num⟩, by norm_num, ⟨334329721297642914124202, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 668659442595285828248405 3917926421456752899893 9 from by
          refine ⟨by norm_num, ⟨334329721297642914124202, by norm_num⟩, by norm_num, ⟨1958963210728376449946, by norm_num⟩⟩)
        (Word.nil 3917926421456752899893)))))
theorem full_word_87 : Word word_87 6262669613142533734427 3917926421456752899893 := by
  unfold word_87
  have hp := shared_prefix_all 10864
  have ht := suffix_proof_87
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_87 : word_87.length = 45 := by decide
theorem word_sum_87 : word_87.sum = 72 := by decide
theorem infinite_family_87 (d : Nat) :
    ∃ z : Nat, Word word_87 (6262669613142533734427 + 2^73*d) z ∧
      z < 6262669613142533734427 + 2^73*d := by
  have h := word_uniform_descent full_word_87
    (show 3917926421456752899893 < 6262669613142533734427 by norm_num)
    (show 3^word_87.length < 2^word_87.sum by norm_num [word_87, sharedPrefix, suffix_87]) d
  simpa [word_sum_87] using h

/-- Certificate 88; shared prefix plus independently witnessed suffix. -/
def suffix_88 : List Nat := [2, 1, 1, 1, 8, 3]
def word_88 : List Nat := sharedPrefix ++ suffix_88
theorem suffix_proof_88 : Word suffix_88 363757350539966539798889 4046312081049127311911 := by
  unfold suffix_88
  exact Word.cons
        (show ExactStep 363757350539966539798889 272818012904974904849167 2 from by
          refine ⟨by norm_num, ⟨181878675269983269899444, by norm_num⟩, by norm_num, ⟨136409006452487452424583, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 272818012904974904849167 409227019357462357273751 1 from by
          refine ⟨by norm_num, ⟨136409006452487452424583, by norm_num⟩, by norm_num, ⟨204613509678731178636875, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 409227019357462357273751 613840529036193535910627 1 from by
          refine ⟨by norm_num, ⟨204613509678731178636875, by norm_num⟩, by norm_num, ⟨306920264518096767955313, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 613840529036193535910627 920760793554290303865941 1 from by
          refine ⟨by norm_num, ⟨306920264518096767955313, by norm_num⟩, by norm_num, ⟨460380396777145151932970, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 920760793554290303865941 10790165549464339498429 8 from by
          refine ⟨by norm_num, ⟨460380396777145151932970, by norm_num⟩, by norm_num, ⟨5395082774732169749214, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 10790165549464339498429 4046312081049127311911 3 from by
          refine ⟨by norm_num, ⟨5395082774732169749214, by norm_num⟩, by norm_num, ⟨2023156040524563655955, by norm_num⟩⟩)
        (Word.nil 4046312081049127311911))))))
theorem full_word_88 : Word word_88 8623852854577356341275 4046312081049127311911 := by
  unfold word_88
  have hp := shared_prefix_all 14960
  have ht := suffix_proof_88
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_88 : word_88.length = 46 := by decide
theorem word_sum_88 : word_88.sum = 74 := by decide
theorem infinite_family_88 (d : Nat) :
    ∃ z : Nat, Word word_88 (8623852854577356341275 + 2^75*d) z ∧
      z < 8623852854577356341275 + 2^75*d := by
  have h := word_uniform_descent full_word_88
    (show 4046312081049127311911 < 8623852854577356341275 by norm_num)
    (show 3^word_88.length < 2^word_88.sum by norm_num [word_88, sharedPrefix, suffix_88]) d
  simpa [word_sum_88] using h

/-- Certificate 89; shared prefix plus independently witnessed suffix. -/
def suffix_89 : List Nat := [2, 1, 1, 1, 8, 2]
def word_89 : List Nat := sharedPrefix ++ suffix_89
theorem suffix_proof_89 : Word suffix_89 762139732302343982750057 16955562281750755719751 := by
  unfold suffix_89
  exact Word.cons
        (show ExactStep 762139732302343982750057 571604799226757987062543 2 from by
          refine ⟨by norm_num, ⟨381069866151171991375028, by norm_num⟩, by norm_num, ⟨285802399613378993531271, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 571604799226757987062543 857407198840136980593815 1 from by
          refine ⟨by norm_num, ⟨285802399613378993531271, by norm_num⟩, by norm_num, ⟨428703599420068490296907, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 857407198840136980593815 1286110798260205470890723 1 from by
          refine ⟨by norm_num, ⟨428703599420068490296907, by norm_num⟩, by norm_num, ⟨643055399130102735445361, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1286110798260205470890723 1929166197390308206336085 1 from by
          refine ⟨by norm_num, ⟨643055399130102735445361, by norm_num⟩, by norm_num, ⟨964583098695154103168042, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1929166197390308206336085 22607416375667674293001 8 from by
          refine ⟨by norm_num, ⟨964583098695154103168042, by norm_num⟩, by norm_num, ⟨11303708187833837146500, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 22607416375667674293001 16955562281750755719751 2 from by
          refine ⟨by norm_num, ⟨11303708187833837146500, by norm_num⟩, by norm_num, ⟨8477781140875377859875, by norm_num⟩⟩)
        (Word.nil 16955562281750755719751))))))
theorem full_word_89 : Word word_89 18068585820316646768667 16955562281750755719751 := by
  unfold word_89
  have hp := shared_prefix_all 31344
  have ht := suffix_proof_89
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_89 : word_89.length = 46 := by decide
theorem word_sum_89 : word_89.sum = 73 := by decide
theorem infinite_family_89 (d : Nat) :
    ∃ z : Nat, Word word_89 (18068585820316646768667 + 2^74*d) z ∧
      z < 18068585820316646768667 + 2^74*d := by
  have h := word_uniform_descent full_word_89
    (show 16955562281750755719751 < 18068585820316646768667 by norm_num)
    (show 3^word_89.length < 2^word_89.sum by norm_num [word_89, sharedPrefix, suffix_89]) d
  simpa [word_sum_89] using h

/-- Certificate 90; shared prefix plus independently witnessed suffix. -/
def suffix_90 : List Nat := [2, 1, 1, 1, 6, 5]
def word_90 : List Nat := sharedPrefix ++ suffix_90
theorem suffix_proof_90 : Word suffix_90 1036027619763978474778985 11524416119505925111601 := by
  unfold suffix_90
  exact Word.cons
        (show ExactStep 1036027619763978474778985 777020714822983856084239 2 from by
          refine ⟨by norm_num, ⟨518013809881989237389492, by norm_num⟩, by norm_num, ⟨388510357411491928042119, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 777020714822983856084239 1165531072234475784126359 1 from by
          refine ⟨by norm_num, ⟨388510357411491928042119, by norm_num⟩, by norm_num, ⟨582765536117237892063179, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1165531072234475784126359 1748296608351713676189539 1 from by
          refine ⟨by norm_num, ⟨582765536117237892063179, by norm_num⟩, by norm_num, ⟨874148304175856838094769, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1748296608351713676189539 2622444912527570514284309 1 from by
          refine ⟨by norm_num, ⟨874148304175856838094769, by norm_num⟩, by norm_num, ⟨1311222456263785257142154, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2622444912527570514284309 122927105274729867857077 6 from by
          refine ⟨by norm_num, ⟨1311222456263785257142154, by norm_num⟩, by norm_num, ⟨61463552637364933928538, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 122927105274729867857077 11524416119505925111601 5 from by
          refine ⟨by norm_num, ⟨61463552637364933928538, by norm_num⟩, by norm_num, ⟨5762208059752962555800, by norm_num⟩⟩)
        (Word.nil 11524416119505925111601))))))
theorem full_word_90 : Word word_90 24561839734262408937499 11524416119505925111601 := by
  unfold word_90
  have hp := shared_prefix_all 42608
  have ht := suffix_proof_90
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_90 : word_90.length = 46 := by decide
theorem word_sum_90 : word_90.sum = 74 := by decide
theorem infinite_family_90 (d : Nat) :
    ∃ z : Nat, Word word_90 (24561839734262408937499 + 2^75*d) z ∧
      z < 24561839734262408937499 + 2^75*d := by
  have h := word_uniform_descent full_word_90
    (show 11524416119505925111601 < 24561839734262408937499 by norm_num)
    (show 3^word_90.length < 2^word_90.sum by norm_num [word_90, sharedPrefix, suffix_90]) d
  simpa [word_sum_90] using h

/-- Certificate 91; shared prefix plus independently witnessed suffix. -/
def suffix_91 : List Nat := [2, 1, 1, 1, 6, 4]
def word_91 : List Nat := sharedPrefix ++ suffix_91
theorem suffix_proof_91 : Word suffix_91 637645238001601031827817 14185894119359349127273 := by
  unfold suffix_91
  exact Word.cons
        (show ExactStep 637645238001601031827817 478233928501200773870863 2 from by
          refine ⟨by norm_num, ⟨318822619000800515913908, by norm_num⟩, by norm_num, ⟨239116964250600386935431, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 478233928501200773870863 717350892751801160806295 1 from by
          refine ⟨by norm_num, ⟨239116964250600386935431, by norm_num⟩, by norm_num, ⟨358675446375900580403147, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 717350892751801160806295 1076026339127701741209443 1 from by
          refine ⟨by norm_num, ⟨358675446375900580403147, by norm_num⟩, by norm_num, ⟨538013169563850870604721, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1076026339127701741209443 1614039508691552611814165 1 from by
          refine ⟨by norm_num, ⟨538013169563850870604721, by norm_num⟩, by norm_num, ⟨807019754345776305907082, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1614039508691552611814165 75658101969916528678789 6 from by
          refine ⟨by norm_num, ⟨807019754345776305907082, by norm_num⟩, by norm_num, ⟨37829050984958264339394, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 75658101969916528678789 14185894119359349127273 4 from by
          refine ⟨by norm_num, ⟨37829050984958264339394, by norm_num⟩, by norm_num, ⟨7092947059679674563636, by norm_num⟩⟩)
        (Word.nil 14185894119359349127273))))))
theorem full_word_91 : Word word_91 15117106768523118510107 14185894119359349127273 := by
  unfold word_91
  have hp := shared_prefix_all 26224
  have ht := suffix_proof_91
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_91 : word_91.length = 46 := by decide
theorem word_sum_91 : word_91.sum = 73 := by decide
theorem infinite_family_91 (d : Nat) :
    ∃ z : Nat, Word word_91 (15117106768523118510107 + 2^74*d) z ∧
      z < 15117106768523118510107 + 2^74*d := by
  have h := word_uniform_descent full_word_91
    (show 14185894119359349127273 < 15117106768523118510107 by norm_num)
    (show 3^word_91.length < 2^word_91.sum by norm_num [word_91, sharedPrefix, suffix_91]) d
  simpa [word_sum_91] using h

/-- Certificate 92; shared prefix plus independently witnessed suffix. -/
def suffix_92 : List Nat := [2, 1, 1, 1, 4, 7]
def word_92 : List Nat := sharedPrefix ++ suffix_92
theorem suffix_proof_92 : Word suffix_92 805712805307604015572841 8962473069293874013559 := by
  unfold suffix_92
  exact Word.cons
        (show ExactStep 805712805307604015572841 604284603980703011679631 2 from by
          refine ⟨by norm_num, ⟨402856402653802007786420, by norm_num⟩, by norm_num, ⟨302142301990351505839815, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 604284603980703011679631 906426905971054517519447 1 from by
          refine ⟨by norm_num, ⟨302142301990351505839815, by norm_num⟩, by norm_num, ⟨453213452985527258759723, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 906426905971054517519447 1359640358956581776279171 1 from by
          refine ⟨by norm_num, ⟨453213452985527258759723, by norm_num⟩, by norm_num, ⟨679820179478290888139585, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1359640358956581776279171 2039460538434872664418757 1 from by
          refine ⟨by norm_num, ⟨679820179478290888139585, by norm_num⟩, by norm_num, ⟨1019730269217436332209378, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2039460538434872664418757 382398850956538624578517 4 from by
          refine ⟨by norm_num, ⟨1019730269217436332209378, by norm_num⟩, by norm_num, ⟨191199425478269312289258, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 382398850956538624578517 8962473069293874013559 7 from by
          refine ⟨by norm_num, ⟨191199425478269312289258, by norm_num⟩, by norm_num, ⟨4481236534646937006779, by norm_num⟩⟩)
        (Word.nil 8962473069293874013559))))))
theorem full_word_92 : Word word_92 19101603488444381659163 8962473069293874013559 := by
  unfold word_92
  have hp := shared_prefix_all 33136
  have ht := suffix_proof_92
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_92 : word_92.length = 46 := by decide
theorem word_sum_92 : word_92.sum = 74 := by decide
theorem infinite_family_92 (d : Nat) :
    ∃ z : Nat, Word word_92 (19101603488444381659163 + 2^75*d) z ∧
      z < 19101603488444381659163 + 2^75*d := by
  have h := word_uniform_descent full_word_92
    (show 8962473069293874013559 < 19101603488444381659163 by norm_num)
    (show 3^word_92.length < 2^word_92.sum by norm_num [word_92, sharedPrefix, suffix_92]) d
  simpa [word_sum_92] using h

/-- Certificate 93; shared prefix plus independently witnessed suffix. -/
def suffix_93 : List Nat := [2, 1, 1, 1, 4, 6]
def word_93 : List Nat := sharedPrefix ++ suffix_93
theorem suffix_proof_93 : Word suffix_93 407330423545226572621673 9062008018935246931189 := by
  unfold suffix_93
  exact Word.cons
        (show ExactStep 407330423545226572621673 305497817658919929466255 2 from by
          refine ⟨by norm_num, ⟨203665211772613286310836, by norm_num⟩, by norm_num, ⟨152748908829459964733127, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 305497817658919929466255 458246726488379894199383 1 from by
          refine ⟨by norm_num, ⟨152748908829459964733127, by norm_num⟩, by norm_num, ⟨229123363244189947099691, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 458246726488379894199383 687370089732569841299075 1 from by
          refine ⟨by norm_num, ⟨229123363244189947099691, by norm_num⟩, by norm_num, ⟨343685044866284920649537, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 687370089732569841299075 1031055134598854761948613 1 from by
          refine ⟨by norm_num, ⟨343685044866284920649537, by norm_num⟩, by norm_num, ⟨515527567299427380974306, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1031055134598854761948613 193322837737285267865365 4 from by
          refine ⟨by norm_num, ⟨515527567299427380974306, by norm_num⟩, by norm_num, ⟨96661418868642633932682, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 193322837737285267865365 9062008018935246931189 6 from by
          refine ⟨by norm_num, ⟨96661418868642633932682, by norm_num⟩, by norm_num, ⟨4531004009467623465594, by norm_num⟩⟩)
        (Word.nil 9062008018935246931189))))))
theorem full_word_93 : Word word_93 9656870522705091231771 9062008018935246931189 := by
  unfold word_93
  have hp := shared_prefix_all 16752
  have ht := suffix_proof_93
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_93 : word_93.length = 46 := by decide
theorem word_sum_93 : word_93.sum = 73 := by decide
theorem infinite_family_93 (d : Nat) :
    ∃ z : Nat, Word word_93 (9656870522705091231771 + 2^74*d) z ∧
      z < 9656870522705091231771 + 2^74*d := by
  have h := word_uniform_descent full_word_93
    (show 9062008018935246931189 < 9656870522705091231771 by norm_num)
    (show 3^word_93.length < 2^word_93.sum by norm_num [word_93, sharedPrefix, suffix_93]) d
  simpa [word_sum_93] using h

/-- Certificate 94; shared prefix plus independently witnessed suffix. -/
def suffix_94 : List Nat := [2, 1, 1, 1, 3, 8]
def word_94 : List Nat := sharedPrefix ++ suffix_94
theorem suffix_proof_94 : Word suffix_94 1032915257406459901005929 11489795267476032529195 := by
  unfold suffix_94
  exact Word.cons
        (show ExactStep 1032915257406459901005929 774686443054844925754447 2 from by
          refine ⟨by norm_num, ⟨516457628703229950502964, by norm_num⟩, by norm_num, ⟨387343221527422462877223, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 774686443054844925754447 1162029664582267388631671 1 from by
          refine ⟨by norm_num, ⟨387343221527422462877223, by norm_num⟩, by norm_num, ⟨581014832291133694315835, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1162029664582267388631671 1743044496873401082947507 1 from by
          refine ⟨by norm_num, ⟨581014832291133694315835, by norm_num⟩, by norm_num, ⟨871522248436700541473753, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1743044496873401082947507 2614566745310101624421261 1 from by
          refine ⟨by norm_num, ⟨871522248436700541473753, by norm_num⟩, by norm_num, ⟨1307283372655050812210630, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2614566745310101624421261 980462529491288109157973 3 from by
          refine ⟨by norm_num, ⟨1307283372655050812210630, by norm_num⟩, by norm_num, ⟨490231264745644054578986, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 980462529491288109157973 11489795267476032529195 8 from by
          refine ⟨by norm_num, ⟨490231264745644054578986, by norm_num⟩, by norm_num, ⟨5744897633738016264597, by norm_num⟩⟩)
        (Word.nil 11489795267476032529195))))))
theorem full_word_94 : Word word_94 24488052757967570731035 11489795267476032529195 := by
  unfold word_94
  have hp := shared_prefix_all 42480
  have ht := suffix_proof_94
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_94 : word_94.length = 46 := by decide
theorem word_sum_94 : word_94.sum = 74 := by decide
theorem infinite_family_94 (d : Nat) :
    ∃ z : Nat, Word word_94 (24488052757967570731035 + 2^75*d) z ∧
      z < 24488052757967570731035 + 2^75*d := by
  have h := word_uniform_descent full_word_94
    (show 11489795267476032529195 < 24488052757967570731035 by norm_num)
    (show 3^word_94.length < 2^word_94.sum by norm_num [word_94, sharedPrefix, suffix_94]) d
  simpa [word_sum_94] using h

/-- Certificate 95; shared prefix plus independently witnessed suffix. -/
def suffix_95 : List Nat := [2, 1, 1, 1, 3, 7]
def word_95 : List Nat := sharedPrefix ++ suffix_95
theorem suffix_proof_95 : Word suffix_95 634532875644082458054761 14116652415299563962461 := by
  unfold suffix_95
  exact Word.cons
        (show ExactStep 634532875644082458054761 475899656733061843541071 2 from by
          refine ⟨by norm_num, ⟨317266437822041229027380, by norm_num⟩, by norm_num, ⟨237949828366530921770535, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 475899656733061843541071 713849485099592765311607 1 from by
          refine ⟨by norm_num, ⟨237949828366530921770535, by norm_num⟩, by norm_num, ⟨356924742549796382655803, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 713849485099592765311607 1070774227649389147967411 1 from by
          refine ⟨by norm_num, ⟨356924742549796382655803, by norm_num⟩, by norm_num, ⟨535387113824694573983705, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1070774227649389147967411 1606161341474083721951117 1 from by
          refine ⟨by norm_num, ⟨535387113824694573983705, by norm_num⟩, by norm_num, ⟨803080670737041860975558, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1606161341474083721951117 602310503052781395731669 3 from by
          refine ⟨by norm_num, ⟨803080670737041860975558, by norm_num⟩, by norm_num, ⟨301155251526390697865834, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 602310503052781395731669 14116652415299563962461 7 from by
          refine ⟨by norm_num, ⟨301155251526390697865834, by norm_num⟩, by norm_num, ⟨7058326207649781981230, by norm_num⟩⟩)
        (Word.nil 14116652415299563962461))))))
theorem full_word_95 : Word word_95 15043319792228280303643 14116652415299563962461 := by
  unfold word_95
  have hp := shared_prefix_all 26096
  have ht := suffix_proof_95
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_95 : word_95.length = 46 := by decide
theorem word_sum_95 : word_95.sum = 73 := by decide
theorem infinite_family_95 (d : Nat) :
    ∃ z : Nat, Word word_95 (15043319792228280303643 + 2^74*d) z ∧
      z < 15043319792228280303643 + 2^74*d := by
  have h := word_uniform_descent full_word_95
    (show 14116652415299563962461 < 15043319792228280303643 by norm_num)
    (show 3^word_95.length < 2^word_95.sum by norm_num [word_95, sharedPrefix, suffix_95]) d
  simpa [word_sum_95] using h

/-- Certificate 96; shared prefix plus independently witnessed suffix. -/
def suffix_96 : List Nat := [2, 1, 3, 2, 1, 7]
def word_96 : List Nat := sharedPrefix ++ suffix_96
theorem suffix_proof_96 : Word suffix_96 25093421512476731118233 279130619546440688861 := by
  unfold suffix_96
  exact Word.cons
        (show ExactStep 25093421512476731118233 18820066134357548338675 2 from by
          refine ⟨by norm_num, ⟨12546710756238365559116, by norm_num⟩, by norm_num, ⟨9410033067178774169337, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 18820066134357548338675 28230099201536322508013 1 from by
          refine ⟨by norm_num, ⟨9410033067178774169337, by norm_num⟩, by norm_num, ⟨14115049600768161254006, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 28230099201536322508013 10586287200576120940505 3 from by
          refine ⟨by norm_num, ⟨14115049600768161254006, by norm_num⟩, by norm_num, ⟨5293143600288060470252, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 10586287200576120940505 7939715400432090705379 2 from by
          refine ⟨by norm_num, ⟨5293143600288060470252, by norm_num⟩, by norm_num, ⟨3969857700216045352689, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 7939715400432090705379 11909573100648136058069 1 from by
          refine ⟨by norm_num, ⟨3969857700216045352689, by norm_num⟩, by norm_num, ⟨5954786550324068029034, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 11909573100648136058069 279130619546440688861 7 from by
          refine ⟨by norm_num, ⟨5954786550324068029034, by norm_num⟩, by norm_num, ⟨139565309773220344430, by norm_num⟩⟩)
        (Word.nil 279130619546440688861))))))
theorem full_word_96 : Word word_96 594907496495274000411 279130619546440688861 := by
  unfold word_96
  have hp := shared_prefix_all 1032
  have ht := suffix_proof_96
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_96 : word_96.length = 46 := by decide
theorem word_sum_96 : word_96.sum = 74 := by decide
theorem infinite_family_96 (d : Nat) :
    ∃ z : Nat, Word word_96 (594907496495274000411 + 2^75*d) z ∧
      z < 594907496495274000411 + 2^75*d := by
  have h := word_uniform_descent full_word_96
    (show 279130619546440688861 < 594907496495274000411 by norm_num)
    (show 3^word_96.length < 2^word_96.sum by norm_num [word_96, sharedPrefix, suffix_96]) d
  simpa [word_sum_96] using h

/-- Certificate 97; shared prefix plus independently witnessed suffix. -/
def suffix_97 : List Nat := [2, 1, 3, 2, 1, 6]
def word_97 : List Nat := sharedPrefix ++ suffix_97
theorem suffix_proof_97 : Word suffix_97 423475803274854174069401 9421199358745382473651 := by
  unfold suffix_97
  exact Word.cons
        (show ExactStep 423475803274854174069401 317606852456140630552051 2 from by
          refine ⟨by norm_num, ⟨211737901637427087034700, by norm_num⟩, by norm_num, ⟨158803426228070315276025, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 317606852456140630552051 476410278684210945828077 1 from by
          refine ⟨by norm_num, ⟨158803426228070315276025, by norm_num⟩, by norm_num, ⟨238205139342105472914038, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 476410278684210945828077 178653854506579104685529 3 from by
          refine ⟨by norm_num, ⟨238205139342105472914038, by norm_num⟩, by norm_num, ⟨89326927253289552342764, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 178653854506579104685529 133990390879934328514147 2 from by
          refine ⟨by norm_num, ⟨89326927253289552342764, by norm_num⟩, by norm_num, ⟨66995195439967164257073, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 133990390879934328514147 200985586319901492771221 1 from by
          refine ⟨by norm_num, ⟨66995195439967164257073, by norm_num⟩, by norm_num, ⟨100492793159950746385610, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 200985586319901492771221 9421199358745382473651 6 from by
          refine ⟨by norm_num, ⟨100492793159950746385610, by norm_num⟩, by norm_num, ⟨4710599679372691236825, by norm_num⟩⟩)
        (Word.nil 9421199358745382473651))))))
theorem full_word_97 : Word word_97 10039640462234564427803 9421199358745382473651 := by
  unfold word_97
  have hp := shared_prefix_all 17416
  have ht := suffix_proof_97
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_97 : word_97.length = 46 := by decide
theorem word_sum_97 : word_97.sum = 73 := by decide
theorem infinite_family_97 (d : Nat) :
    ∃ z : Nat, Word word_97 (10039640462234564427803 + 2^74*d) z ∧
      z < 10039640462234564427803 + 2^74*d := by
  have h := word_uniform_descent full_word_97
    (show 9421199358745382473651 < 10039640462234564427803 by norm_num)
    (show 3^word_97.length < 2^word_97.sum by norm_num [word_97, sharedPrefix, suffix_97]) d
  simpa [word_sum_97] using h

/-- Certificate 98; shared prefix plus independently witnessed suffix. -/
def suffix_98 : List Nat := [2, 1, 3, 2, 3, 5]
def word_98 : List Nat := sharedPrefix ++ suffix_98
theorem suffix_proof_98 : Word suffix_98 255408235968851190324377 2841073669758491786903 := by
  unfold suffix_98
  exact Word.cons
        (show ExactStep 255408235968851190324377 191556176976638392743283 2 from by
          refine ⟨by norm_num, ⟨127704117984425595162188, by norm_num⟩, by norm_num, ⟨95778088488319196371641, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 191556176976638392743283 287334265464957589114925 1 from by
          refine ⟨by norm_num, ⟨95778088488319196371641, by norm_num⟩, by norm_num, ⟨143667132732478794557462, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 287334265464957589114925 107750349549359095918097 3 from by
          refine ⟨by norm_num, ⟨143667132732478794557462, by norm_num⟩, by norm_num, ⟨53875174774679547959048, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 107750349549359095918097 80812762162019321938573 2 from by
          refine ⟨by norm_num, ⟨53875174774679547959048, by norm_num⟩, by norm_num, ⟨40406381081009660969286, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 80812762162019321938573 30304785810757245726965 3 from by
          refine ⟨by norm_num, ⟨40406381081009660969286, by norm_num⟩, by norm_num, ⟨15152392905378622863482, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 30304785810757245726965 2841073669758491786903 5 from by
          refine ⟨by norm_num, ⟨15152392905378622863482, by norm_num⟩, by norm_num, ⟨1420536834879245893451, by norm_num⟩⟩)
        (Word.nil 2841073669758491786903))))))
theorem full_word_98 : Word word_98 6055143742313301278747 2841073669758491786903 := by
  unfold word_98
  have hp := shared_prefix_all 10504
  have ht := suffix_proof_98
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_98 : word_98.length = 46 := by decide
theorem word_sum_98 : word_98.sum = 74 := by decide
theorem infinite_family_98 (d : Nat) :
    ∃ z : Nat, Word word_98 (6055143742313301278747 + 2^75*d) z ∧
      z < 6055143742313301278747 + 2^75*d := by
  have h := word_uniform_descent full_word_98
    (show 2841073669758491786903 < 6055143742313301278747 by norm_num)
    (show 3^word_98.length < 2^word_98.sum by norm_num [word_98, sharedPrefix, suffix_98]) d
  simpa [word_sum_98] using h

/-- Certificate 99; shared prefix plus independently witnessed suffix. -/
def suffix_99 : List Nat := [2, 1, 3, 2, 3, 4]
def word_99 : List Nat := sharedPrefix ++ suffix_99
theorem suffix_proof_99 : Word suffix_99 653790617731228633275545 14545085459169484669735 := by
  unfold suffix_99
  exact Word.cons
        (show ExactStep 653790617731228633275545 490342963298421474956659 2 from by
          refine ⟨by norm_num, ⟨326895308865614316637772, by norm_num⟩, by norm_num, ⟨245171481649210737478329, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 490342963298421474956659 735514444947632212434989 1 from by
          refine ⟨by norm_num, ⟨245171481649210737478329, by norm_num⟩, by norm_num, ⟨367757222473816106217494, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 735514444947632212434989 275817916855362079663121 3 from by
          refine ⟨by norm_num, ⟨367757222473816106217494, by norm_num⟩, by norm_num, ⟨137908958427681039831560, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 275817916855362079663121 206863437641521559747341 2 from by
          refine ⟨by norm_num, ⟨137908958427681039831560, by norm_num⟩, by norm_num, ⟨103431718820760779873670, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 206863437641521559747341 77573789115570584905253 3 from by
          refine ⟨by norm_num, ⟨103431718820760779873670, by norm_num⟩, by norm_num, ⟨38786894557785292452626, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 77573789115570584905253 14545085459169484669735 4 from by
          refine ⟨by norm_num, ⟨38786894557785292452626, by norm_num⟩, by norm_num, ⟨7272542729584742334867, by norm_num⟩⟩)
        (Word.nil 14545085459169484669735))))))
theorem full_word_99 : Word word_99 15499876708052591706139 14545085459169484669735 := by
  unfold word_99
  have hp := shared_prefix_all 26888
  have ht := suffix_proof_99
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_99 : word_99.length = 46 := by decide
theorem word_sum_99 : word_99.sum = 73 := by decide
theorem infinite_family_99 (d : Nat) :
    ∃ z : Nat, Word word_99 (15499876708052591706139 + 2^74*d) z ∧
      z < 15499876708052591706139 + 2^74*d := by
  have h := word_uniform_descent full_word_99
    (show 14545085459169484669735 < 15499876708052591706139 by norm_num)
    (show 3^word_99.length < 2^word_99.sum by norm_num [word_99, sharedPrefix, suffix_99]) d
  simpa [word_sum_99] using h

/-- Certificate 100; shared prefix plus independently witnessed suffix. -/
def suffix_100 : List Nat := [2, 1, 3, 2, 4, 4]
def word_100 : List Nat := sharedPrefix ++ suffix_100
theorem suffix_proof_100 : Word suffix_100 31318146227513878664345 348372323606225853673 := by
  unfold suffix_100
  exact Word.cons
        (show ExactStep 31318146227513878664345 23488609670635408998259 2 from by
          refine ⟨by norm_num, ⟨15659073113756939332172, by norm_num⟩, by norm_num, ⟨11744304835317704499129, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 23488609670635408998259 35232914505953113497389 1 from by
          refine ⟨by norm_num, ⟨11744304835317704499129, by norm_num⟩, by norm_num, ⟨17616457252976556748694, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 35232914505953113497389 13212342939732417561521 3 from by
          refine ⟨by norm_num, ⟨17616457252976556748694, by norm_num⟩, by norm_num, ⟨6606171469866208780760, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 13212342939732417561521 9909257204799313171141 2 from by
          refine ⟨by norm_num, ⟨6606171469866208780760, by norm_num⟩, by norm_num, ⟨4954628602399656585570, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 9909257204799313171141 1857985725899871219589 4 from by
          refine ⟨by norm_num, ⟨4954628602399656585570, by norm_num⟩, by norm_num, ⟨928992862949935609794, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1857985725899871219589 348372323606225853673 4 from by
          refine ⟨by norm_num, ⟨928992862949935609794, by norm_num⟩, by norm_num, ⟨174186161803112926836, by norm_num⟩⟩)
        (Word.nil 348372323606225853673))))))
theorem full_word_100 : Word word_100 742481449084950413339 348372323606225853673 := by
  unfold word_100
  have hp := shared_prefix_all 1288
  have ht := suffix_proof_100
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_100 : word_100.length = 46 := by decide
theorem word_sum_100 : word_100.sum = 74 := by decide
theorem infinite_family_100 (d : Nat) :
    ∃ z : Nat, Word word_100 (742481449084950413339 + 2^75*d) z ∧
      z < 742481449084950413339 + 2^75*d := by
  have h := word_uniform_descent full_word_100
    (show 348372323606225853673 < 742481449084950413339 by norm_num)
    (show 3^word_100.length < 2^word_100.sum by norm_num [word_100, sharedPrefix, suffix_100]) d
  simpa [word_sum_100] using h

/-- Certificate 101; shared prefix plus independently witnessed suffix. -/
def suffix_101 : List Nat := [2, 1, 3, 2, 4, 3]
def word_101 : List Nat := sharedPrefix ++ suffix_101
theorem suffix_proof_101 : Word suffix_101 429700527989891321615513 9559682766864952803275 := by
  unfold suffix_101
  exact Word.cons
        (show ExactStep 429700527989891321615513 322275395992418491211635 2 from by
          refine ⟨by norm_num, ⟨214850263994945660807756, by norm_num⟩, by norm_num, ⟨161137697996209245605817, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 322275395992418491211635 483413093988627736817453 1 from by
          refine ⟨by norm_num, ⟨161137697996209245605817, by norm_num⟩, by norm_num, ⟨241706546994313868408726, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 483413093988627736817453 181279910245735401306545 3 from by
          refine ⟨by norm_num, ⟨241706546994313868408726, by norm_num⟩, by norm_num, ⟨90639955122867700653272, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 181279910245735401306545 135959932684301550979909 2 from by
          refine ⟨by norm_num, ⟨90639955122867700653272, by norm_num⟩, by norm_num, ⟨67979966342150775489954, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 135959932684301550979909 25492487378306540808733 4 from by
          refine ⟨by norm_num, ⟨67979966342150775489954, by norm_num⟩, by norm_num, ⟨12746243689153270404366, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 25492487378306540808733 9559682766864952803275 3 from by
          refine ⟨by norm_num, ⟨12746243689153270404366, by norm_num⟩, by norm_num, ⟨4779841383432476401637, by norm_num⟩⟩)
        (Word.nil 9559682766864952803275))))))
theorem full_word_101 : Word word_101 10187214414824240840731 9559682766864952803275 := by
  unfold word_101
  have hp := shared_prefix_all 17672
  have ht := suffix_proof_101
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_101 : word_101.length = 46 := by decide
theorem word_sum_101 : word_101.sum = 73 := by decide
theorem infinite_family_101 (d : Nat) :
    ∃ z : Nat, Word word_101 (10187214414824240840731 + 2^74*d) z ∧
      z < 10187214414824240840731 + 2^74*d := by
  have h := word_uniform_descent full_word_101
    (show 9559682766864952803275 < 10187214414824240840731 by norm_num)
    (show 3^word_101.length < 2^word_101.sum by norm_num [word_101, sharedPrefix, suffix_101]) d
  simpa [word_sum_101] using h

/-- Certificate 102; shared prefix plus independently witnessed suffix. -/
def suffix_102 : List Nat := [2, 1, 3, 2, 7]
def word_102 : List Nat := sharedPrefix ++ suffix_102
theorem suffix_proof_102 : Word suffix_102 81115943947811059033241 601537304056338114779 := by
  unfold suffix_102
  exact Word.cons
        (show ExactStep 81115943947811059033241 60836957960858294274931 2 from by
          refine ⟨by norm_num, ⟨40557971973905529516620, by norm_num⟩, by norm_num, ⟨30418478980429147137465, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 60836957960858294274931 91255436941287441412397 1 from by
          refine ⟨by norm_num, ⟨30418478980429147137465, by norm_num⟩, by norm_num, ⟨45627718470643720706198, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 91255436941287441412397 34220788852982790529649 3 from by
          refine ⟨by norm_num, ⟨45627718470643720706198, by norm_num⟩, by norm_num, ⟨17110394426491395264824, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 34220788852982790529649 25665591639737092897237 2 from by
          refine ⟨by norm_num, ⟨17110394426491395264824, by norm_num⟩, by norm_num, ⟨12832795819868546448618, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 25665591639737092897237 601537304056338114779 7 from by
          refine ⟨by norm_num, ⟨12832795819868546448618, by norm_num⟩, by norm_num, ⟨300768652028169057389, by norm_num⟩⟩)
        (Word.nil 601537304056338114779)))))
theorem full_word_102 : Word word_102 1923073069802361716763 601537304056338114779 := by
  unfold word_102
  have hp := shared_prefix_all 3336
  have ht := suffix_proof_102
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_102 : word_102.length = 45 := by decide
theorem word_sum_102 : word_102.sum = 73 := by decide
theorem infinite_family_102 (d : Nat) :
    ∃ z : Nat, Word word_102 (1923073069802361716763 + 2^74*d) z ∧
      z < 1923073069802361716763 + 2^74*d := by
  have h := word_uniform_descent full_word_102
    (show 601537304056338114779 < 1923073069802361716763 by norm_num)
    (show 3^word_102.length < 2^word_102.sum by norm_num [word_102, sharedPrefix, suffix_102]) d
  simpa [word_sum_102] using h

/-- Certificate 103; shared prefix plus independently witnessed suffix. -/
def suffix_103 : List Nat := [2, 1, 3, 2, 8]
def word_103 : List Nat := sharedPrefix ++ suffix_103
theorem suffix_proof_103 : Word suffix_103 479498325710188501984409 1777925005303585906711 := by
  unfold suffix_103
  exact Word.cons
        (show ExactStep 479498325710188501984409 359623744282641376488307 2 from by
          refine ⟨by norm_num, ⟨239749162855094250992204, by norm_num⟩, by norm_num, ⟨179811872141320688244153, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 359623744282641376488307 539435616423962064732461 1 from by
          refine ⟨by norm_num, ⟨179811872141320688244153, by norm_num⟩, by norm_num, ⟨269717808211981032366230, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 539435616423962064732461 202288356158985774274673 3 from by
          refine ⟨by norm_num, ⟨269717808211981032366230, by norm_num⟩, by norm_num, ⟨101144178079492887137336, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 202288356158985774274673 151716267119239330706005 2 from by
          refine ⟨by norm_num, ⟨101144178079492887137336, by norm_num⟩, by norm_num, ⟨75858133559619665353002, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 151716267119239330706005 1777925005303585906711 8 from by
          refine ⟨by norm_num, ⟨75858133559619665353002, by norm_num⟩, by norm_num, ⟨888962502651792953355, by norm_num⟩⟩)
        (Word.nil 1777925005303585906711)))))
theorem full_word_103 : Word word_103 11367806035541652144155 1777925005303585906711 := by
  unfold word_103
  have hp := shared_prefix_all 19720
  have ht := suffix_proof_103
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_103 : word_103.length = 45 := by decide
theorem word_sum_103 : word_103.sum = 74 := by decide
theorem infinite_family_103 (d : Nat) :
    ∃ z : Nat, Word word_103 (11367806035541652144155 + 2^75*d) z ∧
      z < 11367806035541652144155 + 2^75*d := by
  have h := word_uniform_descent full_word_103
    (show 1777925005303585906711 < 11367806035541652144155 by norm_num)
    (show 3^word_103.length < 2^word_103.sum by norm_num [word_103, sharedPrefix, suffix_103]) d
  simpa [word_sum_103] using h

/-- Certificate 104; shared prefix plus independently witnessed suffix. -/
def suffix_104 : List Nat := [2, 1, 3, 2, 6]
def word_104 : List Nat := sharedPrefix ++ suffix_104
theorem suffix_proof_104 : Word suffix_104 280307134828999780508825 4157387314663509928201 := by
  unfold suffix_104
  exact Word.cons
        (show ExactStep 280307134828999780508825 210230351121749835381619 2 from by
          refine ⟨by norm_num, ⟨140153567414499890254412, by norm_num⟩, by norm_num, ⟨105115175560874917690809, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 210230351121749835381619 315345526682624753072429 1 from by
          refine ⟨by norm_num, ⟨105115175560874917690809, by norm_num⟩, by norm_num, ⟨157672763341312376536214, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 315345526682624753072429 118254572505984282402161 3 from by
          refine ⟨by norm_num, ⟨157672763341312376536214, by norm_num⟩, by norm_num, ⟨59127286252992141201080, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 118254572505984282402161 88690929379488211801621 2 from by
          refine ⟨by norm_num, ⟨59127286252992141201080, by norm_num⟩, by norm_num, ⟨44345464689744105900810, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 88690929379488211801621 4157387314663509928201 6 from by
          refine ⟨by norm_num, ⟨44345464689744105900810, by norm_num⟩, by norm_num, ⟨2078693657331754964100, by norm_num⟩⟩)
        (Word.nil 4157387314663509928201)))))
theorem full_word_104 : Word word_104 6645439552672006930459 4157387314663509928201 := by
  unfold word_104
  have hp := shared_prefix_all 11528
  have ht := suffix_proof_104
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_104 : word_104.length = 45 := by decide
theorem word_sum_104 : word_104.sum = 72 := by decide
theorem infinite_family_104 (d : Nat) :
    ∃ z : Nat, Word word_104 (6645439552672006930459 + 2^73*d) z ∧
      z < 6645439552672006930459 + 2^73*d := by
  have h := word_uniform_descent full_word_104
    (show 4157387314663509928201 < 6645439552672006930459 by norm_num)
    (show 3^word_104.length < 2^word_104.sum by norm_num [word_104, sharedPrefix, suffix_104]) d
  simpa [word_sum_104] using h

/-- Certificate 105; shared prefix plus independently witnessed suffix. -/
def suffix_105 : List Nat := [2, 1, 3, 2, 5, 3]
def word_105 : List Nat := sharedPrefix ++ suffix_105
theorem suffix_proof_105 : Word suffix_105 1176667493794349027148953 13088845870606696179071 := by
  unfold suffix_105
  exact Word.cons
        (show ExactStep 1176667493794349027148953 882500620345761770361715 2 from by
          refine ⟨by norm_num, ⟨588333746897174513574476, by norm_num⟩, by norm_num, ⟨441250310172880885180857, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 882500620345761770361715 1323750930518642655542573 1 from by
          refine ⟨by norm_num, ⟨441250310172880885180857, by norm_num⟩, by norm_num, ⟨661875465259321327771286, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1323750930518642655542573 496406598944490995828465 3 from by
          refine ⟨by norm_num, ⟨661875465259321327771286, by norm_num⟩, by norm_num, ⟨248203299472245497914232, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 496406598944490995828465 372304949208368246871349 2 from by
          refine ⟨by norm_num, ⟨248203299472245497914232, by norm_num⟩, by norm_num, ⟨186152474604184123435674, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 372304949208368246871349 34903588988284523144189 5 from by
          refine ⟨by norm_num, ⟨186152474604184123435674, by norm_num⟩, by norm_num, ⟨17451794494142261572094, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 34903588988284523144189 13088845870606696179071 3 from by
          refine ⟨by norm_num, ⟨17451794494142261572094, by norm_num⟩, by norm_num, ⟨6544422935303348089535, by norm_num⟩⟩)
        (Word.nil 13088845870606696179071))))))
theorem full_word_105 : Word word_105 27896088725585410392091 13088845870606696179071 := by
  unfold word_105
  have hp := shared_prefix_all 48392
  have ht := suffix_proof_105
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_105 : word_105.length = 46 := by decide
theorem word_sum_105 : word_105.sum = 74 := by decide
theorem infinite_family_105 (d : Nat) :
    ∃ z : Nat, Word word_105 (27896088725585410392091 + 2^75*d) z ∧
      z < 27896088725585410392091 + 2^75*d := by
  have h := word_uniform_descent full_word_105
    (show 13088845870606696179071 < 27896088725585410392091 by norm_num)
    (show 3^word_105.length < 2^word_105.sum by norm_num [word_105, sharedPrefix, suffix_105]) d
  simpa [word_sum_105] using h

/-- Certificate 106; shared prefix plus independently witnessed suffix. -/
def suffix_106 : List Nat := [2, 1, 3, 2, 5, 2]
def word_106 : List Nat := sharedPrefix ++ suffix_106
theorem suffix_proof_106 : Word suffix_106 778285112031971584197785 17314753621560891262213 := by
  unfold suffix_106
  exact Word.cons
        (show ExactStep 778285112031971584197785 583713834023978688148339 2 from by
          refine ⟨by norm_num, ⟨389142556015985792098892, by norm_num⟩, by norm_num, ⟨291856917011989344074169, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 583713834023978688148339 875570751035968032222509 1 from by
          refine ⟨by norm_num, ⟨291856917011989344074169, by norm_num⟩, by norm_num, ⟨437785375517984016111254, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 875570751035968032222509 328339031638488012083441 3 from by
          refine ⟨by norm_num, ⟨437785375517984016111254, by norm_num⟩, by norm_num, ⟨164169515819244006041720, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 328339031638488012083441 246254273728866009062581 2 from by
          refine ⟨by norm_num, ⟨164169515819244006041720, by norm_num⟩, by norm_num, ⟨123127136864433004531290, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 246254273728866009062581 23086338162081188349617 5 from by
          refine ⟨by norm_num, ⟨123127136864433004531290, by norm_num⟩, by norm_num, ⟨11543169081040594174808, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 23086338162081188349617 17314753621560891262213 2 from by
          refine ⟨by norm_num, ⟨11543169081040594174808, by norm_num⟩, by norm_num, ⟨8657376810780445631106, by norm_num⟩⟩)
        (Word.nil 17314753621560891262213))))))
theorem full_word_106 : Word word_106 18451355759846119964699 17314753621560891262213 := by
  unfold word_106
  have hp := shared_prefix_all 32008
  have ht := suffix_proof_106
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_106 : word_106.length = 46 := by decide
theorem word_sum_106 : word_106.sum = 73 := by decide
theorem infinite_family_106 (d : Nat) :
    ∃ z : Nat, Word word_106 (18451355759846119964699 + 2^74*d) z ∧
      z < 18451355759846119964699 + 2^74*d := by
  have h := word_uniform_descent full_word_106
    (show 17314753621560891262213 < 18451355759846119964699 by norm_num)
    (show 3^word_106.length < 2^word_106.sum by norm_num [word_106, sharedPrefix, suffix_106]) d
  simpa [word_sum_106] using h

/-- Certificate 107; shared prefix plus independently witnessed suffix. -/
def suffix_107 : List Nat := [2, 1, 3, 2, 2, 6]
def word_107 : List Nat := sharedPrefix ++ suffix_107
theorem suffix_proof_107 : Word suffix_107 1164218044364274732056729 12950362462487125849447 := by
  unfold suffix_107
  exact Word.cons
        (show ExactStep 1164218044364274732056729 873163533273206049042547 2 from by
          refine ⟨by norm_num, ⟨582109022182137366028364, by norm_num⟩, by norm_num, ⟨436581766636603024521273, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 873163533273206049042547 1309745299909809073563821 1 from by
          refine ⟨by norm_num, ⟨436581766636603024521273, by norm_num⟩, by norm_num, ⟨654872649954904536781910, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1309745299909809073563821 491154487466178402586433 3 from by
          refine ⟨by norm_num, ⟨654872649954904536781910, by norm_num⟩, by norm_num, ⟨245577243733089201293216, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 491154487466178402586433 368365865599633801939825 2 from by
          refine ⟨by norm_num, ⟨245577243733089201293216, by norm_num⟩, by norm_num, ⟨184182932799816900969912, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 368365865599633801939825 276274399199725351454869 2 from by
          refine ⟨by norm_num, ⟨184182932799816900969912, by norm_num⟩, by norm_num, ⟨138137199599862675727434, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 276274399199725351454869 12950362462487125849447 6 from by
          refine ⟨by norm_num, ⟨138137199599862675727434, by norm_num⟩, by norm_num, ⟨6475181231243562924723, by norm_num⟩⟩)
        (Word.nil 12950362462487125849447))))))
theorem full_word_107 : Word word_107 27600940820406057566235 12950362462487125849447 := by
  unfold word_107
  have hp := shared_prefix_all 47880
  have ht := suffix_proof_107
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_107 : word_107.length = 46 := by decide
theorem word_sum_107 : word_107.sum = 74 := by decide
theorem infinite_family_107 (d : Nat) :
    ∃ z : Nat, Word word_107 (27600940820406057566235 + 2^75*d) z ∧
      z < 27600940820406057566235 + 2^75*d := by
  have h := word_uniform_descent full_word_107
    (show 12950362462487125849447 < 27600940820406057566235 by norm_num)
    (show 3^word_107.length < 2^word_107.sum by norm_num [word_107, sharedPrefix, suffix_107]) d
  simpa [word_sum_107] using h

/-- Certificate 108; shared prefix plus independently witnessed suffix. -/
def suffix_108 : List Nat := [2, 1, 3, 2, 2, 5]
def word_108 : List Nat := sharedPrefix ++ suffix_108
theorem suffix_proof_108 : Word suffix_108 765835662601897289105561 17037786805321750602965 := by
  unfold suffix_108
  exact Word.cons
        (show ExactStep 765835662601897289105561 574376746951422966829171 2 from by
          refine ⟨by norm_num, ⟨382917831300948644552780, by norm_num⟩, by norm_num, ⟨287188373475711483414585, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 574376746951422966829171 861565120427134450243757 1 from by
          refine ⟨by norm_num, ⟨287188373475711483414585, by norm_num⟩, by norm_num, ⟨430782560213567225121878, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 861565120427134450243757 323086920160175418841409 3 from by
          refine ⟨by norm_num, ⟨430782560213567225121878, by norm_num⟩, by norm_num, ⟨161543460080087709420704, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 323086920160175418841409 242315190120131564131057 2 from by
          refine ⟨by norm_num, ⟨161543460080087709420704, by norm_num⟩, by norm_num, ⟨121157595060065782065528, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 242315190120131564131057 181736392590098673098293 2 from by
          refine ⟨by norm_num, ⟨121157595060065782065528, by norm_num⟩, by norm_num, ⟨90868196295049336549146, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 181736392590098673098293 17037786805321750602965 5 from by
          refine ⟨by norm_num, ⟨90868196295049336549146, by norm_num⟩, by norm_num, ⟨8518893402660875301482, by norm_num⟩⟩)
        (Word.nil 17037786805321750602965))))))
theorem full_word_108 : Word word_108 18156207854666767138843 17037786805321750602965 := by
  unfold word_108
  have hp := shared_prefix_all 31496
  have ht := suffix_proof_108
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_108 : word_108.length = 46 := by decide
theorem word_sum_108 : word_108.sum = 73 := by decide
theorem infinite_family_108 (d : Nat) :
    ∃ z : Nat, Word word_108 (18156207854666767138843 + 2^74*d) z ∧
      z < 18156207854666767138843 + 2^74*d := by
  have h := word_uniform_descent full_word_108
    (show 17037786805321750602965 < 18156207854666767138843 by norm_num)
    (show 3^word_108.length < 2^word_108.sum by norm_num [word_108, sharedPrefix, suffix_108]) d
  simpa [word_sum_108] using h

/-- Certificate 109; shared prefix plus independently witnessed suffix. -/
def suffix_109 : List Nat := [2, 1, 3, 4, 1, 4]
def word_109 : List Nat := sharedPrefix ++ suffix_109
theorem suffix_proof_109 : Word suffix_109 202498075891035436182425 4505038370500635772003 := by
  unfold suffix_109
  exact Word.cons
        (show ExactStep 202498075891035436182425 151873556918276577136819 2 from by
          refine ⟨by norm_num, ⟨101249037945517718091212, by norm_num⟩, by norm_num, ⟨75936778459138288568409, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 151873556918276577136819 227810335377414865705229 1 from by
          refine ⟨by norm_num, ⟨75936778459138288568409, by norm_num⟩, by norm_num, ⟨113905167688707432852614, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 227810335377414865705229 85428875766530574639461 3 from by
          refine ⟨by norm_num, ⟨113905167688707432852614, by norm_num⟩, by norm_num, ⟨42714437883265287319730, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 85428875766530574639461 16017914206224482744899 4 from by
          refine ⟨by norm_num, ⟨42714437883265287319730, by norm_num⟩, by norm_num, ⟨8008957103112241372449, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 16017914206224482744899 24026871309336724117349 1 from by
          refine ⟨by norm_num, ⟨8008957103112241372449, by norm_num⟩, by norm_num, ⟨12013435654668362058674, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 24026871309336724117349 4505038370500635772003 4 from by
          refine ⟨by norm_num, ⟨12013435654668362058674, by norm_num⟩, by norm_num, ⟨2252519185250317886001, by norm_num⟩⟩)
        (Word.nil 4505038370500635772003))))))
theorem full_word_109 : Word word_109 4800765145301051768859 4505038370500635772003 := by
  unfold word_109
  have hp := shared_prefix_all 8328
  have ht := suffix_proof_109
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_109 : word_109.length = 46 := by decide
theorem word_sum_109 : word_109.sum = 73 := by decide
theorem infinite_family_109 (d : Nat) :
    ∃ z : Nat, Word word_109 (4800765145301051768859 + 2^74*d) z ∧
      z < 4800765145301051768859 + 2^74*d := by
  have h := word_uniform_descent full_word_109
    (show 4505038370500635772003 < 4800765145301051768859 by norm_num)
    (show 3^word_109.length < 2^word_109.sum by norm_num [word_109, sharedPrefix, suffix_109]) d
  simpa [word_sum_109] using h

/-- Certificate 110; shared prefix plus independently witnessed suffix. -/
def suffix_110 : List Nat := [2, 1, 3, 4, 1, 5]
def word_110 : List Nat := sharedPrefix ++ suffix_110
theorem suffix_proof_110 : Word suffix_110 1397645221178167765035929 15546926364729069529895 := by
  unfold suffix_110
  exact Word.cons
        (show ExactStep 1397645221178167765035929 1048233915883625823776947 2 from by
          refine ⟨by norm_num, ⟨698822610589083882517964, by norm_num⟩, by norm_num, ⟨524116957941812911888473, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1048233915883625823776947 1572350873825438735665421 1 from by
          refine ⟨by norm_num, ⟨524116957941812911888473, by norm_num⟩, by norm_num, ⟨786175436912719367832710, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1572350873825438735665421 589631577684539525874533 3 from by
          refine ⟨by norm_num, ⟨786175436912719367832710, by norm_num⟩, by norm_num, ⟨294815788842269762937266, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 589631577684539525874533 110555920815851161101475 4 from by
          refine ⟨by norm_num, ⟨294815788842269762937266, by norm_num⟩, by norm_num, ⟨55277960407925580550737, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 110555920815851161101475 165833881223776741652213 1 from by
          refine ⟨by norm_num, ⟨55277960407925580550737, by norm_num⟩, by norm_num, ⟨82916940611888370826106, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 165833881223776741652213 15546926364729069529895 5 from by
          refine ⟨by norm_num, ⟨82916940611888370826106, by norm_num⟩, by norm_num, ⟨7773463182364534764947, by norm_num⟩⟩)
        (Word.nil 15546926364729069529895))))))
theorem full_word_110 : Word word_110 33134964042518923051035 15546926364729069529895 := by
  unfold word_110
  have hp := shared_prefix_all 57480
  have ht := suffix_proof_110
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_110 : word_110.length = 46 := by decide
theorem word_sum_110 : word_110.sum = 74 := by decide
theorem infinite_family_110 (d : Nat) :
    ∃ z : Nat, Word word_110 (33134964042518923051035 + 2^75*d) z ∧
      z < 33134964042518923051035 + 2^75*d := by
  have h := word_uniform_descent full_word_110
    (show 15546926364729069529895 < 33134964042518923051035 by norm_num)
    (show 3^word_110.length < 2^word_110.sum by norm_num [word_110, sharedPrefix, suffix_110]) d
  simpa [word_sum_110] using h

/-- Certificate 111; shared prefix plus independently witnessed suffix. -/
def suffix_111 : List Nat := [2, 1, 3, 4, 6]
def word_111 : List Nat := sharedPrefix ++ suffix_111
theorem suffix_proof_111 : Word suffix_111 28205783869995304891289 104583823858777757089 := by
  unfold suffix_111
  exact Word.cons
        (show ExactStep 28205783869995304891289 21154337902496478668467 2 from by
          refine ⟨by norm_num, ⟨14102891934997652445644, by norm_num⟩, by norm_num, ⟨10577168951248239334233, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 21154337902496478668467 31731506853744718002701 1 from by
          refine ⟨by norm_num, ⟨10577168951248239334233, by norm_num⟩, by norm_num, ⟨15865753426872359001350, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 31731506853744718002701 11899315070154269251013 3 from by
          refine ⟨by norm_num, ⟨15865753426872359001350, by norm_num⟩, by norm_num, ⟨5949657535077134625506, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 11899315070154269251013 2231121575653925484565 4 from by
          refine ⟨by norm_num, ⟨5949657535077134625506, by norm_num⟩, by norm_num, ⟨1115560787826962742282, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2231121575653925484565 104583823858777757089 6 from by
          refine ⟨by norm_num, ⟨1115560787826962742282, by norm_num⟩, by norm_num, ⟨52291911929388878544, by norm_num⟩⟩)
        (Word.nil 104583823858777757089)))))
theorem full_word_111 : Word word_111 668694472790112206875 104583823858777757089 := by
  unfold word_111
  have hp := shared_prefix_all 1160
  have ht := suffix_proof_111
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_111 : word_111.length = 45 := by decide
theorem word_sum_111 : word_111.sum = 74 := by decide
theorem infinite_family_111 (d : Nat) :
    ∃ z : Nat, Word word_111 (668694472790112206875 + 2^75*d) z ∧
      z < 668694472790112206875 + 2^75*d := by
  have h := word_uniform_descent full_word_111
    (show 104583823858777757089 < 668694472790112206875 by norm_num)
    (show 3^word_111.length < 2^word_111.sum by norm_num [word_111, sharedPrefix, suffix_111]) d
  simpa [word_sum_111] using h

/-- Certificate 112; shared prefix plus independently witnessed suffix. -/
def suffix_112 : List Nat := [2, 1, 3, 4, 5]
def word_112 : List Nat := sharedPrefix ++ suffix_112
theorem suffix_proof_112 : Word suffix_112 426588165632372747842457 3163480354268389212821 := by
  unfold suffix_112
  exact Word.cons
        (show ExactStep 426588165632372747842457 319941124224279560881843 2 from by
          refine ⟨by norm_num, ⟨213294082816186373921228, by norm_num⟩, by norm_num, ⟨159970562112139780440921, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 319941124224279560881843 479911686336419341322765 1 from by
          refine ⟨by norm_num, ⟨159970562112139780440921, by norm_num⟩, by norm_num, ⟨239955843168209670661382, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 479911686336419341322765 179966882376157252996037 3 from by
          refine ⟨by norm_num, ⟨239955843168209670661382, by norm_num⟩, by norm_num, ⟨89983441188078626498018, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 179966882376157252996037 33743790445529484936757 4 from by
          refine ⟨by norm_num, ⟨89983441188078626498018, by norm_num⟩, by norm_num, ⟨16871895222764742468378, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 33743790445529484936757 3163480354268389212821 5 from by
          refine ⟨by norm_num, ⟨16871895222764742468378, by norm_num⟩, by norm_num, ⟨1581740177134194606410, by norm_num⟩⟩)
        (Word.nil 3163480354268389212821)))))
theorem full_word_112 : Word word_112 10113427438529402634267 3163480354268389212821 := by
  unfold word_112
  have hp := shared_prefix_all 17544
  have ht := suffix_proof_112
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_112 : word_112.length = 45 := by decide
theorem word_sum_112 : word_112.sum = 73 := by decide
theorem infinite_family_112 (d : Nat) :
    ∃ z : Nat, Word word_112 (10113427438529402634267 + 2^74*d) z ∧
      z < 10113427438529402634267 + 2^74*d := by
  have h := word_uniform_descent full_word_112
    (show 3163480354268389212821 < 10113427438529402634267 by norm_num)
    (show 3^word_112.length < 2^word_112.sum by norm_num [word_112, sharedPrefix, suffix_112]) d
  simpa [word_sum_112] using h

/-- Certificate 113; shared prefix plus independently witnessed suffix. -/
def suffix_113 : List Nat := [2, 1, 3, 4, 4]
def word_113 : List Nat := sharedPrefix ++ suffix_113
theorem suffix_proof_113 : Word suffix_113 227396974751184026366873 3372648001985944726999 := by
  unfold suffix_113
  exact Word.cons
        (show ExactStep 227396974751184026366873 170547731063388019775155 2 from by
          refine ⟨by norm_num, ⟨113698487375592013183436, by norm_num⟩, by norm_num, ⟨85273865531694009887577, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 170547731063388019775155 255821596595082029662733 1 from by
          refine ⟨by norm_num, ⟨85273865531694009887577, by norm_num⟩, by norm_num, ⟨127910798297541014831366, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 255821596595082029662733 95933098723155761123525 3 from by
          refine ⟨by norm_num, ⟨127910798297541014831366, by norm_num⟩, by norm_num, ⟨47966549361577880561762, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 95933098723155761123525 17987456010591705210661 4 from by
          refine ⟨by norm_num, ⟨47966549361577880561762, by norm_num⟩, by norm_num, ⟨8993728005295852605330, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 17987456010591705210661 3372648001985944726999 4 from by
          refine ⟨by norm_num, ⟨8993728005295852605330, by norm_num⟩, by norm_num, ⟨1686324000992972363499, by norm_num⟩⟩)
        (Word.nil 3372648001985944726999)))))
theorem full_word_113 : Word word_113 5391060955659757420571 3372648001985944726999 := by
  unfold word_113
  have hp := shared_prefix_all 9352
  have ht := suffix_proof_113
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_113 : word_113.length = 45 := by decide
theorem word_sum_113 : word_113.sum = 72 := by decide
theorem infinite_family_113 (d : Nat) :
    ∃ z : Nat, Word word_113 (5391060955659757420571 + 2^73*d) z ∧
      z < 5391060955659757420571 + 2^73*d := by
  have h := word_uniform_descent full_word_113
    (show 3372648001985944726999 < 5391060955659757420571 by norm_num)
    (show 3^word_113.length < 2^word_113.sum by norm_num [word_113, sharedPrefix, suffix_113]) d
  simpa [word_sum_113] using h

/-- Certificate 114; shared prefix plus independently witnessed suffix. -/
def suffix_114 : List Nat := [2, 1, 3, 4, 3, 2]
def word_114 : List Nat := sharedPrefix ++ suffix_114
theorem suffix_proof_114 : Word suffix_114 326992570191778387104665 7274706532892042364481 := by
  unfold suffix_114
  exact Word.cons
        (show ExactStep 326992570191778387104665 245244427643833790328499 2 from by
          refine ⟨by norm_num, ⟨163496285095889193552332, by norm_num⟩, by norm_num, ⟨122622213821916895164249, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 245244427643833790328499 367866641465750685492749 1 from by
          refine ⟨by norm_num, ⟨122622213821916895164249, by norm_num⟩, by norm_num, ⟨183933320732875342746374, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 367866641465750685492749 137949990549656507059781 3 from by
          refine ⟨by norm_num, ⟨183933320732875342746374, by norm_num⟩, by norm_num, ⟨68974995274828253529890, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 137949990549656507059781 25865623228060595073709 4 from by
          refine ⟨by norm_num, ⟨68974995274828253529890, by norm_num⟩, by norm_num, ⟨12932811614030297536854, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 25865623228060595073709 9699608710522723152641 3 from by
          refine ⟨by norm_num, ⟨12932811614030297536854, by norm_num⟩, by norm_num, ⟨4849804355261361576320, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 9699608710522723152641 7274706532892042364481 2 from by
          refine ⟨by norm_num, ⟨4849804355261361576320, by norm_num⟩, by norm_num, ⟨3637353266446021182240, by norm_num⟩⟩)
        (Word.nil 7274706532892042364481))))))
theorem full_word_114 : Word word_114 7752244197094580027419 7274706532892042364481 := by
  unfold word_114
  have hp := shared_prefix_all 13448
  have ht := suffix_proof_114
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_114 : word_114.length = 46 := by decide
theorem word_sum_114 : word_114.sum = 73 := by decide
theorem infinite_family_114 (d : Nat) :
    ∃ z : Nat, Word word_114 (7752244197094580027419 + 2^74*d) z ∧
      z < 7752244197094580027419 + 2^74*d := by
  have h := word_uniform_descent full_word_114
    (show 7274706532892042364481 < 7752244197094580027419 by norm_num)
    (show 3^word_114.length < 2^word_114.sum by norm_num [word_114, sharedPrefix, suffix_114]) d
  simpa [word_sum_114] using h

/-- Certificate 115; shared prefix plus independently witnessed suffix. -/
def suffix_115 : List Nat := [2, 1, 3, 4, 3, 3]
def word_115 : List Nat := sharedPrefix ++ suffix_115
theorem suffix_proof_115 : Word suffix_115 725374951954155830055833 8068822326272271730205 := by
  unfold suffix_115
  exact Word.cons
        (show ExactStep 725374951954155830055833 544031213965616872541875 2 from by
          refine ⟨by norm_num, ⟨362687475977077915027916, by norm_num⟩, by norm_num, ⟨272015606982808436270937, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 544031213965616872541875 816046820948425308812813 1 from by
          refine ⟨by norm_num, ⟨272015606982808436270937, by norm_num⟩, by norm_num, ⟨408023410474212654406406, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 816046820948425308812813 306017557855659490804805 3 from by
          refine ⟨by norm_num, ⟨408023410474212654406406, by norm_num⟩, by norm_num, ⟨153008778927829745402402, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 306017557855659490804805 57378292097936154525901 4 from by
          refine ⟨by norm_num, ⟨153008778927829745402402, by norm_num⟩, by norm_num, ⟨28689146048968077262950, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 57378292097936154525901 21516859536726057947213 3 from by
          refine ⟨by norm_num, ⟨28689146048968077262950, by norm_num⟩, by norm_num, ⟨10758429768363028973606, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 21516859536726057947213 8068822326272271730205 3 from by
          refine ⟨by norm_num, ⟨10758429768363028973606, by norm_num⟩, by norm_num, ⟨4034411163136135865102, by norm_num⟩⟩)
        (Word.nil 8068822326272271730205))))))
theorem full_word_115 : Word word_115 17196977162833870454811 8068822326272271730205 := by
  unfold word_115
  have hp := shared_prefix_all 29832
  have ht := suffix_proof_115
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_115 : word_115.length = 46 := by decide
theorem word_sum_115 : word_115.sum = 74 := by decide
theorem infinite_family_115 (d : Nat) :
    ∃ z : Nat, Word word_115 (17196977162833870454811 + 2^75*d) z ∧
      z < 17196977162833870454811 + 2^75*d := by
  have h := word_uniform_descent full_word_115
    (show 8068822326272271730205 < 17196977162833870454811 by norm_num)
    (show 3^word_115.length < 2^word_115.sum by norm_num [word_115, sharedPrefix, suffix_115]) d
  simpa [word_sum_115] using h

/-- Certificate 116; shared prefix plus independently witnessed suffix. -/
def suffix_116 : List Nat := [2, 1, 3, 4, 2, 4]
def word_116 : List Nat := sharedPrefix ++ suffix_116
theorem suffix_proof_116 : Word suffix_116 1173555131436830453375897 13054225018576803596665 := by
  unfold suffix_116
  exact Word.cons
        (show ExactStep 1173555131436830453375897 880166348577622840031923 2 from by
          refine ⟨by norm_num, ⟨586777565718415226687948, by norm_num⟩, by norm_num, ⟨440083174288811420015961, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 880166348577622840031923 1320249522866434260047885 1 from by
          refine ⟨by norm_num, ⟨440083174288811420015961, by norm_num⟩, by norm_num, ⟨660124761433217130023942, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1320249522866434260047885 495093571074912847517957 3 from by
          refine ⟨by norm_num, ⟨660124761433217130023942, by norm_num⟩, by norm_num, ⟨247546785537456423758978, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 495093571074912847517957 92830044576546158909617 4 from by
          refine ⟨by norm_num, ⟨247546785537456423758978, by norm_num⟩, by norm_num, ⟨46415022288273079454808, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 92830044576546158909617 69622533432409619182213 2 from by
          refine ⟨by norm_num, ⟨46415022288273079454808, by norm_num⟩, by norm_num, ⟨34811266716204809591106, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 69622533432409619182213 13054225018576803596665 4 from by
          refine ⟨by norm_num, ⟨34811266716204809591106, by norm_num⟩, by norm_num, ⟨6527112509288401798332, by norm_num⟩⟩)
        (Word.nil 13054225018576803596665))))))
theorem full_word_116 : Word word_116 27822301749290572185627 13054225018576803596665 := by
  unfold word_116
  have hp := shared_prefix_all 48264
  have ht := suffix_proof_116
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_116 : word_116.length = 46 := by decide
theorem word_sum_116 : word_116.sum = 74 := by decide
theorem infinite_family_116 (d : Nat) :
    ∃ z : Nat, Word word_116 (27822301749290572185627 + 2^75*d) z ∧
      z < 27822301749290572185627 + 2^75*d := by
  have h := word_uniform_descent full_word_116
    (show 13054225018576803596665 < 27822301749290572185627 by norm_num)
    (show 3^word_116.length < 2^word_116.sum by norm_num [word_116, sharedPrefix, suffix_116]) d
  simpa [word_sum_116] using h

/-- Certificate 117; shared prefix plus independently witnessed suffix. -/
def suffix_117 : List Nat := [2, 1, 3, 4, 2, 3]
def word_117 : List Nat := sharedPrefix ++ suffix_117
theorem suffix_proof_117 : Word suffix_117 775172749674453010424729 17245511917501106097401 := by
  unfold suffix_117
  exact Word.cons
        (show ExactStep 775172749674453010424729 581379562255839757818547 2 from by
          refine ⟨by norm_num, ⟨387586374837226505212364, by norm_num⟩, by norm_num, ⟨290689781127919878909273, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 581379562255839757818547 872069343383759636727821 1 from by
          refine ⟨by norm_num, ⟨290689781127919878909273, by norm_num⟩, by norm_num, ⟨436034671691879818363910, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 872069343383759636727821 327026003768909863772933 3 from by
          refine ⟨by norm_num, ⟨436034671691879818363910, by norm_num⟩, by norm_num, ⟨163513001884454931886466, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 327026003768909863772933 61317375706670599457425 4 from by
          refine ⟨by norm_num, ⟨163513001884454931886466, by norm_num⟩, by norm_num, ⟨30658687853335299728712, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 61317375706670599457425 45988031780002949593069 2 from by
          refine ⟨by norm_num, ⟨30658687853335299728712, by norm_num⟩, by norm_num, ⟨22994015890001474796534, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 45988031780002949593069 17245511917501106097401 3 from by
          refine ⟨by norm_num, ⟨22994015890001474796534, by norm_num⟩, by norm_num, ⟨8622755958750553048700, by norm_num⟩⟩)
        (Word.nil 17245511917501106097401))))))
theorem full_word_117 : Word word_117 18377568783551281758235 17245511917501106097401 := by
  unfold word_117
  have hp := shared_prefix_all 31880
  have ht := suffix_proof_117
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_117 : word_117.length = 46 := by decide
theorem word_sum_117 : word_117.sum = 73 := by decide
theorem infinite_family_117 (d : Nat) :
    ∃ z : Nat, Word word_117 (18377568783551281758235 + 2^74*d) z ∧
      z < 18377568783551281758235 + 2^74*d := by
  have h := word_uniform_descent full_word_117
    (show 17245511917501106097401 < 18377568783551281758235 by norm_num)
    (show 3^word_117.length < 2^word_117.sum by norm_num [word_117, sharedPrefix, suffix_117]) d
  simpa [word_sum_117] using h

/-- Certificate 118; shared prefix plus independently witnessed suffix. -/
def suffix_118 : List Nat := [2, 1, 3, 6]
def word_118 : List Nat := sharedPrefix ++ suffix_118
theorem suffix_proof_118 : Word suffix_118 15756334439921009799065 311587668367578562921 := by
  unfold suffix_118
  exact Word.cons
        (show ExactStep 15756334439921009799065 11817250829940757349299 2 from by
          refine ⟨by norm_num, ⟨7878167219960504899532, by norm_num⟩, by norm_num, ⟨5908625414970378674649, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 11817250829940757349299 17725876244911136023949 1 from by
          refine ⟨by norm_num, ⟨5908625414970378674649, by norm_num⟩, by norm_num, ⟨8862938122455568011974, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 17725876244911136023949 6647203591841676008981 3 from by
          refine ⟨by norm_num, ⟨8862938122455568011974, by norm_num⟩, by norm_num, ⟨3323601795920838004490, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 6647203591841676008981 311587668367578562921 6 from by
          refine ⟨by norm_num, ⟨3323601795920838004490, by norm_num⟩, by norm_num, ⟨155793834183789281460, by norm_num⟩⟩)
        (Word.nil 311587668367578562921))))
theorem full_word_118 : Word word_118 373546567610759381019 311587668367578562921 := by
  unfold word_118
  have hp := shared_prefix_all 648
  have ht := suffix_proof_118
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_118 : word_118.length = 44 := by decide
theorem word_sum_118 : word_118.sum = 70 := by decide
theorem infinite_family_118 (d : Nat) :
    ∃ z : Nat, Word word_118 (373546567610759381019 + 2^71*d) z ∧
      z < 373546567610759381019 + 2^71*d := by
  have h := word_uniform_descent full_word_118
    (show 311587668367578562921 < 373546567610759381019 by norm_num)
    (show 3^word_118.length < 2^word_118.sum by norm_num [word_118, sharedPrefix, suffix_118]) d
  simpa [word_sum_118] using h

/-- Certificate 119; shared prefix plus independently witnessed suffix. -/
def suffix_119 : List Nat := [2, 1, 3, 7]
def word_119 : List Nat := sharedPrefix ++ suffix_119
theorem suffix_proof_119 : Word suffix_119 65554132160218190167961 648179285275594897901 := by
  unfold suffix_119
  exact Word.cons
        (show ExactStep 65554132160218190167961 49165599120163642625971 2 from by
          refine ⟨by norm_num, ⟨32777066080109095083980, by norm_num⟩, by norm_num, ⟨24582799560081821312985, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 49165599120163642625971 73748398680245463938957 1 from by
          refine ⟨by norm_num, ⟨24582799560081821312985, by norm_num⟩, by norm_num, ⟨36874199340122731969478, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 73748398680245463938957 27655649505092048977109 3 from by
          refine ⟨by norm_num, ⟨36874199340122731969478, by norm_num⟩, by norm_num, ⟨13827824752546024488554, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 27655649505092048977109 648179285275594897901 7 from by
          refine ⟨by norm_num, ⟨13827824752546024488554, by norm_num⟩, by norm_num, ⟨324089642637797448950, by norm_num⟩⟩)
        (Word.nil 648179285275594897901))))
theorem full_word_119 : Word word_119 1554138188328170684443 648179285275594897901 := by
  unfold word_119
  have hp := shared_prefix_all 2696
  have ht := suffix_proof_119
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_119 : word_119.length = 44 := by decide
theorem word_sum_119 : word_119.sum = 71 := by decide
theorem infinite_family_119 (d : Nat) :
    ∃ z : Nat, Word word_119 (1554138188328170684443 + 2^72*d) z ∧
      z < 1554138188328170684443 + 2^72*d := by
  have h := word_uniform_descent full_word_119
    (show 648179285275594897901 < 1554138188328170684443 by norm_num)
    (show 3^word_119.length < 2^word_119.sum by norm_num [word_119, sharedPrefix, suffix_119]) d
  simpa [word_sum_119] using h

/-- Certificate 120; shared prefix plus independently witnessed suffix. -/
def suffix_120 : List Nat := [2, 1, 3, 8]
def word_120 : List Nat := sharedPrefix ++ suffix_120
theorem suffix_proof_120 : Word suffix_120 165149727600812550905753 816475093729603065391 := by
  unfold suffix_120
  exact Word.cons
        (show ExactStep 165149727600812550905753 123862295700609413179315 2 from by
          refine ⟨by norm_num, ⟨82574863800406275452876, by norm_num⟩, by norm_num, ⟨61931147850304706589657, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 123862295700609413179315 185793443550914119768973 1 from by
          refine ⟨by norm_num, ⟨61931147850304706589657, by norm_num⟩, by norm_num, ⟨92896721775457059884486, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 185793443550914119768973 69672541331592794913365 3 from by
          refine ⟨by norm_num, ⟨92896721775457059884486, by norm_num⟩, by norm_num, ⟨34836270665796397456682, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 69672541331592794913365 816475093729603065391 8 from by
          refine ⟨by norm_num, ⟨34836270665796397456682, by norm_num⟩, by norm_num, ⟨408237546864801532695, by norm_num⟩⟩)
        (Word.nil 816475093729603065391))))
theorem full_word_120 : Word word_120 3915321429762993291291 816475093729603065391 := by
  unfold word_120
  have hp := shared_prefix_all 6792
  have ht := suffix_proof_120
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_120 : word_120.length = 44 := by decide
theorem word_sum_120 : word_120.sum = 72 := by decide
theorem infinite_family_120 (d : Nat) :
    ∃ z : Nat, Word word_120 (3915321429762993291291 + 2^73*d) z ∧
      z < 3915321429762993291291 + 2^73*d := by
  have h := word_uniform_descent full_word_120
    (show 816475093729603065391 < 3915321429762993291291 by norm_num)
    (show 3^word_120.length < 2^word_120.sum by norm_num [word_120, sharedPrefix, suffix_120]) d
  simpa [word_sum_120] using h

/-- Certificate 121; shared prefix plus independently witnessed suffix. -/
def suffix_121 : List Nat := [2, 1, 3, 10]
def word_121 : List Nat := sharedPrefix ++ suffix_121
theorem suffix_proof_121 : Word suffix_121 1161105682006756158283673 1435082401161914807449 := by
  unfold suffix_121
  exact Word.cons
        (show ExactStep 1161105682006756158283673 870829261505067118712755 2 from by
          refine ⟨by norm_num, ⟨580552841003378079141836, by norm_num⟩, by norm_num, ⟨435414630752533559356377, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 870829261505067118712755 1306243892257600678069133 1 from by
          refine ⟨by norm_num, ⟨435414630752533559356377, by norm_num⟩, by norm_num, ⟨653121946128800339034566, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1306243892257600678069133 489841459596600254275925 3 from by
          refine ⟨by norm_num, ⟨653121946128800339034566, by norm_num⟩, by norm_num, ⟨244920729798300127137962, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 489841459596600254275925 1435082401161914807449 10 from by
          refine ⟨by norm_num, ⟨244920729798300127137962, by norm_num⟩, by norm_num, ⟨717541200580957403724, by norm_num⟩⟩)
        (Word.nil 1435082401161914807449))))
theorem full_word_121 : Word word_121 27527153844111219359771 1435082401161914807449 := by
  unfold word_121
  have hp := shared_prefix_all 47752
  have ht := suffix_proof_121
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_121 : word_121.length = 44 := by decide
theorem word_sum_121 : word_121.sum = 74 := by decide
theorem infinite_family_121 (d : Nat) :
    ∃ z : Nat, Word word_121 (27527153844111219359771 + 2^75*d) z ∧
      z < 27527153844111219359771 + 2^75*d := by
  have h := word_uniform_descent full_word_121
    (show 1435082401161914807449 < 27527153844111219359771 by norm_num)
    (show 3^word_121.length < 2^word_121.sum by norm_num [word_121, sharedPrefix, suffix_121]) d
  simpa [word_sum_121] using h

/-- Certificate 122; shared prefix plus independently witnessed suffix. -/
def suffix_122 : List Nat := [2, 1, 3, 9]
def word_122 : List Nat := sharedPrefix ++ suffix_122
theorem suffix_proof_122 : Word suffix_122 762723300244378715332505 1885393900140218382017 := by
  unfold suffix_122
  exact Word.cons
        (show ExactStep 762723300244378715332505 572042475183284036499379 2 from by
          refine ⟨by norm_num, ⟨381361650122189357666252, by norm_num⟩, by norm_num, ⟨286021237591642018249689, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 572042475183284036499379 858063712774926054749069 1 from by
          refine ⟨by norm_num, ⟨286021237591642018249689, by norm_num⟩, by norm_num, ⟨429031856387463027374534, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 858063712774926054749069 321773892290597270530901 3 from by
          refine ⟨by norm_num, ⟨429031856387463027374534, by norm_num⟩, by norm_num, ⟨160886946145298635265450, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 321773892290597270530901 1885393900140218382017 9 from by
          refine ⟨by norm_num, ⟨160886946145298635265450, by norm_num⟩, by norm_num, ⟨942696950070109191008, by norm_num⟩⟩)
        (Word.nil 1885393900140218382017))))
theorem full_word_122 : Word word_122 18082420878371928932379 1885393900140218382017 := by
  unfold word_122
  have hp := shared_prefix_all 31368
  have ht := suffix_proof_122
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_122 : word_122.length = 44 := by decide
theorem word_sum_122 : word_122.sum = 73 := by decide
theorem infinite_family_122 (d : Nat) :
    ∃ z : Nat, Word word_122 (18082420878371928932379 + 2^74*d) z ∧
      z < 18082420878371928932379 + 2^74*d := by
  have h := word_uniform_descent full_word_122
    (show 1885393900140218382017 < 18082420878371928932379 by norm_num)
    (show 3^word_122.length < 2^word_122.sum by norm_num [word_122, sharedPrefix, suffix_122]) d
  simpa [word_sum_122] using h

/-- Certificate 123; shared prefix plus independently witnessed suffix. -/
def suffix_123 : List Nat := [2, 1, 3, 5, 1, 4]
def word_123 : List Nat := sharedPrefix ++ suffix_123
theorem suffix_proof_123 : Word suffix_123 40655233300069599983513 452234879695903600891 := by
  unfold suffix_123
  exact Word.cons
        (show ExactStep 40655233300069599983513 30491424975052199987635 2 from by
          refine ⟨by norm_num, ⟨20327616650034799991756, by norm_num⟩, by norm_num, ⟨15245712487526099993817, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 30491424975052199987635 45737137462578299981453 1 from by
          refine ⟨by norm_num, ⟨15245712487526099993817, by norm_num⟩, by norm_num, ⟨22868568731289149990726, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 45737137462578299981453 17151426548466862493045 3 from by
          refine ⟨by norm_num, ⟨22868568731289149990726, by norm_num⟩, by norm_num, ⟨8575713274233431246522, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 17151426548466862493045 1607946238918768358723 5 from by
          refine ⟨by norm_num, ⟨8575713274233431246522, by norm_num⟩, by norm_num, ⟨803973119459384179361, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1607946238918768358723 2411919358378152538085 1 from by
          refine ⟨by norm_num, ⟨803973119459384179361, by norm_num⟩, by norm_num, ⟨1205959679189076269042, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2411919358378152538085 452234879695903600891 4 from by
          refine ⟨by norm_num, ⟨1205959679189076269042, by norm_num⟩, by norm_num, ⟨226117439847951800445, by norm_num⟩⟩)
        (Word.nil 452234879695903600891))))))
theorem full_word_123 : Word word_123 963842377969465032731 452234879695903600891 := by
  unfold word_123
  have hp := shared_prefix_all 1672
  have ht := suffix_proof_123
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_123 : word_123.length = 46 := by decide
theorem word_sum_123 : word_123.sum = 74 := by decide
theorem infinite_family_123 (d : Nat) :
    ∃ z : Nat, Word word_123 (963842377969465032731 + 2^75*d) z ∧
      z < 963842377969465032731 + 2^75*d := by
  have h := word_uniform_descent full_word_123
    (show 452234879695903600891 < 963842377969465032731 by norm_num)
    (show 3^word_123.length < 2^word_123.sum by norm_num [word_123, sharedPrefix, suffix_123]) d
  simpa [word_sum_123] using h

/-- Certificate 124; shared prefix plus independently witnessed suffix. -/
def suffix_124 : List Nat := [2, 1, 3, 5, 1, 3]
def word_124 : List Nat := sharedPrefix ++ suffix_124
theorem suffix_proof_124 : Word suffix_124 439037615062447042934681 9767407879044308297711 := by
  unfold suffix_124
  exact Word.cons
        (show ExactStep 439037615062447042934681 329278211296835282201011 2 from by
          refine ⟨by norm_num, ⟨219518807531223521467340, by norm_num⟩, by norm_num, ⟨164639105648417641100505, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 329278211296835282201011 493917316945252923301517 1 from by
          refine ⟨by norm_num, ⟨164639105648417641100505, by norm_num⟩, by norm_num, ⟨246958658472626461650758, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 493917316945252923301517 185218993854469846238069 3 from by
          refine ⟨by norm_num, ⟨246958658472626461650758, by norm_num⟩, by norm_num, ⟨92609496927234923119034, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 185218993854469846238069 17364280673856548084819 5 from by
          refine ⟨by norm_num, ⟨92609496927234923119034, by norm_num⟩, by norm_num, ⟨8682140336928274042409, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 17364280673856548084819 26046421010784822127229 1 from by
          refine ⟨by norm_num, ⟨8682140336928274042409, by norm_num⟩, by norm_num, ⟨13023210505392411063614, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 26046421010784822127229 9767407879044308297711 3 from by
          refine ⟨by norm_num, ⟨13023210505392411063614, by norm_num⟩, by norm_num, ⟨4883703939522154148855, by norm_num⟩⟩)
        (Word.nil 9767407879044308297711))))))
theorem full_word_124 : Word word_124 10408575343708755460123 9767407879044308297711 := by
  unfold word_124
  have hp := shared_prefix_all 18056
  have ht := suffix_proof_124
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_124 : word_124.length = 46 := by decide
theorem word_sum_124 : word_124.sum = 73 := by decide
theorem infinite_family_124 (d : Nat) :
    ∃ z : Nat, Word word_124 (10408575343708755460123 + 2^74*d) z ∧
      z < 10408575343708755460123 + 2^74*d := by
  have h := word_uniform_descent full_word_124
    (show 9767407879044308297711 < 10408575343708755460123 by norm_num)
    (show 3^word_124.length < 2^word_124.sum by norm_num [word_124, sharedPrefix, suffix_124]) d
  simpa [word_sum_124] using h

/-- Certificate 125; shared prefix plus independently witnessed suffix. -/
def suffix_125 : List Nat := [2, 1, 3, 5, 4]
def word_125 : List Nat := sharedPrefix ++ suffix_125
theorem suffix_proof_125 : Word suffix_125 90453031020366780352409 670779008116123279591 := by
  unfold suffix_125
  exact Word.cons
        (show ExactStep 90453031020366780352409 67839773265275085264307 2 from by
          refine ⟨by norm_num, ⟨45226515510183390176204, by norm_num⟩, by norm_num, ⟨33919886632637542632153, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 67839773265275085264307 101759659897912627896461 1 from by
          refine ⟨by norm_num, ⟨33919886632637542632153, by norm_num⟩, by norm_num, ⟨50879829948956313948230, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 101759659897912627896461 38159872461717235461173 3 from by
          refine ⟨by norm_num, ⟨50879829948956313948230, by norm_num⟩, by norm_num, ⟨19079936230858617730586, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 38159872461717235461173 3577488043285990824485 5 from by
          refine ⟨by norm_num, ⟨19079936230858617730586, by norm_num⟩, by norm_num, ⟨1788744021642995412242, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 3577488043285990824485 670779008116123279591 4 from by
          refine ⟨by norm_num, ⟨1788744021642995412242, by norm_num⟩, by norm_num, ⟨335389504058061639795, by norm_num⟩⟩)
        (Word.nil 670779008116123279591)))))
theorem full_word_125 : Word word_125 2144433998686876336155 670779008116123279591 := by
  unfold word_125
  have hp := shared_prefix_all 3720
  have ht := suffix_proof_125
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_125 : word_125.length = 45 := by decide
theorem word_sum_125 : word_125.sum = 73 := by decide
theorem infinite_family_125 (d : Nat) :
    ∃ z : Nat, Word word_125 (2144433998686876336155 + 2^74*d) z ∧
      z < 2144433998686876336155 + 2^74*d := by
  have h := word_uniform_descent full_word_125
    (show 670779008116123279591 < 2144433998686876336155 by norm_num)
    (show 3^word_125.length < 2^word_125.sum by norm_num [word_125, sharedPrefix, suffix_125]) d
  simpa [word_sum_125] using h

/-- Certificate 126; shared prefix plus independently witnessed suffix. -/
def suffix_126 : List Nat := [2, 1, 3, 5, 5]
def word_126 : List Nat := sharedPrefix ++ suffix_126
theorem suffix_proof_126 : Word suffix_126 488835412782744223303577 1812545857333478489117 := by
  unfold suffix_126
  exact Word.cons
        (show ExactStep 488835412782744223303577 366626559587058167477683 2 from by
          refine ⟨by norm_num, ⟨244417706391372111651788, by norm_num⟩, by norm_num, ⟨183313279793529083738841, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 366626559587058167477683 549939839380587251216525 1 from by
          refine ⟨by norm_num, ⟨183313279793529083738841, by norm_num⟩, by norm_num, ⟨274969919690293625608262, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 549939839380587251216525 206227439767720219206197 3 from by
          refine ⟨by norm_num, ⟨274969919690293625608262, by norm_num⟩, by norm_num, ⟨103113719883860109603098, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 206227439767720219206197 19333822478223770550581 5 from by
          refine ⟨by norm_num, ⟨103113719883860109603098, by norm_num⟩, by norm_num, ⟨9666911239111885275290, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 19333822478223770550581 1812545857333478489117 5 from by
          refine ⟨by norm_num, ⟨9666911239111885275290, by norm_num⟩, by norm_num, ⟨906272928666739244558, by norm_num⟩⟩)
        (Word.nil 1812545857333478489117)))))
theorem full_word_126 : Word word_126 11589166964426166763547 1812545857333478489117 := by
  unfold word_126
  have hp := shared_prefix_all 20104
  have ht := suffix_proof_126
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_126 : word_126.length = 45 := by decide
theorem word_sum_126 : word_126.sum = 74 := by decide
theorem infinite_family_126 (d : Nat) :
    ∃ z : Nat, Word word_126 (11589166964426166763547 + 2^75*d) z ∧
      z < 11589166964426166763547 + 2^75*d := by
  have h := word_uniform_descent full_word_126
    (show 1812545857333478489117 < 11589166964426166763547 by norm_num)
    (show 3^word_126.length < 2^word_126.sum by norm_num [word_126, sharedPrefix, suffix_126]) d
  simpa [word_sum_126] using h

/-- Certificate 127; shared prefix plus independently witnessed suffix. -/
def suffix_127 : List Nat := [2, 1, 3, 5, 3]
def word_127 : List Nat := sharedPrefix ++ suffix_127
theorem suffix_proof_127 : Word suffix_127 289644221901555501827993 4295870722783080257825 := by
  unfold suffix_127
  exact Word.cons
        (show ExactStep 289644221901555501827993 217233166426166626370995 2 from by
          refine ⟨by norm_num, ⟨144822110950777750913996, by norm_num⟩, by norm_num, ⟨108616583213083313185497, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 217233166426166626370995 325849749639249939556493 1 from by
          refine ⟨by norm_num, ⟨108616583213083313185497, by norm_num⟩, by norm_num, ⟨162924874819624969778246, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 325849749639249939556493 122193656114718727333685 3 from by
          refine ⟨by norm_num, ⟨162924874819624969778246, by norm_num⟩, by norm_num, ⟨61096828057359363666842, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 122193656114718727333685 11455655260754880687533 5 from by
          refine ⟨by norm_num, ⟨61096828057359363666842, by norm_num⟩, by norm_num, ⟨5727827630377440343766, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 11455655260754880687533 4295870722783080257825 3 from by
          refine ⟨by norm_num, ⟨5727827630377440343766, by norm_num⟩, by norm_num, ⟨2147935361391540128912, by norm_num⟩⟩)
        (Word.nil 4295870722783080257825)))))
theorem full_word_127 : Word word_127 6866800481556521549851 4295870722783080257825 := by
  unfold word_127
  have hp := shared_prefix_all 11912
  have ht := suffix_proof_127
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_127 : word_127.length = 45 := by decide
theorem word_sum_127 : word_127.sum = 72 := by decide
theorem infinite_family_127 (d : Nat) :
    ∃ z : Nat, Word word_127 (6866800481556521549851 + 2^73*d) z ∧
      z < 6866800481556521549851 + 2^73*d := by
  have h := word_uniform_descent full_word_127
    (show 4295870722783080257825 < 6866800481556521549851 by norm_num)
    (show 3^word_127.length < 2^word_127.sum by norm_num [word_127, sharedPrefix, suffix_127]) d
  simpa [word_sum_127] using h

/-- Certificate 128; shared prefix plus independently witnessed suffix. -/
def suffix_128 : List Nat := [2, 1, 3, 5, 2, 3]
def word_128 : List Nat := sharedPrefix ++ suffix_128
theorem suffix_proof_128 : Word suffix_128 1186004580866904748468121 13192708426696373926289 := by
  unfold suffix_128
  exact Word.cons
        (show ExactStep 1186004580866904748468121 889503435650178561351091 2 from by
          refine ⟨by norm_num, ⟨593002290433452374234060, by norm_num⟩, by norm_num, ⟨444751717825089280675545, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 889503435650178561351091 1334255153475267842026637 1 from by
          refine ⟨by norm_num, ⟨444751717825089280675545, by norm_num⟩, by norm_num, ⟨667127576737633921013318, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1334255153475267842026637 500345682553225440759989 3 from by
          refine ⟨by norm_num, ⟨667127576737633921013318, by norm_num⟩, by norm_num, ⟨250172841276612720379994, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 500345682553225440759989 46907407739364885071249 5 from by
          refine ⟨by norm_num, ⟨250172841276612720379994, by norm_num⟩, by norm_num, ⟨23453703869682442535624, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 46907407739364885071249 35180555804523663803437 2 from by
          refine ⟨by norm_num, ⟨23453703869682442535624, by norm_num⟩, by norm_num, ⟨17590277902261831901718, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 35180555804523663803437 13192708426696373926289 3 from by
          refine ⟨by norm_num, ⟨17590277902261831901718, by norm_num⟩, by norm_num, ⟨6596354213348186963144, by norm_num⟩⟩)
        (Word.nil 13192708426696373926289))))))
theorem full_word_128 : Word word_128 28117449654469925011483 13192708426696373926289 := by
  unfold word_128
  have hp := shared_prefix_all 48776
  have ht := suffix_proof_128
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_128 : word_128.length = 46 := by decide
theorem word_sum_128 : word_128.sum = 74 := by decide
theorem infinite_family_128 (d : Nat) :
    ∃ z : Nat, Word word_128 (28117449654469925011483 + 2^75*d) z ∧
      z < 28117449654469925011483 + 2^75*d := by
  have h := word_uniform_descent full_word_128
    (show 13192708426696373926289 < 28117449654469925011483 by norm_num)
    (show 3^word_128.length < 2^word_128.sum by norm_num [word_128, sharedPrefix, suffix_128]) d
  simpa [word_sum_128] using h

/-- Certificate 129; shared prefix plus independently witnessed suffix. -/
def suffix_129 : List Nat := [2, 1, 3, 5, 2, 2]
def word_129 : List Nat := sharedPrefix ++ suffix_129
theorem suffix_proof_129 : Word suffix_129 787622199104527305516953 17522478733740246756649 := by
  unfold suffix_129
  exact Word.cons
        (show ExactStep 787622199104527305516953 590716649328395479137715 2 from by
          refine ⟨by norm_num, ⟨393811099552263652758476, by norm_num⟩, by norm_num, ⟨295358324664197739568857, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 590716649328395479137715 886074973992593218706573 1 from by
          refine ⟨by norm_num, ⟨295358324664197739568857, by norm_num⟩, by norm_num, ⟨443037486996296609353286, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 886074973992593218706573 332278115247222457014965 3 from by
          refine ⟨by norm_num, ⟨443037486996296609353286, by norm_num⟩, by norm_num, ⟨166139057623611228507482, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 332278115247222457014965 31151073304427105345153 5 from by
          refine ⟨by norm_num, ⟨166139057623611228507482, by norm_num⟩, by norm_num, ⟨15575536652213552672576, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 31151073304427105345153 23363304978320329008865 2 from by
          refine ⟨by norm_num, ⟨15575536652213552672576, by norm_num⟩, by norm_num, ⟨11681652489160164504432, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 23363304978320329008865 17522478733740246756649 2 from by
          refine ⟨by norm_num, ⟨11681652489160164504432, by norm_num⟩, by norm_num, ⟨8761239366870123378324, by norm_num⟩⟩)
        (Word.nil 17522478733740246756649))))))
theorem full_word_129 : Word word_129 18672716688730634584091 17522478733740246756649 := by
  unfold word_129
  have hp := shared_prefix_all 32392
  have ht := suffix_proof_129
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_129 : word_129.length = 46 := by decide
theorem word_sum_129 : word_129.sum = 73 := by decide
theorem infinite_family_129 (d : Nat) :
    ∃ z : Nat, Word word_129 (18672716688730634584091 + 2^74*d) z ∧
      z < 18672716688730634584091 + 2^74*d := by
  have h := word_uniform_descent full_word_129
    (show 17522478733740246756649 < 18672716688730634584091 by norm_num)
    (show 3^word_129.length < 2^word_129.sum by norm_num [word_129, sharedPrefix, suffix_129]) d
  simpa [word_sum_129] using h

/-- Certificate 130; shared prefix plus independently witnessed suffix. -/
def suffix_130 : List Nat := [2, 1, 3, 3, 1, 5]
def word_130 : List Nat := sharedPrefix ++ suffix_130
theorem suffix_proof_130 : Word suffix_130 84228306305329632806297 1873853616228799509149 := by
  unfold suffix_130
  exact Word.cons
        (show ExactStep 84228306305329632806297 63171229728997224604723 2 from by
          refine ⟨by norm_num, ⟨42114153152664816403148, by norm_num⟩, by norm_num, ⟨31585614864498612302361, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 63171229728997224604723 94756844593495836907085 1 from by
          refine ⟨by norm_num, ⟨31585614864498612302361, by norm_num⟩, by norm_num, ⟨47378422296747918453542, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 94756844593495836907085 35533816722560938840157 3 from by
          refine ⟨by norm_num, ⟨47378422296747918453542, by norm_num⟩, by norm_num, ⟨17766908361280469420078, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 35533816722560938840157 13325181270960352065059 3 from by
          refine ⟨by norm_num, ⟨17766908361280469420078, by norm_num⟩, by norm_num, ⟨6662590635480176032529, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 13325181270960352065059 19987771906440528097589 1 from by
          refine ⟨by norm_num, ⟨6662590635480176032529, by norm_num⟩, by norm_num, ⟨9993885953220264048794, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 19987771906440528097589 1873853616228799509149 5 from by
          refine ⟨by norm_num, ⟨9993885953220264048794, by norm_num⟩, by norm_num, ⟨936926808114399754574, by norm_num⟩⟩)
        (Word.nil 1873853616228799509149))))))
theorem full_word_130 : Word word_130 1996860046097199923227 1873853616228799509149 := by
  unfold word_130
  have hp := shared_prefix_all 3464
  have ht := suffix_proof_130
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_130 : word_130.length = 46 := by decide
theorem word_sum_130 : word_130.sum = 73 := by decide
theorem infinite_family_130 (d : Nat) :
    ∃ z : Nat, Word word_130 (1996860046097199923227 + 2^74*d) z ∧
      z < 1996860046097199923227 + 2^74*d := by
  have h := word_uniform_descent full_word_130
    (show 1873853616228799509149 < 1996860046097199923227 by norm_num)
    (show 3^word_130.length < 2^word_130.sum by norm_num [word_130, sharedPrefix, suffix_130]) d
  simpa [word_sum_130] using h

/-- Certificate 131; shared prefix plus independently witnessed suffix. -/
def suffix_131 : List Nat := [2, 1, 3, 3, 1, 6]
def word_131 : List Nat := sharedPrefix ++ suffix_131
theorem suffix_proof_131 : Word suffix_131 482610688067707075757465 5368395867940650302539 := by
  unfold suffix_131
  exact Word.cons
        (show ExactStep 482610688067707075757465 361958016050780306818099 2 from by
          refine ⟨by norm_num, ⟨241305344033853537878732, by norm_num⟩, by norm_num, ⟨180979008025390153409049, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 361958016050780306818099 542937024076170460227149 1 from by
          refine ⟨by norm_num, ⟨180979008025390153409049, by norm_num⟩, by norm_num, ⟨271468512038085230113574, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 542937024076170460227149 203601384028563922585181 3 from by
          refine ⟨by norm_num, ⟨271468512038085230113574, by norm_num⟩, by norm_num, ⟨101800692014281961292590, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 203601384028563922585181 76350519010711470969443 3 from by
          refine ⟨by norm_num, ⟨101800692014281961292590, by norm_num⟩, by norm_num, ⟨38175259505355735484721, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 76350519010711470969443 114525778516067206454165 1 from by
          refine ⟨by norm_num, ⟨38175259505355735484721, by norm_num⟩, by norm_num, ⟨57262889258033603227082, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 114525778516067206454165 5368395867940650302539 6 from by
          refine ⟨by norm_num, ⟨57262889258033603227082, by norm_num⟩, by norm_num, ⟨2684197933970325151269, by norm_num⟩⟩)
        (Word.nil 5368395867940650302539))))))
theorem full_word_131 : Word word_131 11441593011836490350619 5368395867940650302539 := by
  unfold word_131
  have hp := shared_prefix_all 19848
  have ht := suffix_proof_131
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_131 : word_131.length = 46 := by decide
theorem word_sum_131 : word_131.sum = 74 := by decide
theorem infinite_family_131 (d : Nat) :
    ∃ z : Nat, Word word_131 (11441593011836490350619 + 2^75*d) z ∧
      z < 11441593011836490350619 + 2^75*d := by
  have h := word_uniform_descent full_word_131
    (show 5368395867940650302539 < 11441593011836490350619 by norm_num)
    (show 3^word_131.length < 2^word_131.sum by norm_num [word_131, sharedPrefix, suffix_131]) d
  simpa [word_sum_131] using h

/-- Certificate 132; shared prefix plus independently witnessed suffix. -/
def suffix_132 : List Nat := [2, 1, 3, 3, 2, 5]
def word_132 : List Nat := sharedPrefix ++ suffix_132
theorem suffix_proof_132 : Word suffix_132 1167330406721793305829785 12984983314517018431853 := by
  unfold suffix_132
  exact Word.cons
        (show ExactStep 1167330406721793305829785 875497805041344979372339 2 from by
          refine ⟨by norm_num, ⟨583665203360896652914892, by norm_num⟩, by norm_num, ⟨437748902520672489686169, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 875497805041344979372339 1313246707562017469058509 1 from by
          refine ⟨by norm_num, ⟨437748902520672489686169, by norm_num⟩, by norm_num, ⟨656623353781008734529254, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1313246707562017469058509 492467515335756550896941 3 from by
          refine ⟨by norm_num, ⟨656623353781008734529254, by norm_num⟩, by norm_num, ⟨246233757667878275448470, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 492467515335756550896941 184675318250908706586353 3 from by
          refine ⟨by norm_num, ⟨246233757667878275448470, by norm_num⟩, by norm_num, ⟨92337659125454353293176, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 184675318250908706586353 138506488688181529939765 2 from by
          refine ⟨by norm_num, ⟨92337659125454353293176, by norm_num⟩, by norm_num, ⟨69253244344090764969882, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 138506488688181529939765 12984983314517018431853 5 from by
          refine ⟨by norm_num, ⟨69253244344090764969882, by norm_num⟩, by norm_num, ⟨6492491657258509215926, by norm_num⟩⟩)
        (Word.nil 12984983314517018431853))))))
theorem full_word_132 : Word word_132 27674727796700895772699 12984983314517018431853 := by
  unfold word_132
  have hp := shared_prefix_all 48008
  have ht := suffix_proof_132
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_132 : word_132.length = 46 := by decide
theorem word_sum_132 : word_132.sum = 74 := by decide
theorem infinite_family_132 (d : Nat) :
    ∃ z : Nat, Word word_132 (27674727796700895772699 + 2^75*d) z ∧
      z < 27674727796700895772699 + 2^75*d := by
  have h := word_uniform_descent full_word_132
    (show 12984983314517018431853 < 27674727796700895772699 by norm_num)
    (show 3^word_132.length < 2^word_132.sum by norm_num [word_132, sharedPrefix, suffix_132]) d
  simpa [word_sum_132] using h

/-- Certificate 133; shared prefix plus independently witnessed suffix. -/
def suffix_133 : List Nat := [2, 1, 3, 3, 2, 4]
def word_133 : List Nat := sharedPrefix ++ suffix_133
theorem suffix_proof_133 : Word suffix_133 768948024959415862878617 17107028509381535767777 := by
  unfold suffix_133
  exact Word.cons
        (show ExactStep 768948024959415862878617 576711018719561897158963 2 from by
          refine ⟨by norm_num, ⟨384474012479707931439308, by norm_num⟩, by norm_num, ⟨288355509359780948579481, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 576711018719561897158963 865066528079342845738445 1 from by
          refine ⟨by norm_num, ⟨288355509359780948579481, by norm_num⟩, by norm_num, ⟨432533264039671422869222, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 865066528079342845738445 324399948029753567151917 3 from by
          refine ⟨by norm_num, ⟨432533264039671422869222, by norm_num⟩, by norm_num, ⟨162199974014876783575958, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 324399948029753567151917 121649980511157587681969 3 from by
          refine ⟨by norm_num, ⟨162199974014876783575958, by norm_num⟩, by norm_num, ⟨60824990255578793840984, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 121649980511157587681969 91237485383368190761477 2 from by
          refine ⟨by norm_num, ⟨60824990255578793840984, by norm_num⟩, by norm_num, ⟨45618742691684095380738, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 91237485383368190761477 17107028509381535767777 4 from by
          refine ⟨by norm_num, ⟨45618742691684095380738, by norm_num⟩, by norm_num, ⟨8553514254690767883888, by norm_num⟩⟩)
        (Word.nil 17107028509381535767777))))))
theorem full_word_133 : Word word_133 18229994830961605345307 17107028509381535767777 := by
  unfold word_133
  have hp := shared_prefix_all 31624
  have ht := suffix_proof_133
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_133 : word_133.length = 46 := by decide
theorem word_sum_133 : word_133.sum = 73 := by decide
theorem infinite_family_133 (d : Nat) :
    ∃ z : Nat, Word word_133 (18229994830961605345307 + 2^74*d) z ∧
      z < 18229994830961605345307 + 2^74*d := by
  have h := word_uniform_descent full_word_133
    (show 17107028509381535767777 < 18229994830961605345307 by norm_num)
    (show 3^word_133.length < 2^word_133.sum by norm_num [word_133, sharedPrefix, suffix_133]) d
  simpa [word_sum_133] using h

/-- Certificate 134; shared prefix plus independently witnessed suffix. -/
def suffix_134 : List Nat := [2, 1, 3, 3, 3, 4]
def word_134 : List Nat := sharedPrefix ++ suffix_134
theorem suffix_proof_134 : Word suffix_134 943240316980455994169753 10492281968364752498623 := by
  unfold suffix_134
  exact Word.cons
        (show ExactStep 943240316980455994169753 707430237735341995627315 2 from by
          refine ⟨by norm_num, ⟨471620158490227997084876, by norm_num⟩, by norm_num, ⟨353715118867670997813657, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 707430237735341995627315 1061145356603012993440973 1 from by
          refine ⟨by norm_num, ⟨353715118867670997813657, by norm_num⟩, by norm_num, ⟨530572678301506496720486, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1061145356603012993440973 397929508726129872540365 3 from by
          refine ⟨by norm_num, ⟨530572678301506496720486, by norm_num⟩, by norm_num, ⟨198964754363064936270182, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 397929508726129872540365 149223565772298702202637 3 from by
          refine ⟨by norm_num, ⟨198964754363064936270182, by norm_num⟩, by norm_num, ⟨74611782886149351101318, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 149223565772298702202637 55958837164612013325989 3 from by
          refine ⟨by norm_num, ⟨74611782886149351101318, by norm_num⟩, by norm_num, ⟨27979418582306006662994, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 55958837164612013325989 10492281968364752498623 4 from by
          refine ⟨by norm_num, ⟨27979418582306006662994, by norm_num⟩, by norm_num, ⟨5246140984182376249311, by norm_num⟩⟩)
        (Word.nil 10492281968364752498623))))))
theorem full_word_134 : Word word_134 22362065503472544907291 10492281968364752498623 := by
  unfold word_134
  have hp := shared_prefix_all 38792
  have ht := suffix_proof_134
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_134 : word_134.length = 46 := by decide
theorem word_sum_134 : word_134.sum = 74 := by decide
theorem infinite_family_134 (d : Nat) :
    ∃ z : Nat, Word word_134 (22362065503472544907291 + 2^75*d) z ∧
      z < 22362065503472544907291 + 2^75*d := by
  have h := word_uniform_descent full_word_134
    (show 10492281968364752498623 < 22362065503472544907291 by norm_num)
    (show 3^word_134.length < 2^word_134.sum by norm_num [word_134, sharedPrefix, suffix_134]) d
  simpa [word_sum_134] using h

/-- Certificate 135; shared prefix plus independently witnessed suffix. -/
def suffix_135 : List Nat := [2, 1, 3, 3, 3, 3]
def word_135 : List Nat := sharedPrefix ++ suffix_135
theorem suffix_proof_135 : Word suffix_135 544857935218078551218585 12121625817077003901317 := by
  unfold suffix_135
  exact Word.cons
        (show ExactStep 544857935218078551218585 408643451413558913413939 2 from by
          refine ⟨by norm_num, ⟨272428967609039275609292, by norm_num⟩, by norm_num, ⟨204321725706779456706969, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 408643451413558913413939 612965177120338370120909 1 from by
          refine ⟨by norm_num, ⟨204321725706779456706969, by norm_num⟩, by norm_num, ⟨306482588560169185060454, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 612965177120338370120909 229861941420126888795341 3 from by
          refine ⟨by norm_num, ⟨306482588560169185060454, by norm_num⟩, by norm_num, ⟨114930970710063444397670, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 229861941420126888795341 86198228032547583298253 3 from by
          refine ⟨by norm_num, ⟨114930970710063444397670, by norm_num⟩, by norm_num, ⟨43099114016273791649126, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 86198228032547583298253 32324335512205343736845 3 from by
          refine ⟨by norm_num, ⟨43099114016273791649126, by norm_num⟩, by norm_num, ⟨16162167756102671868422, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 32324335512205343736845 12121625817077003901317 3 from by
          refine ⟨by norm_num, ⟨16162167756102671868422, by norm_num⟩, by norm_num, ⟨6060812908538501950658, by norm_num⟩⟩)
        (Word.nil 12121625817077003901317))))))
theorem full_word_135 : Word word_135 12917332537733254479899 12121625817077003901317 := by
  unfold word_135
  have hp := shared_prefix_all 22408
  have ht := suffix_proof_135
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_135 : word_135.length = 46 := by decide
theorem word_sum_135 : word_135.sum = 73 := by decide
theorem infinite_family_135 (d : Nat) :
    ∃ z : Nat, Word word_135 (12917332537733254479899 + 2^74*d) z ∧
      z < 12917332537733254479899 + 2^74*d := by
  have h := word_uniform_descent full_word_135
    (show 12121625817077003901317 < 12917332537733254479899 by norm_num)
    (show 3^word_135.length < 2^word_135.sum by norm_num [word_135, sharedPrefix, suffix_135]) d
  simpa [word_sum_135] using h

/-- Certificate 136; shared prefix plus independently witnessed suffix. -/
def suffix_136 : List Nat := [2, 1, 3, 3, 4, 2]
def word_136 : List Nat := sharedPrefix ++ suffix_136
theorem suffix_proof_136 : Word suffix_136 96677755735403927898521 2150820432467940168397 := by
  unfold suffix_136
  exact Word.cons
        (show ExactStep 96677755735403927898521 72508316801552945923891 2 from by
          refine ⟨by norm_num, ⟨48338877867701963949260, by norm_num⟩, by norm_num, ⟨36254158400776472961945, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 72508316801552945923891 108762475202329418885837 1 from by
          refine ⟨by norm_num, ⟨36254158400776472961945, by norm_num⟩, by norm_num, ⟨54381237601164709442918, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 108762475202329418885837 40785928200873532082189 3 from by
          refine ⟨by norm_num, ⟨54381237601164709442918, by norm_num⟩, by norm_num, ⟨20392964100436766041094, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 40785928200873532082189 15294723075327574530821 3 from by
          refine ⟨by norm_num, ⟨20392964100436766041094, by norm_num⟩, by norm_num, ⟨7647361537663787265410, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 15294723075327574530821 2867760576623920224529 4 from by
          refine ⟨by norm_num, ⟨7647361537663787265410, by norm_num⟩, by norm_num, ⟨1433880288311960112264, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2867760576623920224529 2150820432467940168397 2 from by
          refine ⟨by norm_num, ⟨1433880288311960112264, by norm_num⟩, by norm_num, ⟨1075410216233970084198, by norm_num⟩⟩)
        (Word.nil 2150820432467940168397))))))
theorem full_word_136 : Word word_136 2292007951276552749083 2150820432467940168397 := by
  unfold word_136
  have hp := shared_prefix_all 3976
  have ht := suffix_proof_136
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_136 : word_136.length = 46 := by decide
theorem word_sum_136 : word_136.sum = 73 := by decide
theorem infinite_family_136 (d : Nat) :
    ∃ z : Nat, Word word_136 (2292007951276552749083 + 2^74*d) z ∧
      z < 2292007951276552749083 + 2^74*d := by
  have h := word_uniform_descent full_word_136
    (show 2150820432467940168397 < 2292007951276552749083 by norm_num)
    (show 3^word_136.length < 2^word_136.sum by norm_num [word_136, sharedPrefix, suffix_136]) d
  simpa [word_sum_136] using h

/-- Certificate 137; shared prefix plus independently witnessed suffix. -/
def suffix_137 : List Nat := [2, 1, 3, 3, 4, 3]
def word_137 : List Nat := sharedPrefix ++ suffix_137
theorem suffix_proof_137 : Word suffix_137 495060137497781370849689 5506879276060220632163 := by
  unfold suffix_137
  exact Word.cons
        (show ExactStep 495060137497781370849689 371295103123336028137267 2 from by
          refine ⟨by norm_num, ⟨247530068748890685424844, by norm_num⟩, by norm_num, ⟨185647551561668014068633, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 371295103123336028137267 556942654685004042205901 1 from by
          refine ⟨by norm_num, ⟨185647551561668014068633, by norm_num⟩, by norm_num, ⟨278471327342502021102950, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 556942654685004042205901 208853495506876515827213 3 from by
          refine ⟨by norm_num, ⟨278471327342502021102950, by norm_num⟩, by norm_num, ⟨104426747753438257913606, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 208853495506876515827213 78320060815078693435205 3 from by
          refine ⟨by norm_num, ⟨104426747753438257913606, by norm_num⟩, by norm_num, ⟨39160030407539346717602, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 78320060815078693435205 14685011402827255019101 4 from by
          refine ⟨by norm_num, ⟨39160030407539346717602, by norm_num⟩, by norm_num, ⟨7342505701413627509550, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 14685011402827255019101 5506879276060220632163 3 from by
          refine ⟨by norm_num, ⟨7342505701413627509550, by norm_num⟩, by norm_num, ⟨2753439638030110316081, by norm_num⟩⟩)
        (Word.nil 5506879276060220632163))))))
theorem full_word_137 : Word word_137 11736740917015843176475 5506879276060220632163 := by
  unfold word_137
  have hp := shared_prefix_all 20360
  have ht := suffix_proof_137
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_137 : word_137.length = 46 := by decide
theorem word_sum_137 : word_137.sum = 74 := by decide
theorem infinite_family_137 (d : Nat) :
    ∃ z : Nat, Word word_137 (11736740917015843176475 + 2^75*d) z ∧
      z < 11736740917015843176475 + 2^75*d := by
  have h := word_uniform_descent full_word_137
    (show 5506879276060220632163 < 11736740917015843176475 by norm_num)
    (show 3^word_137.length < 2^word_137.sum by norm_num [word_137, sharedPrefix, suffix_137]) d
  simpa [word_sum_137] using h

/-- Certificate 138; shared prefix plus independently witnessed suffix. -/
def suffix_138 : List Nat := [2, 1, 3, 3, 6]
def word_138 : List Nat := sharedPrefix ++ suffix_138
theorem suffix_proof_138 : Word suffix_138 196273351175998288636313 1455518320793688480793 := by
  unfold suffix_138
  exact Word.cons
        (show ExactStep 196273351175998288636313 147205013381998716477235 2 from by
          refine ⟨by norm_num, ⟨98136675587999144318156, by norm_num⟩, by norm_num, ⟨73602506690999358238617, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 147205013381998716477235 220807520072998074715853 1 from by
          refine ⟨by norm_num, ⟨73602506690999358238617, by norm_num⟩, by norm_num, ⟨110403760036499037357926, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 220807520072998074715853 82802820027374278018445 3 from by
          refine ⟨by norm_num, ⟨110403760036499037357926, by norm_num⟩, by norm_num, ⟨41401410013687139009222, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 82802820027374278018445 31051057510265354256917 3 from by
          refine ⟨by norm_num, ⟨41401410013687139009222, by norm_num⟩, by norm_num, ⟨15525528755132677128458, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 31051057510265354256917 1455518320793688480793 6 from by
          refine ⟨by norm_num, ⟨15525528755132677128458, by norm_num⟩, by norm_num, ⟨727759160396844240396, by norm_num⟩⟩)
        (Word.nil 1455518320793688480793)))))
theorem full_word_138 : Word word_138 4653191192711375355931 1455518320793688480793 := by
  unfold word_138
  have hp := shared_prefix_all 8072
  have ht := suffix_proof_138
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_138 : word_138.length = 45 := by decide
theorem word_sum_138 : word_138.sum = 73 := by decide
theorem infinite_family_138 (d : Nat) :
    ∃ z : Nat, Word word_138 (4653191192711375355931 + 2^74*d) z ∧
      z < 4653191192711375355931 + 2^74*d := by
  have h := word_uniform_descent full_word_138
    (show 1455518320793688480793 < 4653191192711375355931 by norm_num)
    (show 3^word_138.length < 2^word_138.sum by norm_num [word_138, sharedPrefix, suffix_138]) d
  simpa [word_sum_138] using h

/-- Certificate 139; shared prefix plus independently witnessed suffix. -/
def suffix_139 : List Nat := [2, 1, 3, 3, 7]
def word_139 : List Nat := sharedPrefix ++ suffix_139
theorem suffix_proof_139 : Word suffix_139 1391420496463130617489817 5159228220223094788361 := by
  unfold suffix_139
  exact Word.cons
        (show ExactStep 1391420496463130617489817 1043565372347347963117363 2 from by
          refine ⟨by norm_num, ⟨695710248231565308744908, by norm_num⟩, by norm_num, ⟨521782686173673981558681, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1043565372347347963117363 1565348058521021944676045 1 from by
          refine ⟨by norm_num, ⟨521782686173673981558681, by norm_num⟩, by norm_num, ⟨782674029260510972338022, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1565348058521021944676045 587005521945383229253517 3 from by
          refine ⟨by norm_num, ⟨782674029260510972338022, by norm_num⟩, by norm_num, ⟨293502760972691614626758, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 587005521945383229253517 220127070729518710970069 3 from by
          refine ⟨by norm_num, ⟨293502760972691614626758, by norm_num⟩, by norm_num, ⟨110063535364759355485034, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 220127070729518710970069 5159228220223094788361 7 from by
          refine ⟨by norm_num, ⟨110063535364759355485034, by norm_num⟩, by norm_num, ⟨2579614110111547394180, by norm_num⟩⟩)
        (Word.nil 5159228220223094788361)))))
theorem full_word_139 : Word word_139 32987390089929246638107 5159228220223094788361 := by
  unfold word_139
  have hp := shared_prefix_all 57224
  have ht := suffix_proof_139
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_139 : word_139.length = 45 := by decide
theorem word_sum_139 : word_139.sum = 74 := by decide
theorem infinite_family_139 (d : Nat) :
    ∃ z : Nat, Word word_139 (32987390089929246638107 + 2^75*d) z ∧
      z < 32987390089929246638107 + 2^75*d := by
  have h := word_uniform_descent full_word_139
    (show 5159228220223094788361 < 32987390089929246638107 by norm_num)
    (show 3^word_139.length < 2^word_139.sum by norm_num [word_139, sharedPrefix, suffix_139]) d
  simpa [word_sum_139] using h

/-- Certificate 140; shared prefix plus independently witnessed suffix. -/
def suffix_140 : List Nat := [2, 1, 3, 3, 5]
def word_140 : List Nat := sharedPrefix ++ suffix_140
theorem suffix_proof_140 : Word suffix_140 395464542057187010111897 5865349348138210660229 := by
  unfold suffix_140
  exact Word.cons
        (show ExactStep 395464542057187010111897 296598406542890257583923 2 from by
          refine ⟨by norm_num, ⟨197732271028593505055948, by norm_num⟩, by norm_num, ⟨148299203271445128791961, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 296598406542890257583923 444897609814335386375885 1 from by
          refine ⟨by norm_num, ⟨148299203271445128791961, by norm_num⟩, by norm_num, ⟨222448804907167693187942, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 444897609814335386375885 166836603680375769890957 3 from by
          refine ⟨by norm_num, ⟨222448804907167693187942, by norm_num⟩, by norm_num, ⟨83418301840187884945478, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 166836603680375769890957 62563726380140913709109 3 from by
          refine ⟨by norm_num, ⟨83418301840187884945478, by norm_num⟩, by norm_num, ⟨31281863190070456854554, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 62563726380140913709109 5865349348138210660229 5 from by
          refine ⟨by norm_num, ⟨31281863190070456854554, by norm_num⟩, by norm_num, ⟨2932674674069105330114, by norm_num⟩⟩)
        (Word.nil 5865349348138210660229)))))
theorem full_word_140 : Word word_140 9375557675581020569627 5865349348138210660229 := by
  unfold word_140
  have hp := shared_prefix_all 16264
  have ht := suffix_proof_140
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_140 : word_140.length = 45 := by decide
theorem word_sum_140 : word_140.sum = 72 := by decide
theorem infinite_family_140 (d : Nat) :
    ∃ z : Nat, Word word_140 (9375557675581020569627 + 2^73*d) z ∧
      z < 9375557675581020569627 + 2^73*d := by
  have h := word_uniform_descent full_word_140
    (show 5865349348138210660229 < 9375557675581020569627 by norm_num)
    (show 3^word_140.length < 2^word_140.sum by norm_num [word_140, sharedPrefix, suffix_140]) d
  simpa [word_sum_140] using h

/-- Certificate 141; shared prefix plus independently witnessed suffix. -/
def suffix_141 : List Nat := [2, 1, 3, 1, 1, 7]
def word_141 : List Nat := sharedPrefix ++ suffix_141
theorem suffix_proof_141 : Word suffix_141 194717169997239001749785 4331934110351172859973 := by
  unfold suffix_141
  exact Word.cons
        (show ExactStep 194717169997239001749785 146037877497929251312339 2 from by
          refine ⟨by norm_num, ⟨97358584998619500874892, by norm_num⟩, by norm_num, ⟨73018938748964625656169, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 146037877497929251312339 219056816246893876968509 1 from by
          refine ⟨by norm_num, ⟨73018938748964625656169, by norm_num⟩, by norm_num, ⟨109528408123446938484254, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 219056816246893876968509 82146306092585203863191 3 from by
          refine ⟨by norm_num, ⟨109528408123446938484254, by norm_num⟩, by norm_num, ⟨41073153046292601931595, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 82146306092585203863191 123219459138877805794787 1 from by
          refine ⟨by norm_num, ⟨41073153046292601931595, by norm_num⟩, by norm_num, ⟨61609729569438902897393, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 123219459138877805794787 184829188708316708692181 1 from by
          refine ⟨by norm_num, ⟨61609729569438902897393, by norm_num⟩, by norm_num, ⟨92414594354158354346090, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 184829188708316708692181 4331934110351172859973 7 from by
          refine ⟨by norm_num, ⟨92414594354158354346090, by norm_num⟩, by norm_num, ⟨2165967055175586429986, by norm_num⟩⟩)
        (Word.nil 4331934110351172859973))))))
theorem full_word_141 : Word word_141 4616297704563956252699 4331934110351172859973 := by
  unfold word_141
  have hp := shared_prefix_all 8008
  have ht := suffix_proof_141
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_141 : word_141.length = 46 := by decide
theorem word_sum_141 : word_141.sum = 73 := by decide
theorem infinite_family_141 (d : Nat) :
    ∃ z : Nat, Word word_141 (4616297704563956252699 + 2^74*d) z ∧
      z < 4616297704563956252699 + 2^74*d := by
  have h := word_uniform_descent full_word_141
    (show 4331934110351172859973 < 4616297704563956252699 by norm_num)
    (show 3^word_141.length < 2^word_141.sum by norm_num [word_141, sharedPrefix, suffix_141]) d
  simpa [word_sum_141] using h

/-- Certificate 142; shared prefix plus independently witnessed suffix. -/
def suffix_142 : List Nat := [2, 1, 3, 1, 1, 8]
def word_142 : List Nat := sharedPrefix ++ suffix_142
theorem suffix_proof_142 : Word suffix_142 593099551759616444700953 6597436115001836977951 := by
  unfold suffix_142
  exact Word.cons
        (show ExactStep 593099551759616444700953 444824663819712333525715 2 from by
          refine ⟨by norm_num, ⟨296549775879808222350476, by norm_num⟩, by norm_num, ⟨222412331909856166762857, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 444824663819712333525715 667236995729568500288573 1 from by
          refine ⟨by norm_num, ⟨222412331909856166762857, by norm_num⟩, by norm_num, ⟨333618497864784250144286, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 667236995729568500288573 250213873398588187608215 3 from by
          refine ⟨by norm_num, ⟨333618497864784250144286, by norm_num⟩, by norm_num, ⟨125106936699294093804107, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 250213873398588187608215 375320810097882281412323 1 from by
          refine ⟨by norm_num, ⟨125106936699294093804107, by norm_num⟩, by norm_num, ⟨187660405048941140706161, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 375320810097882281412323 562981215146823422118485 1 from by
          refine ⟨by norm_num, ⟨187660405048941140706161, by norm_num⟩, by norm_num, ⟨281490607573411711059242, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 562981215146823422118485 6597436115001836977951 8 from by
          refine ⟨by norm_num, ⟨281490607573411711059242, by norm_num⟩, by norm_num, ⟨3298718057500918488975, by norm_num⟩⟩)
        (Word.nil 6597436115001836977951))))))
theorem full_word_142 : Word word_142 14061030670303246680091 6597436115001836977951 := by
  unfold word_142
  have hp := shared_prefix_all 24392
  have ht := suffix_proof_142
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_142 : word_142.length = 46 := by decide
theorem word_sum_142 : word_142.sum = 74 := by decide
theorem infinite_family_142 (d : Nat) :
    ∃ z : Nat, Word word_142 (14061030670303246680091 + 2^75*d) z ∧
      z < 14061030670303246680091 + 2^75*d := by
  have h := word_uniform_descent full_word_142
    (show 6597436115001836977951 < 14061030670303246680091 by norm_num)
    (show 3^word_142.length < 2^word_142.sum by norm_num [word_142, sharedPrefix, suffix_142]) d
  simpa [word_sum_142] using h

/-- Certificate 143; shared prefix plus independently witnessed suffix. -/
def suffix_143 : List Nat := [2, 1, 3, 1, 2, 7]
def word_143 : List Nat := sharedPrefix ++ suffix_143
theorem suffix_proof_143 : Word suffix_143 365897099660760559267865 4070113916819678462315 := by
  unfold suffix_143
  exact Word.cons
        (show ExactStep 365897099660760559267865 274422824745570419450899 2 from by
          refine ⟨by norm_num, ⟨182948549830380279633932, by norm_num⟩, by norm_num, ⟨137211412372785209725449, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 274422824745570419450899 411634237118355629176349 1 from by
          refine ⟨by norm_num, ⟨137211412372785209725449, by norm_num⟩, by norm_num, ⟨205817118559177814588174, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 411634237118355629176349 154362838919383360941131 3 from by
          refine ⟨by norm_num, ⟨205817118559177814588174, by norm_num⟩, by norm_num, ⟨77181419459691680470565, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 154362838919383360941131 231544258379075041411697 1 from by
          refine ⟨by norm_num, ⟨77181419459691680470565, by norm_num⟩, by norm_num, ⟨115772129189537520705848, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 231544258379075041411697 173658193784306281058773 2 from by
          refine ⟨by norm_num, ⟨115772129189537520705848, by norm_num⟩, by norm_num, ⟨86829096892153140529386, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 173658193784306281058773 4070113916819678462315 7 from by
          refine ⟨by norm_num, ⟨86829096892153140529386, by norm_num⟩, by norm_num, ⟨2035056958409839231157, by norm_num⟩⟩)
        (Word.nil 4070113916819678462315))))))
theorem full_word_143 : Word word_143 8674581400780057608219 4070113916819678462315 := by
  unfold word_143
  have hp := shared_prefix_all 15048
  have ht := suffix_proof_143
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_143 : word_143.length = 46 := by decide
theorem word_sum_143 : word_143.sum = 74 := by decide
theorem infinite_family_143 (d : Nat) :
    ∃ z : Nat, Word word_143 (8674581400780057608219 + 2^75*d) z ∧
      z < 8674581400780057608219 + 2^75*d := by
  have h := word_uniform_descent full_word_143
    (show 4070113916819678462315 < 8674581400780057608219 by norm_num)
    (show 3^word_143.length < 2^word_143.sum by norm_num [word_143, sharedPrefix, suffix_143]) d
  simpa [word_sum_143] using h

/-- Certificate 144; shared prefix plus independently witnessed suffix. -/
def suffix_144 : List Nat := [2, 1, 3, 1, 2, 6]
def word_144 : List Nat := sharedPrefix ++ suffix_144
theorem suffix_proof_144 : Word suffix_144 764279481423138002219033 17003165953291858020559 := by
  unfold suffix_144
  exact Word.cons
        (show ExactStep 764279481423138002219033 573209611067353501664275 2 from by
          refine ⟨by norm_num, ⟨382139740711569001109516, by norm_num⟩, by norm_num, ⟨286604805533676750832137, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 573209611067353501664275 859814416601030252496413 1 from by
          refine ⟨by norm_num, ⟨286604805533676750832137, by norm_num⟩, by norm_num, ⟨429907208300515126248206, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 859814416601030252496413 322430406225386344686155 3 from by
          refine ⟨by norm_num, ⟨429907208300515126248206, by norm_num⟩, by norm_num, ⟨161215203112693172343077, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 322430406225386344686155 483645609338079517029233 1 from by
          refine ⟨by norm_num, ⟨161215203112693172343077, by norm_num⟩, by norm_num, ⟨241822804669039758514616, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 483645609338079517029233 362734207003559637771925 2 from by
          refine ⟨by norm_num, ⟨241822804669039758514616, by norm_num⟩, by norm_num, ⟨181367103501779818885962, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 362734207003559637771925 17003165953291858020559 6 from by
          refine ⟨by norm_num, ⟨181367103501779818885962, by norm_num⟩, by norm_num, ⟨8501582976645929010279, by norm_num⟩⟩)
        (Word.nil 17003165953291858020559))))))
theorem full_word_144 : Word word_144 18119314366519348035611 17003165953291858020559 := by
  unfold word_144
  have hp := shared_prefix_all 31432
  have ht := suffix_proof_144
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_144 : word_144.length = 46 := by decide
theorem word_sum_144 : word_144.sum = 73 := by decide
theorem infinite_family_144 (d : Nat) :
    ∃ z : Nat, Word word_144 (18119314366519348035611 + 2^74*d) z ∧
      z < 18119314366519348035611 + 2^74*d := by
  have h := word_uniform_descent full_word_144
    (show 17003165953291858020559 < 18119314366519348035611 by norm_num)
    (show 3^word_144.length < 2^word_144.sum by norm_num [word_144, sharedPrefix, suffix_144]) d
  simpa [word_sum_144] using h

/-- Certificate 145; shared prefix plus independently witnessed suffix. -/
def suffix_145 : List Nat := [2, 1, 3, 1, 3, 5]
def word_145 : List Nat := sharedPrefix ++ suffix_145
theorem suffix_proof_145 : Word suffix_145 309874577225426231352857 6893877160563223958015 := by
  unfold suffix_145
  exact Word.cons
        (show ExactStep 309874577225426231352857 232405932919069673514643 2 from by
          refine ⟨by norm_num, ⟨154937288612713115676428, by norm_num⟩, by norm_num, ⟨116202966459534836757321, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 232405932919069673514643 348608899378604510271965 1 from by
          refine ⟨by norm_num, ⟨116202966459534836757321, by norm_num⟩, by norm_num, ⟨174304449689302255135982, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 348608899378604510271965 130728337266976691351987 3 from by
          refine ⟨by norm_num, ⟨174304449689302255135982, by norm_num⟩, by norm_num, ⟨65364168633488345675993, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 130728337266976691351987 196092505900465037027981 1 from by
          refine ⟨by norm_num, ⟨65364168633488345675993, by norm_num⟩, by norm_num, ⟨98046252950232518513990, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 196092505900465037027981 73534689712674388885493 3 from by
          refine ⟨by norm_num, ⟨98046252950232518513990, by norm_num⟩, by norm_num, ⟨36767344856337194442746, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 73534689712674388885493 6893877160563223958015 5 from by
          refine ⟨by norm_num, ⟨36767344856337194442746, by norm_num⟩, by norm_num, ⟨3446938580281611979007, by norm_num⟩⟩)
        (Word.nil 6893877160563223958015))))))
theorem full_word_145 : Word word_145 7346415827472969891867 6893877160563223958015 := by
  unfold word_145
  have hp := shared_prefix_all 12744
  have ht := suffix_proof_145
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_145 : word_145.length = 46 := by decide
theorem word_sum_145 : word_145.sum = 73 := by decide
theorem infinite_family_145 (d : Nat) :
    ∃ z : Nat, Word word_145 (7346415827472969891867 + 2^74*d) z ∧
      z < 7346415827472969891867 + 2^74*d := by
  have h := word_uniform_descent full_word_145
    (show 6893877160563223958015 < 7346415827472969891867 by norm_num)
    (show 3^word_145.length < 2^word_145.sum by norm_num [word_145, sharedPrefix, suffix_145]) d
  simpa [word_sum_145] using h

/-- Certificate 146; shared prefix plus independently witnessed suffix. -/
def suffix_146 : List Nat := [2, 1, 3, 1, 3, 6]
def word_146 : List Nat := sharedPrefix ++ suffix_146
theorem suffix_proof_146 : Word suffix_146 1505021722512558560206361 16741345759760363622901 := by
  unfold suffix_146
  exact Word.cons
        (show ExactStep 1505021722512558560206361 1128766291884418920154771 2 from by
          refine ⟨by norm_num, ⟨752510861256279280103180, by norm_num⟩, by norm_num, ⟨564383145942209460077385, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1128766291884418920154771 1693149437826628380232157 1 from by
          refine ⟨by norm_num, ⟨564383145942209460077385, by norm_num⟩, by norm_num, ⟨846574718913314190116078, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1693149437826628380232157 634931039184985642587059 3 from by
          refine ⟨by norm_num, ⟨846574718913314190116078, by norm_num⟩, by norm_num, ⟨317465519592492821293529, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 634931039184985642587059 952396558777478463880589 1 from by
          refine ⟨by norm_num, ⟨317465519592492821293529, by norm_num⟩, by norm_num, ⟨476198279388739231940294, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 952396558777478463880589 357148709541554423955221 3 from by
          refine ⟨by norm_num, ⟨476198279388739231940294, by norm_num⟩, by norm_num, ⟨178574354770777211977610, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 357148709541554423955221 16741345759760363622901 6 from by
          refine ⟨by norm_num, ⟨178574354770777211977610, by norm_num⟩, by norm_num, ⟨8370672879880181811450, by norm_num⟩⟩)
        (Word.nil 16741345759760363622901))))))
theorem full_word_146 : Word word_146 35680614724690841174043 16741345759760363622901 := by
  unfold word_146
  have hp := shared_prefix_all 61896
  have ht := suffix_proof_146
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_146 : word_146.length = 46 := by decide
theorem word_sum_146 : word_146.sum = 74 := by decide
theorem infinite_family_146 (d : Nat) :
    ∃ z : Nat, Word word_146 (35680614724690841174043 + 2^75*d) z ∧
      z < 35680614724690841174043 + 2^75*d := by
  have h := word_uniform_descent full_word_146
    (show 16741345759760363622901 < 35680614724690841174043 by norm_num)
    (show 3^word_146.length < 2^word_146.sum by norm_num [word_146, sharedPrefix, suffix_146]) d
  simpa [word_sum_146] using h

/-- Certificate 147; shared prefix plus independently witnessed suffix. -/
def suffix_147 : List Nat := [2, 1, 3, 1, 9]
def word_147 : List Nat := sharedPrefix ++ suffix_147
theorem suffix_proof_147 : Word suffix_147 820302003858472330134041 3041586104394665164529 := by
  unfold suffix_147
  exact Word.cons
        (show ExactStep 820302003858472330134041 615226502893854247600531 2 from by
          refine ⟨by norm_num, ⟨410151001929236165067020, by norm_num⟩, by norm_num, ⟨307613251446927123800265, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 615226502893854247600531 922839754340781371400797 1 from by
          refine ⟨by norm_num, ⟨307613251446927123800265, by norm_num⟩, by norm_num, ⟨461419877170390685700398, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 922839754340781371400797 346064907877793014275299 3 from by
          refine ⟨by norm_num, ⟨461419877170390685700398, by norm_num⟩, by norm_num, ⟨173032453938896507137649, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 346064907877793014275299 519097361816689521412949 1 from by
          refine ⟨by norm_num, ⟨173032453938896507137649, by norm_num⟩, by norm_num, ⟨259548680908344760706474, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 519097361816689521412949 3041586104394665164529 9 from by
          refine ⟨by norm_num, ⟨259548680908344760706474, by norm_num⟩, by norm_num, ⟨1520793052197332582264, by norm_num⟩⟩)
        (Word.nil 3041586104394665164529)))))
theorem full_word_147 : Word word_147 19447479939826435751963 3041586104394665164529 := by
  unfold word_147
  have hp := shared_prefix_all 33736
  have ht := suffix_proof_147
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_147 : word_147.length = 45 := by decide
theorem word_sum_147 : word_147.sum = 74 := by decide
theorem infinite_family_147 (d : Nat) :
    ∃ z : Nat, Word word_147 (19447479939826435751963 + 2^75*d) z ∧
      z < 19447479939826435751963 + 2^75*d := by
  have h := word_uniform_descent full_word_147
    (show 3041586104394665164529 < 19447479939826435751963 by norm_num)
    (show 3^word_147.length < 2^word_147.sum by norm_num [word_147, sharedPrefix, suffix_147]) d
  simpa [word_sum_147] using h

/-- Certificate 148; shared prefix plus independently witnessed suffix. -/
def suffix_148 : List Nat := [2, 1, 3, 1, 8]
def word_148 : List Nat := sharedPrefix ++ suffix_148
theorem suffix_proof_148 : Word suffix_148 421919622096094887182873 3128859502238496630415 := by
  unfold suffix_148
  exact Word.cons
        (show ExactStep 421919622096094887182873 316439716572071165387155 2 from by
          refine ⟨by norm_num, ⟨210959811048047443591436, by norm_num⟩, by norm_num, ⟨158219858286035582693577, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 316439716572071165387155 474659574858106748080733 1 from by
          refine ⟨by norm_num, ⟨158219858286035582693577, by norm_num⟩, by norm_num, ⟨237329787429053374040366, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 474659574858106748080733 177997340571790030530275 3 from by
          refine ⟨by norm_num, ⟨237329787429053374040366, by norm_num⟩, by norm_num, ⟨88998670285895015265137, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 177997340571790030530275 266996010857685045795413 1 from by
          refine ⟨by norm_num, ⟨88998670285895015265137, by norm_num⟩, by norm_num, ⟨133498005428842522897706, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 266996010857685045795413 3128859502238496630415 8 from by
          refine ⟨by norm_num, ⟨133498005428842522897706, by norm_num⟩, by norm_num, ⟨1564429751119248315207, by norm_num⟩⟩)
        (Word.nil 3128859502238496630415)))))
theorem full_word_148 : Word word_148 10002746974087145324571 3128859502238496630415 := by
  unfold word_148
  have hp := shared_prefix_all 17352
  have ht := suffix_proof_148
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_148 : word_148.length = 45 := by decide
theorem word_sum_148 : word_148.sum = 73 := by decide
theorem infinite_family_148 (d : Nat) :
    ∃ z : Nat, Word word_148 (10002746974087145324571 + 2^74*d) z ∧
      z < 10002746974087145324571 + 2^74*d := by
  have h := word_uniform_descent full_word_148
    (show 3128859502238496630415 < 10002746974087145324571 by norm_num)
    (show 3^word_148.length < 2^word_148.sum by norm_num [word_148, sharedPrefix, suffix_148]) d
  simpa [word_sum_148] using h

/-- Certificate 149; shared prefix plus independently witnessed suffix. -/
def suffix_149 : List Nat := [2, 1, 3, 1, 7]
def word_149 : List Nat := sharedPrefix ++ suffix_149
theorem suffix_proof_149 : Word suffix_149 222728431214906165707289 3303406297926159562187 := by
  unfold suffix_149
  exact Word.cons
        (show ExactStep 222728431214906165707289 167046323411179624280467 2 from by
          refine ⟨by norm_num, ⟨111364215607453082853644, by norm_num⟩, by norm_num, ⟨83523161705589812140233, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 167046323411179624280467 250569485116769436420701 1 from by
          refine ⟨by norm_num, ⟨83523161705589812140233, by norm_num⟩, by norm_num, ⟨125284742558384718210350, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 250569485116769436420701 93963556918788538657763 3 from by
          refine ⟨by norm_num, ⟨125284742558384718210350, by norm_num⟩, by norm_num, ⟨46981778459394269328881, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 93963556918788538657763 140945335378182807986645 1 from by
          refine ⟨by norm_num, ⟨46981778459394269328881, by norm_num⟩, by norm_num, ⟨70472667689091403993322, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 140945335378182807986645 3303406297926159562187 7 from by
          refine ⟨by norm_num, ⟨70472667689091403993322, by norm_num⟩, by norm_num, ⟨1651703148963079781093, by norm_num⟩⟩)
        (Word.nil 3303406297926159562187)))))
theorem full_word_149 : Word word_149 5280380491217500110875 3303406297926159562187 := by
  unfold word_149
  have hp := shared_prefix_all 9160
  have ht := suffix_proof_149
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_149 : word_149.length = 45 := by decide
theorem word_sum_149 : word_149.sum = 72 := by decide
theorem infinite_family_149 (d : Nat) :
    ∃ z : Nat, Word word_149 (5280380491217500110875 + 2^73*d) z ∧
      z < 5280380491217500110875 + 2^73*d := by
  have h := word_uniform_descent full_word_149
    (show 3303406297926159562187 < 5280380491217500110875 by norm_num)
    (show 3^word_149.length < 2^word_149.sum by norm_num [word_149, sharedPrefix, suffix_149]) d
  simpa [word_sum_149] using h

/-- Certificate 150; shared prefix plus independently witnessed suffix. -/
def suffix_150 : List Nat := [2, 1, 3, 1, 6, 2]
def word_150 : List Nat := sharedPrefix ++ suffix_150
theorem suffix_proof_150 : Word suffix_150 322324026655500526445081 7170843976802364617263 := by
  unfold suffix_150
  exact Word.cons
        (show ExactStep 322324026655500526445081 241743019991625394833811 2 from by
          refine ⟨by norm_num, ⟨161162013327750263222540, by norm_num⟩, by norm_num, ⟨120871509995812697416905, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 241743019991625394833811 362614529987438092250717 1 from by
          refine ⟨by norm_num, ⟨120871509995812697416905, by norm_num⟩, by norm_num, ⟨181307264993719046125358, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 362614529987438092250717 135980448745289284594019 3 from by
          refine ⟨by norm_num, ⟨181307264993719046125358, by norm_num⟩, by norm_num, ⟨67990224372644642297009, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 135980448745289284594019 203970673117933926891029 1 from by
          refine ⟨by norm_num, ⟨67990224372644642297009, by norm_num⟩, by norm_num, ⟨101985336558966963445514, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 203970673117933926891029 9561125302403152823017 6 from by
          refine ⟨by norm_num, ⟨101985336558966963445514, by norm_num⟩, by norm_num, ⟨4780562651201576411508, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 9561125302403152823017 7170843976802364617263 2 from by
          refine ⟨by norm_num, ⟨4780562651201576411508, by norm_num⟩, by norm_num, ⟨3585421988401182308631, by norm_num⟩⟩)
        (Word.nil 7170843976802364617263))))))
theorem full_word_150 : Word word_150 7641563732652322717723 7170843976802364617263 := by
  unfold word_150
  have hp := shared_prefix_all 13256
  have ht := suffix_proof_150
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_150 : word_150.length = 46 := by decide
theorem word_sum_150 : word_150.sum = 73 := by decide
theorem infinite_family_150 (d : Nat) :
    ∃ z : Nat, Word word_150 (7641563732652322717723 + 2^74*d) z ∧
      z < 7641563732652322717723 + 2^74*d := by
  have h := word_uniform_descent full_word_150
    (show 7170843976802364617263 < 7641563732652322717723 by norm_num)
    (show 3^word_150.length < 2^word_150.sum by norm_num [word_150, sharedPrefix, suffix_150]) d
  simpa [word_sum_150] using h

/-- Certificate 151; shared prefix plus independently witnessed suffix. -/
def suffix_151 : List Nat := [2, 1, 3, 1, 6, 3]
def word_151 : List Nat := sharedPrefix ++ suffix_151
theorem suffix_proof_151 : Word suffix_151 1517471171942632855298585 16879829167879933952525 := by
  unfold suffix_151
  exact Word.cons
        (show ExactStep 1517471171942632855298585 1138103378956974641473939 2 from by
          refine ⟨by norm_num, ⟨758735585971316427649292, by norm_num⟩, by norm_num, ⟨569051689478487320736969, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1138103378956974641473939 1707155068435461962210909 1 from by
          refine ⟨by norm_num, ⟨569051689478487320736969, by norm_num⟩, by norm_num, ⟨853577534217730981105454, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1707155068435461962210909 640183150663298235829091 3 from by
          refine ⟨by norm_num, ⟨853577534217730981105454, by norm_num⟩, by norm_num, ⟨320091575331649117914545, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 640183150663298235829091 960274725994947353743637 1 from by
          refine ⟨by norm_num, ⟨320091575331649117914545, by norm_num⟩, by norm_num, ⟨480137362997473676871818, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 960274725994947353743637 45012877781013157206733 6 from by
          refine ⟨by norm_num, ⟨480137362997473676871818, by norm_num⟩, by norm_num, ⟨22506438890506578603366, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 45012877781013157206733 16879829167879933952525 3 from by
          refine ⟨by norm_num, ⟨22506438890506578603366, by norm_num⟩, by norm_num, ⟨8439914583939966976262, by norm_num⟩⟩)
        (Word.nil 16879829167879933952525))))))
theorem full_word_151 : Word word_151 35975762629870193999899 16879829167879933952525 := by
  unfold word_151
  have hp := shared_prefix_all 62408
  have ht := suffix_proof_151
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_151 : word_151.length = 46 := by decide
theorem word_sum_151 : word_151.sum = 74 := by decide
theorem infinite_family_151 (d : Nat) :
    ∃ z : Nat, Word word_151 (35975762629870193999899 + 2^75*d) z ∧
      z < 35975762629870193999899 + 2^75*d := by
  have h := word_uniform_descent full_word_151
    (show 16879829167879933952525 < 35975762629870193999899 by norm_num)
    (show 3^word_151.length < 2^word_151.sum by norm_num [word_151, sharedPrefix, suffix_151]) d
  simpa [word_sum_151] using h

/-- Certificate 152; shared prefix plus independently witnessed suffix. -/
def suffix_152 : List Nat := [2, 1, 3, 1, 5, 4]
def word_152 : List Nat := sharedPrefix ++ suffix_152
theorem suffix_proof_152 : Word suffix_152 372121824375797706813977 4139355620879463627127 := by
  unfold suffix_152
  exact Word.cons
        (show ExactStep 372121824375797706813977 279091368281848280110483 2 from by
          refine ⟨by norm_num, ⟨186060912187898853406988, by norm_num⟩, by norm_num, ⟨139545684140924140055241, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 279091368281848280110483 418637052422772420165725 1 from by
          refine ⟨by norm_num, ⟨139545684140924140055241, by norm_num⟩, by norm_num, ⟨209318526211386210082862, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 418637052422772420165725 156988894658539657562147 3 from by
          refine ⟨by norm_num, ⟨209318526211386210082862, by norm_num⟩, by norm_num, ⟨78494447329269828781073, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 156988894658539657562147 235483341987809486343221 1 from by
          refine ⟨by norm_num, ⟨78494447329269828781073, by norm_num⟩, by norm_num, ⟨117741670993904743171610, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 235483341987809486343221 22076563311357139344677 5 from by
          refine ⟨by norm_num, ⟨117741670993904743171610, by norm_num⟩, by norm_num, ⟨11038281655678569672338, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 22076563311357139344677 4139355620879463627127 4 from by
          refine ⟨by norm_num, ⟨11038281655678569672338, by norm_num⟩, by norm_num, ⟨2069677810439731813563, by norm_num⟩⟩)
        (Word.nil 4139355620879463627127))))))
theorem full_word_152 : Word word_152 8822155353369734021147 4139355620879463627127 := by
  unfold word_152
  have hp := shared_prefix_all 15304
  have ht := suffix_proof_152
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_152 : word_152.length = 46 := by decide
theorem word_sum_152 : word_152.sum = 74 := by decide
theorem infinite_family_152 (d : Nat) :
    ∃ z : Nat, Word word_152 (8822155353369734021147 + 2^75*d) z ∧
      z < 8822155353369734021147 + 2^75*d := by
  have h := word_uniform_descent full_word_152
    (show 4139355620879463627127 < 8822155353369734021147 by norm_num)
    (show 3^word_152.length < 2^word_152.sum by norm_num [word_152, sharedPrefix, suffix_152]) d
  simpa [word_sum_152] using h

/-- Certificate 153; shared prefix plus independently witnessed suffix. -/
def suffix_153 : List Nat := [2, 1, 3, 1, 5, 3]
def word_153 : List Nat := sharedPrefix ++ suffix_153
theorem suffix_proof_153 : Word suffix_153 770504206138175149765145 17141649361411428350183 := by
  unfold suffix_153
  exact Word.cons
        (show ExactStep 770504206138175149765145 577878154603631362323859 2 from by
          refine ⟨by norm_num, ⟨385252103069087574882572, by norm_num⟩, by norm_num, ⟨288939077301815681161929, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 577878154603631362323859 866817231905447043485789 1 from by
          refine ⟨by norm_num, ⟨288939077301815681161929, by norm_num⟩, by norm_num, ⟨433408615952723521742894, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 866817231905447043485789 325056461964542641307171 3 from by
          refine ⟨by norm_num, ⟨433408615952723521742894, by norm_num⟩, by norm_num, ⟨162528230982271320653585, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 325056461964542641307171 487584692946813961960757 1 from by
          refine ⟨by norm_num, ⟨162528230982271320653585, by norm_num⟩, by norm_num, ⟨243792346473406980980378, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 487584692946813961960757 45711064963763808933821 5 from by
          refine ⟨by norm_num, ⟨243792346473406980980378, by norm_num⟩, by norm_num, ⟨22855532481881904466910, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 45711064963763808933821 17141649361411428350183 3 from by
          refine ⟨by norm_num, ⟨22855532481881904466910, by norm_num⟩, by norm_num, ⟨8570824680705714175091, by norm_num⟩⟩)
        (Word.nil 17141649361411428350183))))))
theorem full_word_153 : Word word_153 18266888319109024448539 17141649361411428350183 := by
  unfold word_153
  have hp := shared_prefix_all 31688
  have ht := suffix_proof_153
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_153 : word_153.length = 46 := by decide
theorem word_sum_153 : word_153.sum = 73 := by decide
theorem infinite_family_153 (d : Nat) :
    ∃ z : Nat, Word word_153 (18266888319109024448539 + 2^74*d) z ∧
      z < 18266888319109024448539 + 2^74*d := by
  have h := word_uniform_descent full_word_153
    (show 17141649361411428350183 < 18266888319109024448539 by norm_num)
    (show 3^word_153.length < 2^word_153.sum by norm_num [word_153, sharedPrefix, suffix_153]) d
  simpa [word_sum_153] using h

/-- Certificate 154; shared prefix plus independently witnessed suffix. -/
def suffix_154 : List Nat := [2, 1, 3, 1, 4, 4]
def word_154 : List Nat := sharedPrefix ++ suffix_154
theorem suffix_proof_154 : Word suffix_154 197829532354757575522841 4401175814410958024785 := by
  unfold suffix_154
  exact Word.cons
        (show ExactStep 197829532354757575522841 148372149266068181642131 2 from by
          refine ⟨by norm_num, ⟨98914766177378787761420, by norm_num⟩, by norm_num, ⟨74186074633034090821065, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 148372149266068181642131 222558223899102272463197 1 from by
          refine ⟨by norm_num, ⟨74186074633034090821065, by norm_num⟩, by norm_num, ⟨111279111949551136231598, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 222558223899102272463197 83459333962163352173699 3 from by
          refine ⟨by norm_num, ⟨111279111949551136231598, by norm_num⟩, by norm_num, ⟨41729666981081676086849, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 83459333962163352173699 125189000943245028260549 1 from by
          refine ⟨by norm_num, ⟨41729666981081676086849, by norm_num⟩, by norm_num, ⟨62594500471622514130274, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 125189000943245028260549 23472937676858442798853 4 from by
          refine ⟨by norm_num, ⟨62594500471622514130274, by norm_num⟩, by norm_num, ⟨11736468838429221399426, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 23472937676858442798853 4401175814410958024785 4 from by
          refine ⟨by norm_num, ⟨11736468838429221399426, by norm_num⟩, by norm_num, ⟨2200587907205479012392, by norm_num⟩⟩)
        (Word.nil 4401175814410958024785))))))
theorem full_word_154 : Word word_154 4690084680858794459163 4401175814410958024785 := by
  unfold word_154
  have hp := shared_prefix_all 8136
  have ht := suffix_proof_154
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_154 : word_154.length = 46 := by decide
theorem word_sum_154 : word_154.sum = 73 := by decide
theorem infinite_family_154 (d : Nat) :
    ∃ z : Nat, Word word_154 (4690084680858794459163 + 2^74*d) z ∧
      z < 4690084680858794459163 + 2^74*d := by
  have h := word_uniform_descent full_word_154
    (show 4401175814410958024785 < 4690084680858794459163 by norm_num)
    (show 3^word_154.length < 2^word_154.sum by norm_num [word_154, sharedPrefix, suffix_154]) d
  simpa [word_sum_154] using h

/-- Certificate 155; shared prefix plus independently witnessed suffix. -/
def suffix_155 : List Nat := [2, 1, 3, 1, 4, 5]
def word_155 : List Nat := sharedPrefix ++ suffix_155
theorem suffix_proof_155 : Word suffix_155 596211914117135018474009 6632056967031729560357 := by
  unfold suffix_155
  exact Word.cons
        (show ExactStep 596211914117135018474009 447158935587851263855507 2 from by
          refine ⟨by norm_num, ⟨298105957058567509237004, by norm_num⟩, by norm_num, ⟨223579467793925631927753, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 447158935587851263855507 670738403381776895783261 1 from by
          refine ⟨by norm_num, ⟨223579467793925631927753, by norm_num⟩, by norm_num, ⟨335369201690888447891630, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 670738403381776895783261 251526901268166335918723 3 from by
          refine ⟨by norm_num, ⟨335369201690888447891630, by norm_num⟩, by norm_num, ⟨125763450634083167959361, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 251526901268166335918723 377290351902249503878085 1 from by
          refine ⟨by norm_num, ⟨125763450634083167959361, by norm_num⟩, by norm_num, ⟨188645175951124751939042, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 377290351902249503878085 70741940981671781977141 4 from by
          refine ⟨by norm_num, ⟨188645175951124751939042, by norm_num⟩, by norm_num, ⟨35370970490835890988570, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 70741940981671781977141 6632056967031729560357 5 from by
          refine ⟨by norm_num, ⟨35370970490835890988570, by norm_num⟩, by norm_num, ⟨3316028483515864780178, by norm_num⟩⟩)
        (Word.nil 6632056967031729560357))))))
theorem full_word_155 : Word word_155 14134817646598084886555 6632056967031729560357 := by
  unfold word_155
  have hp := shared_prefix_all 24520
  have ht := suffix_proof_155
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_155 : word_155.length = 46 := by decide
theorem word_sum_155 : word_155.sum = 74 := by decide
theorem infinite_family_155 (d : Nat) :
    ∃ z : Nat, Word word_155 (14134817646598084886555 + 2^75*d) z ∧
      z < 14134817646598084886555 + 2^75*d := by
  have h := word_uniform_descent full_word_155
    (show 6632056967031729560357 < 14134817646598084886555 by norm_num)
    (show 3^word_155.length < 2^word_155.sum by norm_num [word_155, sharedPrefix, suffix_155]) d
  simpa [word_sum_155] using h

/-- Certificate 156; shared prefix plus independently witnessed suffix. -/
def suffix_156 : List Nat := [2, 1, 5, 3, 1, 4]
def word_156 : List Nat := sharedPrefix ++ suffix_156
theorem suffix_proof_156 : Word suffix_156 897332972207057031017177 9981624400923836908135 := by
  unfold suffix_156
  exact Word.cons
        (show ExactStep 897332972207057031017177 672999729155292773262883 2 from by
          refine ⟨by norm_num, ⟨448666486103528515508588, by norm_num⟩, by norm_num, ⟨336499864577646386631441, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 672999729155292773262883 1009499593732939159894325 1 from by
          refine ⟨by norm_num, ⟨336499864577646386631441, by norm_num⟩, by norm_num, ⟨504749796866469579947162, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1009499593732939159894325 94640586912463046240093 5 from by
          refine ⟨by norm_num, ⟨504749796866469579947162, by norm_num⟩, by norm_num, ⟨47320293456231523120046, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 94640586912463046240093 35490220092173642340035 3 from by
          refine ⟨by norm_num, ⟨47320293456231523120046, by norm_num⟩, by norm_num, ⟨17745110046086821170017, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 35490220092173642340035 53235330138260463510053 1 from by
          refine ⟨by norm_num, ⟨17745110046086821170017, by norm_num⟩, by norm_num, ⟨26617665069130231755026, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 53235330138260463510053 9981624400923836908135 4 from by
          refine ⟨by norm_num, ⟨26617665069130231755026, by norm_num⟩, by norm_num, ⟨4990812200461918454067, by norm_num⟩⟩)
        (Word.nil 9981624400923836908135))))))
theorem full_word_156 : Word word_156 21273707603123681361947 9981624400923836908135 := by
  unfold word_156
  have hp := shared_prefix_all 36904
  have ht := suffix_proof_156
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_156 : word_156.length = 46 := by decide
theorem word_sum_156 : word_156.sum = 74 := by decide
theorem infinite_family_156 (d : Nat) :
    ∃ z : Nat, Word word_156 (21273707603123681361947 + 2^75*d) z ∧
      z < 21273707603123681361947 + 2^75*d := by
  have h := word_uniform_descent full_word_156
    (show 9981624400923836908135 < 21273707603123681361947 by norm_num)
    (show 3^word_156.length < 2^word_156.sum by norm_num [word_156, sharedPrefix, suffix_156]) d
  simpa [word_sum_156] using h

/-- Certificate 157; shared prefix plus independently witnessed suffix. -/
def suffix_157 : List Nat := [2, 1, 5, 3, 1, 3]
def word_157 : List Nat := sharedPrefix ++ suffix_157
theorem suffix_proof_157 : Word suffix_157 498950590444679588066009 11100310682195172720341 := by
  unfold suffix_157
  exact Word.cons
        (show ExactStep 498950590444679588066009 374212942833509691049507 2 from by
          refine ⟨by norm_num, ⟨249475295222339794033004, by norm_num⟩, by norm_num, ⟨187106471416754845524753, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 374212942833509691049507 561319414250264536574261 1 from by
          refine ⟨by norm_num, ⟨187106471416754845524753, by norm_num⟩, by norm_num, ⟨280659707125132268287130, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 561319414250264536574261 52623695085962300303837 5 from by
          refine ⟨by norm_num, ⟨280659707125132268287130, by norm_num⟩, by norm_num, ⟨26311847542981150151918, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 52623695085962300303837 19733885657235862613939 3 from by
          refine ⟨by norm_num, ⟨26311847542981150151918, by norm_num⟩, by norm_num, ⟨9866942828617931306969, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 19733885657235862613939 29600828485853793920909 1 from by
          refine ⟨by norm_num, ⟨9866942828617931306969, by norm_num⟩, by norm_num, ⟨14800414242926896960454, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 29600828485853793920909 11100310682195172720341 3 from by
          refine ⟨by norm_num, ⟨14800414242926896960454, by norm_num⟩, by norm_num, ⟨5550155341097586360170, by norm_num⟩⟩)
        (Word.nil 11100310682195172720341))))))
theorem full_word_157 : Word word_157 11828974637384390934555 11100310682195172720341 := by
  unfold word_157
  have hp := shared_prefix_all 20520
  have ht := suffix_proof_157
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_157 : word_157.length = 46 := by decide
theorem word_sum_157 : word_157.sum = 73 := by decide
theorem infinite_family_157 (d : Nat) :
    ∃ z : Nat, Word word_157 (11828974637384390934555 + 2^74*d) z ∧
      z < 11828974637384390934555 + 2^74*d := by
  have h := word_uniform_descent full_word_157
    (show 11100310682195172720341 < 11828974637384390934555 by norm_num)
    (show 3^word_157.length < 2^word_157.sum by norm_num [word_157, sharedPrefix, suffix_157]) d
  simpa [word_sum_157] using h

/-- Certificate 158; shared prefix plus independently witnessed suffix. -/
def suffix_158 : List Nat := [2, 1, 5, 3, 2, 2]
def word_158 : List Nat := sharedPrefix ++ suffix_158
theorem suffix_proof_158 : Word suffix_158 50770410962004964745945 1129505297586108987421 := by
  unfold suffix_158
  exact Word.cons
        (show ExactStep 50770410962004964745945 38077808221503723559459 2 from by
          refine ⟨by norm_num, ⟨25385205481002482372972, by norm_num⟩, by norm_num, ⟨19038904110751861779729, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 38077808221503723559459 57116712332255585339189 1 from by
          refine ⟨by norm_num, ⟨19038904110751861779729, by norm_num⟩, by norm_num, ⟨28558356166127792669594, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 57116712332255585339189 5354691781148961125549 5 from by
          refine ⟨by norm_num, ⟨28558356166127792669594, by norm_num⟩, by norm_num, ⟨2677345890574480562774, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 5354691781148961125549 2008009417930860422081 3 from by
          refine ⟨by norm_num, ⟨2677345890574480562774, by norm_num⟩, by norm_num, ⟨1004004708965430211040, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2008009417930860422081 1506007063448145316561 2 from by
          refine ⟨by norm_num, ⟨1004004708965430211040, by norm_num⟩, by norm_num, ⟨753003531724072658280, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1506007063448145316561 1129505297586108987421 2 from by
          refine ⟨by norm_num, ⟨753003531724072658280, by norm_num⟩, by norm_num, ⟨564752648793054493710, by norm_num⟩⟩)
        (Word.nil 1129505297586108987421))))))
theorem full_word_158 : Word word_158 1203650050927689203739 1129505297586108987421 := by
  unfold word_158
  have hp := shared_prefix_all 2088
  have ht := suffix_proof_158
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_158 : word_158.length = 46 := by decide
theorem word_sum_158 : word_158.sum = 73 := by decide
theorem infinite_family_158 (d : Nat) :
    ∃ z : Nat, Word word_158 (1203650050927689203739 + 2^74*d) z ∧
      z < 1203650050927689203739 + 2^74*d := by
  have h := word_uniform_descent full_word_158
    (show 1129505297586108987421 < 1203650050927689203739 by norm_num)
    (show 3^word_158.length < 2^word_158.sum by norm_num [word_158, sharedPrefix, suffix_158]) d
  simpa [word_sum_158] using h

/-- Certificate 159; shared prefix plus independently witnessed suffix. -/
def suffix_159 : List Nat := [2, 1, 5, 3, 2, 3]
def word_159 : List Nat := sharedPrefix ++ suffix_159
theorem suffix_proof_159 : Word suffix_159 449152792724382407697113 4996221708619305041675 := by
  unfold suffix_159
  exact Word.cons
        (show ExactStep 449152792724382407697113 336864594543286805772835 2 from by
          refine ⟨by norm_num, ⟨224576396362191203848556, by norm_num⟩, by norm_num, ⟨168432297271643402886417, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 336864594543286805772835 505296891814930208659253 1 from by
          refine ⟨by norm_num, ⟨168432297271643402886417, by norm_num⟩, by norm_num, ⟨252648445907465104329626, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 505296891814930208659253 47371583607649707061805 5 from by
          refine ⟨by norm_num, ⟨252648445907465104329626, by norm_num⟩, by norm_num, ⟨23685791803824853530902, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 47371583607649707061805 17764343852868640148177 3 from by
          refine ⟨by norm_num, ⟨23685791803824853530902, by norm_num⟩, by norm_num, ⟨8882171926434320074088, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 17764343852868640148177 13323257889651480111133 2 from by
          refine ⟨by norm_num, ⟨8882171926434320074088, by norm_num⟩, by norm_num, ⟨6661628944825740055566, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 13323257889651480111133 4996221708619305041675 3 from by
          refine ⟨by norm_num, ⟨6661628944825740055566, by norm_num⟩, by norm_num, ⟨2498110854309652520837, by norm_num⟩⟩)
        (Word.nil 4996221708619305041675))))))
theorem full_word_159 : Word word_159 10648383016666979631131 4996221708619305041675 := by
  unfold word_159
  have hp := shared_prefix_all 18472
  have ht := suffix_proof_159
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_159 : word_159.length = 46 := by decide
theorem word_sum_159 : word_159.sum = 74 := by decide
theorem infinite_family_159 (d : Nat) :
    ∃ z : Nat, Word word_159 (10648383016666979631131 + 2^75*d) z ∧
      z < 10648383016666979631131 + 2^75*d := by
  have h := word_uniform_descent full_word_159
    (show 4996221708619305041675 < 10648383016666979631131 by norm_num)
    (show 3^word_159.length < 2^word_159.sum by norm_num [word_159, sharedPrefix, suffix_159]) d
  simpa [word_sum_159] using h

/-- Certificate 160; shared prefix plus independently witnessed suffix. -/
def suffix_160 : List Nat := [2, 1, 5, 3, 4]
def word_160 : List Nat := sharedPrefix ++ suffix_160
theorem suffix_proof_160 : Word suffix_160 150366006402599325483737 1115079942499744753801 := by
  unfold suffix_160
  exact Word.cons
        (show ExactStep 150366006402599325483737 112774504801949494112803 2 from by
          refine ⟨by norm_num, ⟨75183003201299662741868, by norm_num⟩, by norm_num, ⟨56387252400974747056401, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 112774504801949494112803 169161757202924241169205 1 from by
          refine ⟨by norm_num, ⟨56387252400974747056401, by norm_num⟩, by norm_num, ⟨84580878601462120584602, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 169161757202924241169205 15858914737774147609613 5 from by
          refine ⟨by norm_num, ⟨84580878601462120584602, by norm_num⟩, by norm_num, ⟨7929457368887073804806, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 15858914737774147609613 5947093026665305353605 3 from by
          refine ⟨by norm_num, ⟨7929457368887073804806, by norm_num⟩, by norm_num, ⟨2973546513332652676802, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 5947093026665305353605 1115079942499744753801 4 from by
          refine ⟨by norm_num, ⟨2973546513332652676802, by norm_num⟩, by norm_num, ⟨557539971249872376900, by norm_num⟩⟩)
        (Word.nil 1115079942499744753801)))))
theorem full_word_160 : Word word_160 3564833292362511810587 1115079942499744753801 := by
  unfold word_160
  have hp := shared_prefix_all 6184
  have ht := suffix_proof_160
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_160 : word_160.length = 45 := by decide
theorem word_sum_160 : word_160.sum = 73 := by decide
theorem infinite_family_160 (d : Nat) :
    ∃ z : Nat, Word word_160 (3564833292362511810587 + 2^74*d) z ∧
      z < 3564833292362511810587 + 2^74*d := by
  have h := word_uniform_descent full_word_160
    (show 1115079942499744753801 < 3564833292362511810587 by norm_num)
    (show 3^word_160.length < 2^word_160.sum by norm_num [word_160, sharedPrefix, suffix_160]) d
  simpa [word_sum_160] using h

/-- Certificate 161; shared prefix plus independently witnessed suffix. -/
def suffix_161 : List Nat := [2, 1, 5, 3, 5]
def word_161 : List Nat := sharedPrefix ++ suffix_161
theorem suffix_proof_161 : Word suffix_161 1345513151689731654337241 4989009031076122924865 := by
  unfold suffix_161
  exact Word.cons
        (show ExactStep 1345513151689731654337241 1009134863767298740752931 2 from by
          refine ⟨by norm_num, ⟨672756575844865827168620, by norm_num⟩, by norm_num, ⟨504567431883649370376465, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1009134863767298740752931 1513702295650948111129397 1 from by
          refine ⟨by norm_num, ⟨504567431883649370376465, by norm_num⟩, by norm_num, ⟨756851147825474055564698, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1513702295650948111129397 141909590217276385418381 5 from by
          refine ⟨by norm_num, ⟨756851147825474055564698, by norm_num⟩, by norm_num, ⟨70954795108638192709190, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 141909590217276385418381 53216096331478644531893 3 from by
          refine ⟨by norm_num, ⟨70954795108638192709190, by norm_num⟩, by norm_num, ⟨26608048165739322265946, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 53216096331478644531893 4989009031076122924865 5 from by
          refine ⟨by norm_num, ⟨26608048165739322265946, by norm_num⟩, by norm_num, ⟨2494504515538061462432, by norm_num⟩⟩)
        (Word.nil 4989009031076122924865)))))
theorem full_word_161 : Word word_161 31899032189580383092763 4989009031076122924865 := by
  unfold word_161
  have hp := shared_prefix_all 55336
  have ht := suffix_proof_161
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_161 : word_161.length = 45 := by decide
theorem word_sum_161 : word_161.sum = 74 := by decide
theorem infinite_family_161 (d : Nat) :
    ∃ z : Nat, Word word_161 (31899032189580383092763 + 2^75*d) z ∧
      z < 31899032189580383092763 + 2^75*d := by
  have h := word_uniform_descent full_word_161
    (show 4989009031076122924865 < 31899032189580383092763 by norm_num)
    (show 3^word_161.length < 2^word_161.sum by norm_num [word_161, sharedPrefix, suffix_161]) d
  simpa [word_sum_161] using h

/-- Certificate 162; shared prefix plus independently witnessed suffix. -/
def suffix_162 : List Nat := [2, 1, 5, 3, 3]
def word_162 : List Nat := sharedPrefix ++ suffix_162
theorem suffix_proof_162 : Word suffix_162 349557197283788046959321 5184472591550323206245 := by
  unfold suffix_162
  exact Word.cons
        (show ExactStep 349557197283788046959321 262167897962841035219491 2 from by
          refine ⟨by norm_num, ⟨174778598641894023479660, by norm_num⟩, by norm_num, ⟨131083948981420517609745, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 262167897962841035219491 393251846944261552829237 1 from by
          refine ⟨by norm_num, ⟨131083948981420517609745, by norm_num⟩, by norm_num, ⟨196625923472130776414618, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 393251846944261552829237 36867360651024520577741 5 from by
          refine ⟨by norm_num, ⟨196625923472130776414618, by norm_num⟩, by norm_num, ⟨18433680325512260288870, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 36867360651024520577741 13825260244134195216653 3 from by
          refine ⟨by norm_num, ⟨18433680325512260288870, by norm_num⟩, by norm_num, ⟨6912630122067097608326, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 13825260244134195216653 5184472591550323206245 3 from by
          refine ⟨by norm_num, ⟨6912630122067097608326, by norm_num⟩, by norm_num, ⟨2592236295775161603122, by norm_num⟩⟩)
        (Word.nil 5184472591550323206245)))))
theorem full_word_162 : Word word_162 8287199775232157024283 5184472591550323206245 := by
  unfold word_162
  have hp := shared_prefix_all 14376
  have ht := suffix_proof_162
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_162 : word_162.length = 45 := by decide
theorem word_sum_162 : word_162.sum = 72 := by decide
theorem infinite_family_162 (d : Nat) :
    ∃ z : Nat, Word word_162 (8287199775232157024283 + 2^73*d) z ∧
      z < 8287199775232157024283 + 2^73*d := by
  have h := word_uniform_descent full_word_162
    (show 5184472591550323206245 < 8287199775232157024283 by norm_num)
    (show 3^word_162.length < 2^word_162.sum by norm_num [word_162, sharedPrefix, suffix_162]) d
  simpa [word_sum_162] using h

/-- Certificate 163; shared prefix plus independently witnessed suffix. -/
def suffix_163 : List Nat := [2, 1, 5, 7]
def word_163 : List Nat := sharedPrefix ++ suffix_163
theorem suffix_proof_163 : Word suffix_163 25871512101856374561497 63952407234203074325 := by
  unfold suffix_163
  exact Word.cons
        (show ExactStep 25871512101856374561497 19403634076392280921123 2 from by
          refine ⟨by norm_num, ⟨12935756050928187280748, by norm_num⟩, by norm_num, ⟨9701817038196140460561, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 19403634076392280921123 29105451114588421381685 1 from by
          refine ⟨by norm_num, ⟨9701817038196140460561, by norm_num⟩, by norm_num, ⟨14552725557294210690842, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 29105451114588421381685 2728636041992664504533 5 from by
          refine ⟨by norm_num, ⟨14552725557294210690842, by norm_num⟩, by norm_num, ⟨1364318020996332252266, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2728636041992664504533 63952407234203074325 7 from by
          refine ⟨by norm_num, ⟨1364318020996332252266, by norm_num⟩, by norm_num, ⟨31976203617101537162, by norm_num⟩⟩)
        (Word.nil 63952407234203074325))))
theorem full_word_163 : Word word_163 613354240568983552027 63952407234203074325 := by
  unfold word_163
  have hp := shared_prefix_all 1064
  have ht := suffix_proof_163
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_163 : word_163.length = 44 := by decide
theorem word_sum_163 : word_163.sum = 73 := by decide
theorem infinite_family_163 (d : Nat) :
    ∃ z : Nat, Word word_163 (613354240568983552027 + 2^74*d) z ∧
      z < 613354240568983552027 + 2^74*d := by
  have h := word_uniform_descent full_word_163
    (show 63952407234203074325 < 613354240568983552027 by norm_num)
    (show 3^word_163.length < 2^word_163.sum by norm_num [word_163, sharedPrefix, suffix_163]) d
  simpa [word_sum_163] using h

/-- Certificate 164; shared prefix plus independently witnessed suffix. -/
def suffix_164 : List Nat := [2, 1, 5, 8]
def word_164 : List Nat := sharedPrefix ++ suffix_164
theorem suffix_proof_164 : Word suffix_164 424253893864233817512665 524361654708907153603 := by
  unfold suffix_164
  exact Word.cons
        (show ExactStep 424253893864233817512665 318190420398175363134499 2 from by
          refine ⟨by norm_num, ⟨212126946932116908756332, by norm_num⟩, by norm_num, ⟨159095210199087681567249, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 318190420398175363134499 477285630597263044701749 1 from by
          refine ⟨by norm_num, ⟨159095210199087681567249, by norm_num⟩, by norm_num, ⟨238642815298631522350874, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 477285630597263044701749 44745527868493410440789 5 from by
          refine ⟨by norm_num, ⟨238642815298631522350874, by norm_num⟩, by norm_num, ⟨22372763934246705220394, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 44745527868493410440789 524361654708907153603 8 from by
          refine ⟨by norm_num, ⟨22372763934246705220394, by norm_num⟩, by norm_num, ⟨262180827354453576801, by norm_num⟩⟩)
        (Word.nil 524361654708907153603))))
theorem full_word_164 : Word word_164 10058087206308273979419 524361654708907153603 := by
  unfold word_164
  have hp := shared_prefix_all 17448
  have ht := suffix_proof_164
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_164 : word_164.length = 44 := by decide
theorem word_sum_164 : word_164.sum = 74 := by decide
theorem infinite_family_164 (d : Nat) :
    ∃ z : Nat, Word word_164 (10058087206308273979419 + 2^75*d) z ∧
      z < 10058087206308273979419 + 2^75*d := by
  have h := word_uniform_descent full_word_164
    (show 524361654708907153603 < 10058087206308273979419 by norm_num)
    (show 3^word_164.length < 2^word_164.sum by norm_num [word_164, sharedPrefix, suffix_164]) d
  simpa [word_sum_164] using h

/-- Certificate 165; shared prefix plus independently witnessed suffix. -/
def suffix_165 : List Nat := [2, 1, 5, 6]
def word_165 : List Nat := sharedPrefix ++ suffix_165
theorem suffix_proof_165 : Word suffix_165 225062702983045096037081 1112675716652017381531 := by
  unfold suffix_165
  exact Word.cons
        (show ExactStep 225062702983045096037081 168797027237283822027811 2 from by
          refine ⟨by norm_num, ⟨112531351491522548018540, by norm_num⟩, by norm_num, ⟨84398513618641911013905, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 168797027237283822027811 253195540855925733041717 1 from by
          refine ⟨by norm_num, ⟨84398513618641911013905, by norm_num⟩, by norm_num, ⟨126597770427962866520858, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 253195540855925733041717 23737081955243037472661 5 from by
          refine ⟨by norm_num, ⟨126597770427962866520858, by norm_num⟩, by norm_num, ⟨11868540977621518736330, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 23737081955243037472661 1112675716652017381531 6 from by
          refine ⟨by norm_num, ⟨11868540977621518736330, by norm_num⟩, by norm_num, ⟨556337858326008690765, by norm_num⟩⟩)
        (Word.nil 1112675716652017381531))))
theorem full_word_165 : Word word_165 5335720723438628765723 1112675716652017381531 := by
  unfold word_165
  have hp := shared_prefix_all 9256
  have ht := suffix_proof_165
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_165 : word_165.length = 44 := by decide
theorem word_sum_165 : word_165.sum = 72 := by decide
theorem infinite_family_165 (d : Nat) :
    ∃ z : Nat, Word word_165 (5335720723438628765723 + 2^73*d) z ∧
      z < 5335720723438628765723 + 2^73*d := by
  have h := word_uniform_descent full_word_165
    (show 1112675716652017381531 < 5335720723438628765723 by norm_num)
    (show 3^word_165.length < 2^word_165.sum by norm_num [word_165, sharedPrefix, suffix_165]) d
  simpa [word_sum_165] using h

/-- Certificate 166; shared prefix plus independently witnessed suffix. -/
def suffix_166 : List Nat := [2, 1, 5, 5]
def word_166 : List Nat := sharedPrefix ++ suffix_166
theorem suffix_proof_166 : Word suffix_166 125467107542450735299289 1240580531120423530181 := by
  unfold suffix_166
  exact Word.cons
        (show ExactStep 125467107542450735299289 94100330656838051474467 2 from by
          refine ⟨by norm_num, ⟨62733553771225367649644, by norm_num⟩, by norm_num, ⟨47050165328419025737233, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 94100330656838051474467 141150495985257077211701 1 from by
          refine ⟨by norm_num, ⟨47050165328419025737233, by norm_num⟩, by norm_num, ⟨70575247992628538605850, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 141150495985257077211701 13232858998617850988597 5 from by
          refine ⟨by norm_num, ⟨70575247992628538605850, by norm_num⟩, by norm_num, ⟨6616429499308925494298, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 13232858998617850988597 1240580531120423530181 5 from by
          refine ⟨by norm_num, ⟨6616429499308925494298, by norm_num⟩, by norm_num, ⟨620290265560211765090, by norm_num⟩⟩)
        (Word.nil 1240580531120423530181))))
theorem full_word_166 : Word word_166 2974537482003806158875 1240580531120423530181 := by
  unfold word_166
  have hp := shared_prefix_all 5160
  have ht := suffix_proof_166
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_166 : word_166.length = 44 := by decide
theorem word_sum_166 : word_166.sum = 71 := by decide
theorem infinite_family_166 (d : Nat) :
    ∃ z : Nat, Word word_166 (2974537482003806158875 + 2^72*d) z ∧
      z < 2974537482003806158875 + 2^72*d := by
  have h := word_uniform_descent full_word_166
    (show 1240580531120423530181 < 2974537482003806158875 by norm_num)
    (show 3^word_166.length < 2^word_166.sum by norm_num [word_166, sharedPrefix, suffix_166]) d
  simpa [word_sum_166] using h

/-- Certificate 167; shared prefix plus independently witnessed suffix. -/
def suffix_167 : List Nat := [2, 1, 5, 4]
def word_167 : List Nat := sharedPrefix ++ suffix_167
theorem suffix_proof_167 : Word suffix_167 75669309822153554930393 1496390160057235827481 := by
  unfold suffix_167
  exact Word.cons
        (show ExactStep 75669309822153554930393 56751982366615166197795 2 from by
          refine ⟨by norm_num, ⟨37834654911076777465196, by norm_num⟩, by norm_num, ⟨28375991183307583098897, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 56751982366615166197795 85127973549922749296693 1 from by
          refine ⟨by norm_num, ⟨28375991183307583098897, by norm_num⟩, by norm_num, ⟨42563986774961374648346, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 85127973549922749296693 7980747520305257746565 5 from by
          refine ⟨by norm_num, ⟨42563986774961374648346, by norm_num⟩, by norm_num, ⟨3990373760152628873282, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 7980747520305257746565 1496390160057235827481 4 from by
          refine ⟨by norm_num, ⟨3990373760152628873282, by norm_num⟩, by norm_num, ⟨748195080028617913740, by norm_num⟩⟩)
        (Word.nil 1496390160057235827481))))
theorem full_word_167 : Word word_167 1793945861286394855451 1496390160057235827481 := by
  unfold word_167
  have hp := shared_prefix_all 3112
  have ht := suffix_proof_167
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_167 : word_167.length = 44 := by decide
theorem word_sum_167 : word_167.sum = 70 := by decide
theorem infinite_family_167 (d : Nat) :
    ∃ z : Nat, Word word_167 (1793945861286394855451 + 2^71*d) z ∧
      z < 1793945861286394855451 + 2^71*d := by
  have h := word_uniform_descent full_word_167
    (show 1496390160057235827481 < 1793945861286394855451 by norm_num)
    (show 3^word_167.length < 2^word_167.sum by norm_num [word_167, sharedPrefix, suffix_167]) d
  simpa [word_sum_167] using h

/-- Certificate 168; shared prefix plus independently witnessed suffix. -/
def suffix_168 : List Nat := [2, 1, 5, 2, 1, 4]
def word_168 : List Nat := sharedPrefix ++ suffix_168
theorem suffix_proof_168 : Word suffix_168 262411051273267981313753 5837941173651500194633 := by
  unfold suffix_168
  exact Word.cons
        (show ExactStep 262411051273267981313753 196808288454950985985315 2 from by
          refine ⟨by norm_num, ⟨131205525636633990656876, by norm_num⟩, by norm_num, ⟨98404144227475492992657, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 196808288454950985985315 295212432682426478977973 1 from by
          refine ⟨by norm_num, ⟨98404144227475492992657, by norm_num⟩, by norm_num, ⟨147606216341213239488986, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 295212432682426478977973 27676165563977482404185 5 from by
          refine ⟨by norm_num, ⟨147606216341213239488986, by norm_num⟩, by norm_num, ⟨13838082781988741202092, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 27676165563977482404185 20757124172983111803139 2 from by
          refine ⟨by norm_num, ⟨13838082781988741202092, by norm_num⟩, by norm_num, ⟨10378562086491555901569, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 20757124172983111803139 31135686259474667704709 1 from by
          refine ⟨by norm_num, ⟨10378562086491555901569, by norm_num⟩, by norm_num, ⟨15567843129737333852354, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 31135686259474667704709 5837941173651500194633 4 from by
          refine ⟨by norm_num, ⟨15567843129737333852354, by norm_num⟩, by norm_num, ⟨2918970586825750097316, by norm_num⟩⟩)
        (Word.nil 5837941173651500194633))))))
theorem full_word_168 : Word word_168 6221164438976687243291 5837941173651500194633 := by
  unfold word_168
  have hp := shared_prefix_all 10792
  have ht := suffix_proof_168
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_168 : word_168.length = 46 := by decide
theorem word_sum_168 : word_168.sum = 73 := by decide
theorem infinite_family_168 (d : Nat) :
    ∃ z : Nat, Word word_168 (6221164438976687243291 + 2^74*d) z ∧
      z < 6221164438976687243291 + 2^74*d := by
  have h := word_uniform_descent full_word_168
    (show 5837941173651500194633 < 6221164438976687243291 by norm_num)
    (show 3^word_168.length < 2^word_168.sum by norm_num [word_168, sharedPrefix, suffix_168]) d
  simpa [word_sum_168] using h

/-- Certificate 169; shared prefix plus independently witnessed suffix. -/
def suffix_169 : List Nat := [2, 1, 5, 2, 1, 5]
def word_169 : List Nat := sharedPrefix ++ suffix_169
theorem suffix_proof_169 : Word suffix_169 660793433035645424264921 7350439646652000645281 := by
  unfold suffix_169
  exact Word.cons
        (show ExactStep 660793433035645424264921 495595074776734068198691 2 from by
          refine ⟨by norm_num, ⟨330396716517822712132460, by norm_num⟩, by norm_num, ⟨247797537388367034099345, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 495595074776734068198691 743392612165101102298037 1 from by
          refine ⟨by norm_num, ⟨247797537388367034099345, by norm_num⟩, by norm_num, ⟨371696306082550551149018, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 743392612165101102298037 69693057390478228340441 5 from by
          refine ⟨by norm_num, ⟨371696306082550551149018, by norm_num⟩, by norm_num, ⟨34846528695239114170220, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 69693057390478228340441 52269793042858671255331 2 from by
          refine ⟨by norm_num, ⟨34846528695239114170220, by norm_num⟩, by norm_num, ⟨26134896521429335627665, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 52269793042858671255331 78404689564288006882997 1 from by
          refine ⟨by norm_num, ⟨26134896521429335627665, by norm_num⟩, by norm_num, ⟨39202344782144003441498, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 78404689564288006882997 7350439646652000645281 5 from by
          refine ⟨by norm_num, ⟨39202344782144003441498, by norm_num⟩, by norm_num, ⟨3675219823326000322640, by norm_num⟩⟩)
        (Word.nil 7350439646652000645281))))))
theorem full_word_169 : Word word_169 15665897404715977670683 7350439646652000645281 := by
  unfold word_169
  have hp := shared_prefix_all 27176
  have ht := suffix_proof_169
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_169 : word_169.length = 46 := by decide
theorem word_sum_169 : word_169.sum = 74 := by decide
theorem infinite_family_169 (d : Nat) :
    ∃ z : Nat, Word word_169 (15665897404715977670683 + 2^75*d) z ∧
      z < 15665897404715977670683 + 2^75*d := by
  have h := word_uniform_descent full_word_169
    (show 7350439646652000645281 < 15665897404715977670683 by norm_num)
    (show 3^word_169.length < 2^word_169.sum by norm_num [word_169, sharedPrefix, suffix_169]) d
  simpa [word_sum_169] using h

/-- Certificate 170; shared prefix plus independently witnessed suffix. -/
def suffix_170 : List Nat := [2, 1, 5, 2, 2, 3]
def word_170 : List Nat := sharedPrefix ++ suffix_170
theorem suffix_proof_170 : Word suffix_170 38320961531930669653721 852538481346968328173 := by
  unfold suffix_170
  exact Word.cons
        (show ExactStep 38320961531930669653721 28740721148948002240291 2 from by
          refine ⟨by norm_num, ⟨19160480765965334826860, by norm_num⟩, by norm_num, ⟨14370360574474001120145, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 28740721148948002240291 43111081723422003360437 1 from by
          refine ⟨by norm_num, ⟨14370360574474001120145, by norm_num⟩, by norm_num, ⟨21555540861711001680218, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 43111081723422003360437 4041663911570812815041 5 from by
          refine ⟨by norm_num, ⟨21555540861711001680218, by norm_num⟩, by norm_num, ⟨2020831955785406407520, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 4041663911570812815041 3031247933678109611281 2 from by
          refine ⟨by norm_num, ⟨2020831955785406407520, by norm_num⟩, by norm_num, ⟨1515623966839054805640, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 3031247933678109611281 2273435950258582208461 2 from by
          refine ⟨by norm_num, ⟨1515623966839054805640, by norm_num⟩, by norm_num, ⟨1136717975129291104230, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2273435950258582208461 852538481346968328173 3 from by
          refine ⟨by norm_num, ⟨1136717975129291104230, by norm_num⟩, by norm_num, ⟨426269240673484164086, by norm_num⟩⟩)
        (Word.nil 852538481346968328173))))))
theorem full_word_170 : Word word_170 908502145748336377883 852538481346968328173 := by
  unfold word_170
  have hp := shared_prefix_all 1576
  have ht := suffix_proof_170
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_170 : word_170.length = 46 := by decide
theorem word_sum_170 : word_170.sum = 73 := by decide
theorem infinite_family_170 (d : Nat) :
    ∃ z : Nat, Word word_170 (908502145748336377883 + 2^74*d) z ∧
      z < 908502145748336377883 + 2^74*d := by
  have h := word_uniform_descent full_word_170
    (show 852538481346968328173 < 908502145748336377883 by norm_num)
    (show 3^word_170.length < 2^word_170.sum by norm_num [word_170, sharedPrefix, suffix_170]) d
  simpa [word_sum_170] using h

/-- Certificate 171; shared prefix plus independently witnessed suffix. -/
def suffix_171 : List Nat := [2, 1, 5, 2, 2, 4]
def word_171 : List Nat := sharedPrefix ++ suffix_171
theorem suffix_proof_171 : Word suffix_171 436703343294308112604889 4857738300499734712051 := by
  unfold suffix_171
  exact Word.cons
        (show ExactStep 436703343294308112604889 327527507470731084453667 2 from by
          refine ⟨by norm_num, ⟨218351671647154056302444, by norm_num⟩, by norm_num, ⟨163763753735365542226833, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 327527507470731084453667 491291261206096626680501 1 from by
          refine ⟨by norm_num, ⟨163763753735365542226833, by norm_num⟩, by norm_num, ⟨245645630603048313340250, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 491291261206096626680501 46058555738071558751297 5 from by
          refine ⟨by norm_num, ⟨245645630603048313340250, by norm_num⟩, by norm_num, ⟨23029277869035779375648, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 46058555738071558751297 34543916803553669063473 2 from by
          refine ⟨by norm_num, ⟨23029277869035779375648, by norm_num⟩, by norm_num, ⟨17271958401776834531736, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 34543916803553669063473 25907937602665251797605 2 from by
          refine ⟨by norm_num, ⟨17271958401776834531736, by norm_num⟩, by norm_num, ⟨12953968801332625898802, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 25907937602665251797605 4857738300499734712051 4 from by
          refine ⟨by norm_num, ⟨12953968801332625898802, by norm_num⟩, by norm_num, ⟨2428869150249867356025, by norm_num⟩⟩)
        (Word.nil 4857738300499734712051))))))
theorem full_word_171 : Word word_171 10353235111487626805275 4857738300499734712051 := by
  unfold word_171
  have hp := shared_prefix_all 17960
  have ht := suffix_proof_171
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_171 : word_171.length = 46 := by decide
theorem word_sum_171 : word_171.sum = 74 := by decide
theorem infinite_family_171 (d : Nat) :
    ∃ z : Nat, Word word_171 (10353235111487626805275 + 2^75*d) z ∧
      z < 10353235111487626805275 + 2^75*d := by
  have h := word_uniform_descent full_word_171
    (show 4857738300499734712051 < 10353235111487626805275 by norm_num)
    (show 3^word_171.length < 2^word_171.sum by norm_num [word_171, sharedPrefix, suffix_171]) d
  simpa [word_sum_171] using h

/-- Certificate 172; shared prefix plus independently witnessed suffix. -/
def suffix_172 : List Nat := [2, 1, 5, 2, 6]
def word_172 : List Nat := sharedPrefix ++ suffix_172
theorem suffix_proof_172 : Word suffix_172 884883522776982735924953 3281046997601422192837 := by
  unfold suffix_172
  exact Word.cons
        (show ExactStep 884883522776982735924953 663662642082737051943715 2 from by
          refine ⟨by norm_num, ⟨442441761388491367962476, by norm_num⟩, by norm_num, ⟨331831321041368525971857, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 663662642082737051943715 995493963124105577915573 1 from by
          refine ⟨by norm_num, ⟨331831321041368525971857, by norm_num⟩, by norm_num, ⟨497746981562052788957786, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 995493963124105577915573 93327559042884897929585 5 from by
          refine ⟨by norm_num, ⟨497746981562052788957786, by norm_num⟩, by norm_num, ⟨46663779521442448964792, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 93327559042884897929585 69995669282163673447189 2 from by
          refine ⟨by norm_num, ⟨46663779521442448964792, by norm_num⟩, by norm_num, ⟨34997834641081836723594, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 69995669282163673447189 3281046997601422192837 6 from by
          refine ⟨by norm_num, ⟨34997834641081836723594, by norm_num⟩, by norm_num, ⟨1640523498800711096418, by norm_num⟩⟩)
        (Word.nil 3281046997601422192837)))))
theorem full_word_172 : Word word_172 20978559697944328536091 3281046997601422192837 := by
  unfold word_172
  have hp := shared_prefix_all 36392
  have ht := suffix_proof_172
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_172 : word_172.length = 45 := by decide
theorem word_sum_172 : word_172.sum = 74 := by decide
theorem infinite_family_172 (d : Nat) :
    ∃ z : Nat, Word word_172 (20978559697944328536091 + 2^75*d) z ∧
      z < 20978559697944328536091 + 2^75*d := by
  have h := word_uniform_descent full_word_172
    (show 3281046997601422192837 < 20978559697944328536091 by norm_num)
    (show 3^word_172.length < 2^word_172.sum by norm_num [word_172, sharedPrefix, suffix_172]) d
  simpa [word_sum_172] using h

/-- Certificate 173; shared prefix plus independently witnessed suffix. -/
def suffix_173 : List Nat := [2, 1, 5, 2, 5]
def word_173 : List Nat := sharedPrefix ++ suffix_173
theorem suffix_proof_173 : Word suffix_173 486501141014605292973785 3607781288652010687031 := by
  unfold suffix_173
  exact Word.cons
        (show ExactStep 486501141014605292973785 364875855760953969730339 2 from by
          refine ⟨by norm_num, ⟨243250570507302646486892, by norm_num⟩, by norm_num, ⟨182437927880476984865169, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 364875855760953969730339 547313783641430954595509 1 from by
          refine ⟨by norm_num, ⟨182437927880476984865169, by norm_num⟩, by norm_num, ⟨273656891820715477297754, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 547313783641430954595509 51310667216384151993329 5 from by
          refine ⟨by norm_num, ⟨273656891820715477297754, by norm_num⟩, by norm_num, ⟨25655333608192075996664, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 51310667216384151993329 38483000412288113994997 2 from by
          refine ⟨by norm_num, ⟨25655333608192075996664, by norm_num⟩, by norm_num, ⟨19241500206144056997498, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 38483000412288113994997 3607781288652010687031 5 from by
          refine ⟨by norm_num, ⟨19241500206144056997498, by norm_num⟩, by norm_num, ⟨1803890644326005343515, by norm_num⟩⟩)
        (Word.nil 3607781288652010687031)))))
theorem full_word_173 : Word word_173 11533826732205038108699 3607781288652010687031 := by
  unfold word_173
  have hp := shared_prefix_all 20008
  have ht := suffix_proof_173
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_173 : word_173.length = 45 := by decide
theorem word_sum_173 : word_173.sum = 73 := by decide
theorem infinite_family_173 (d : Nat) :
    ∃ z : Nat, Word word_173 (11533826732205038108699 + 2^74*d) z ∧
      z < 11533826732205038108699 + 2^74*d := by
  have h := word_uniform_descent full_word_173
    (show 3607781288652010687031 < 11533826732205038108699 by norm_num)
    (show 3^word_173.length < 2^word_173.sum by norm_num [word_173, sharedPrefix, suffix_173]) d
  simpa [word_sum_173] using h

/-- Certificate 174; shared prefix plus independently witnessed suffix. -/
def suffix_174 : List Nat := [2, 1, 5, 2, 4]
def word_174 : List Nat := sharedPrefix ++ suffix_174
theorem suffix_proof_174 : Word suffix_174 287309950133416571498201 4261249870753187675419 := by
  unfold suffix_174
  exact Word.cons
        (show ExactStep 287309950133416571498201 215482462600062428623651 2 from by
          refine ⟨by norm_num, ⟨143654975066708285749100, by norm_num⟩, by norm_num, ⟨107741231300031214311825, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 215482462600062428623651 323223693900093642935477 1 from by
          refine ⟨by norm_num, ⟨107741231300031214311825, by norm_num⟩, by norm_num, ⟨161611846950046821467738, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 323223693900093642935477 30302221303133779025201 5 from by
          refine ⟨by norm_num, ⟨161611846950046821467738, by norm_num⟩, by norm_num, ⟨15151110651566889512600, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 30302221303133779025201 22726665977350334268901 2 from by
          refine ⟨by norm_num, ⟨15151110651566889512600, by norm_num⟩, by norm_num, ⟨11363332988675167134450, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 22726665977350334268901 4261249870753187675419 4 from by
          refine ⟨by norm_num, ⟨11363332988675167134450, by norm_num⟩, by norm_num, ⟨2130624935376593837709, by norm_num⟩⟩)
        (Word.nil 4261249870753187675419)))))
theorem full_word_174 : Word word_174 6811460249335392895003 4261249870753187675419 := by
  unfold word_174
  have hp := shared_prefix_all 11816
  have ht := suffix_proof_174
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_174 : word_174.length = 45 := by decide
theorem word_sum_174 : word_174.sum = 72 := by decide
theorem infinite_family_174 (d : Nat) :
    ∃ z : Nat, Word word_174 (6811460249335392895003 + 2^73*d) z ∧
      z < 6811460249335392895003 + 2^73*d := by
  have h := word_uniform_descent full_word_174
    (show 4261249870753187675419 < 6811460249335392895003 by norm_num)
    (show 3^word_174.length < 2^word_174.sum by norm_num [word_174, sharedPrefix, suffix_174]) d
  simpa [word_sum_174] using h

/-- Certificate 175; shared prefix plus independently witnessed suffix. -/
def suffix_175 : List Nat := [2, 1, 5, 2, 3, 2]
def word_175 : List Nat := sharedPrefix ++ suffix_175
theorem suffix_proof_175 : Word suffix_175 386905545574010932235993 8607609336042906787111 := by
  unfold suffix_175
  exact Word.cons
        (show ExactStep 386905545574010932235993 290179159180508199176995 2 from by
          refine ⟨by norm_num, ⟨193452772787005466117996, by norm_num⟩, by norm_num, ⟨145089579590254099588497, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 290179159180508199176995 435268738770762298765493 1 from by
          refine ⟨by norm_num, ⟨145089579590254099588497, by norm_num⟩, by norm_num, ⟨217634369385381149382746, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 435268738770762298765493 40806444259758965509265 5 from by
          refine ⟨by norm_num, ⟨217634369385381149382746, by norm_num⟩, by norm_num, ⟨20403222129879482754632, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 40806444259758965509265 30604833194819224131949 2 from by
          refine ⟨by norm_num, ⟨20403222129879482754632, by norm_num⟩, by norm_num, ⟨15302416597409612065974, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 30604833194819224131949 11476812448057209049481 3 from by
          refine ⟨by norm_num, ⟨15302416597409612065974, by norm_num⟩, by norm_num, ⟨5738406224028604524740, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 11476812448057209049481 8607609336042906787111 2 from by
          refine ⟨by norm_num, ⟨5738406224028604524740, by norm_num⟩, by norm_num, ⟨4303804668021453393555, by norm_num⟩⟩)
        (Word.nil 8607609336042906787111))))))
theorem full_word_175 : Word word_175 9172643490770215501851 8607609336042906787111 := by
  unfold word_175
  have hp := shared_prefix_all 15912
  have ht := suffix_proof_175
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_175 : word_175.length = 46 := by decide
theorem word_sum_175 : word_175.sum = 73 := by decide
theorem infinite_family_175 (d : Nat) :
    ∃ z : Nat, Word word_175 (9172643490770215501851 + 2^74*d) z ∧
      z < 9172643490770215501851 + 2^74*d := by
  have h := word_uniform_descent full_word_175
    (show 8607609336042906787111 < 9172643490770215501851 by norm_num)
    (show 3^word_175.length < 2^word_175.sum by norm_num [word_175, sharedPrefix, suffix_175]) d
  simpa [word_sum_175] using h

/-- Certificate 176; shared prefix plus independently witnessed suffix. -/
def suffix_176 : List Nat := [2, 1, 5, 2, 3, 3]
def word_176 : List Nat := sharedPrefix ++ suffix_176
theorem suffix_proof_176 : Word suffix_176 1582052690861143261089497 17598211847500205037449 := by
  unfold suffix_176
  exact Word.cons
        (show ExactStep 1582052690861143261089497 1186539518145857445817123 2 from by
          refine ⟨by norm_num, ⟨791026345430571630544748, by norm_num⟩, by norm_num, ⟨593269759072928722908561, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1186539518145857445817123 1779809277218786168725685 1 from by
          refine ⟨by norm_num, ⟨593269759072928722908561, by norm_num⟩, by norm_num, ⟨889904638609393084362842, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1779809277218786168725685 166857119739261203318033 5 from by
          refine ⟨by norm_num, ⟨889904638609393084362842, by norm_num⟩, by norm_num, ⟨83428559869630601659016, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 166857119739261203318033 125142839804445902488525 2 from by
          refine ⟨by norm_num, ⟨83428559869630601659016, by norm_num⟩, by norm_num, ⟨62571419902222951244262, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 125142839804445902488525 46928564926667213433197 3 from by
          refine ⟨by norm_num, ⟨62571419902222951244262, by norm_num⟩, by norm_num, ⟨23464282463333606716598, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 46928564926667213433197 17598211847500205037449 3 from by
          refine ⟨by norm_num, ⟨23464282463333606716598, by norm_num⟩, by norm_num, ⟨8799105923750102518724, by norm_num⟩⟩)
        (Word.nil 17598211847500205037449))))))
theorem full_word_176 : Word word_176 37506842387988086784027 17598211847500205037449 := by
  unfold word_176
  have hp := shared_prefix_all 65064
  have ht := suffix_proof_176
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_176 : word_176.length = 46 := by decide
theorem word_sum_176 : word_176.sum = 74 := by decide
theorem infinite_family_176 (d : Nat) :
    ∃ z : Nat, Word word_176 (37506842387988086784027 + 2^75*d) z ∧
      z < 37506842387988086784027 + 2^75*d := by
  have h := word_uniform_descent full_word_176
    (show 17598211847500205037449 < 37506842387988086784027 by norm_num)
    (show 3^word_176.length < 2^word_176.sum by norm_num [word_176, sharedPrefix, suffix_176]) d
  simpa [word_sum_176] using h

/-- Certificate 177; shared prefix plus independently witnessed suffix. -/
def suffix_177 : List Nat := [2, 1, 5, 1, 3, 4]
def word_177 : List Nat := sharedPrefix ++ suffix_177
theorem suffix_proof_177 : Word suffix_177 206388528837933653398745 2295795250287683614009 := by
  unfold suffix_177
  exact Word.cons
        (show ExactStep 206388528837933653398745 154791396628450240049059 2 from by
          refine ⟨by norm_num, ⟨103194264418966826699372, by norm_num⟩, by norm_num, ⟨77395698314225120024529, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 154791396628450240049059 232187094942675360073589 1 from by
          refine ⟨by norm_num, ⟨77395698314225120024529, by norm_num⟩, by norm_num, ⟨116093547471337680036794, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 232187094942675360073589 21767540150875815006899 5 from by
          refine ⟨by norm_num, ⟨116093547471337680036794, by norm_num⟩, by norm_num, ⟨10883770075437907503449, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 21767540150875815006899 32651310226313722510349 1 from by
          refine ⟨by norm_num, ⟨10883770075437907503449, by norm_num⟩, by norm_num, ⟨16325655113156861255174, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 32651310226313722510349 12244241334867645941381 3 from by
          refine ⟨by norm_num, ⟨16325655113156861255174, by norm_num⟩, by norm_num, ⟨6122120667433822970690, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 12244241334867645941381 2295795250287683614009 4 from by
          refine ⟨by norm_num, ⟨6122120667433822970690, by norm_num⟩, by norm_num, ⟨1147897625143841807004, by norm_num⟩⟩)
        (Word.nil 2295795250287683614009))))))
theorem full_word_177 : Word word_177 4892998865669599526939 2295795250287683614009 := by
  unfold word_177
  have hp := shared_prefix_all 8488
  have ht := suffix_proof_177
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_177 : word_177.length = 46 := by decide
theorem word_sum_177 : word_177.sum = 74 := by decide
theorem infinite_family_177 (d : Nat) :
    ∃ z : Nat, Word word_177 (4892998865669599526939 + 2^75*d) z ∧
      z < 4892998865669599526939 + 2^75*d := by
  have h := word_uniform_descent full_word_177
    (show 2295795250287683614009 < 4892998865669599526939 by norm_num)
    (show 3^word_177.length < 2^word_177.sum by norm_num [word_177, sharedPrefix, suffix_177]) d
  simpa [word_sum_177] using h

/-- Certificate 178; shared prefix plus independently witnessed suffix. -/
def suffix_178 : List Nat := [2, 1, 5, 1, 3, 3]
def word_178 : List Nat := sharedPrefix ++ suffix_178
theorem suffix_proof_178 : Word suffix_178 604770910600311096349913 13454528620227868323947 := by
  unfold suffix_178
  exact Word.cons
        (show ExactStep 604770910600311096349913 453578182950233322262435 2 from by
          refine ⟨by norm_num, ⟨302385455300155548174956, by norm_num⟩, by norm_num, ⟨226789091475116661131217, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 453578182950233322262435 680367274425349983393653 1 from by
          refine ⟨by norm_num, ⟨226789091475116661131217, by norm_num⟩, by norm_num, ⟨340183637212674991696826, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 680367274425349983393653 63784431977376560943155 5 from by
          refine ⟨by norm_num, ⟨340183637212674991696826, by norm_num⟩, by norm_num, ⟨31892215988688280471577, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 63784431977376560943155 95676647966064841414733 1 from by
          refine ⟨by norm_num, ⟨31892215988688280471577, by norm_num⟩, by norm_num, ⟨47838323983032420707366, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 95676647966064841414733 35878742987274315530525 3 from by
          refine ⟨by norm_num, ⟨47838323983032420707366, by norm_num⟩, by norm_num, ⟨17939371493637157765262, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 35878742987274315530525 13454528620227868323947 3 from by
          refine ⟨by norm_num, ⟨17939371493637157765262, by norm_num⟩, by norm_num, ⟨6727264310113934161973, by norm_num⟩⟩)
        (Word.nil 13454528620227868323947))))))
theorem full_word_178 : Word word_178 14337731831408889954331 13454528620227868323947 := by
  unfold word_178
  have hp := shared_prefix_all 24872
  have ht := suffix_proof_178
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_178 : word_178.length = 46 := by decide
theorem word_sum_178 : word_178.sum = 73 := by decide
theorem infinite_family_178 (d : Nat) :
    ∃ z : Nat, Word word_178 (14337731831408889954331 + 2^74*d) z ∧
      z < 14337731831408889954331 + 2^74*d := by
  have h := word_uniform_descent full_word_178
    (show 13454528620227868323947 < 14337731831408889954331 by norm_num)
    (show 3^word_178.length < 2^word_178.sum by norm_num [word_178, sharedPrefix, suffix_178]) d
  simpa [word_sum_178] using h

/-- Certificate 179; shared prefix plus independently witnessed suffix. -/
def suffix_179 : List Nat := [2, 1, 5, 1, 5]
def word_179 : List Nat := sharedPrefix ++ suffix_179
theorem suffix_proof_179 : Word suffix_179 56995135677042112292057 845325803803786211363 := by
  unfold suffix_179
  exact Word.cons
        (show ExactStep 56995135677042112292057 42746351757781584219043 2 from by
          refine ⟨by norm_num, ⟨28497567838521056146028, by norm_num⟩, by norm_num, ⟨21373175878890792109521, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 42746351757781584219043 64119527636672376328565 1 from by
          refine ⟨by norm_num, ⟨21373175878890792109521, by norm_num⟩, by norm_num, ⟨32059763818336188164282, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 64119527636672376328565 6011205715938035280803 5 from by
          refine ⟨by norm_num, ⟨32059763818336188164282, by norm_num⟩, by norm_num, ⟨3005602857969017640401, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 6011205715938035280803 9016808573907052921205 1 from by
          refine ⟨by norm_num, ⟨3005602857969017640401, by norm_num⟩, by norm_num, ⟨4508404286953526460602, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 9016808573907052921205 845325803803786211363 5 from by
          refine ⟨by norm_num, ⟨4508404286953526460602, by norm_num⟩, by norm_num, ⟨422662901901893105681, by norm_num⟩⟩)
        (Word.nil 845325803803786211363)))))
theorem full_word_179 : Word word_179 1351224003517365616667 845325803803786211363 := by
  unfold word_179
  have hp := shared_prefix_all 2344
  have ht := suffix_proof_179
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_179 : word_179.length = 45 := by decide
theorem word_sum_179 : word_179.sum = 72 := by decide
theorem infinite_family_179 (d : Nat) :
    ∃ z : Nat, Word word_179 (1351224003517365616667 + 2^73*d) z ∧
      z < 1351224003517365616667 + 2^73*d := by
  have h := word_uniform_descent full_word_179
    (show 845325803803786211363 < 1351224003517365616667 by norm_num)
    (show 3^word_179.length < 2^word_179.sum by norm_num [word_179, sharedPrefix, suffix_179]) d
  simpa [word_sum_179] using h

/-- Certificate 180; shared prefix plus independently witnessed suffix. -/
def suffix_180 : List Nat := [2, 1, 5, 1, 6]
def word_180 : List Nat := sharedPrefix ++ suffix_180
theorem suffix_proof_180 : Word suffix_180 256186326558230833767641 1899819255177309955003 := by
  unfold suffix_180
  exact Word.cons
        (show ExactStep 256186326558230833767641 192139744918673125325731 2 from by
          refine ⟨by norm_num, ⟨128093163279115416883820, by norm_num⟩, by norm_num, ⟨96069872459336562662865, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 192139744918673125325731 288209617378009687988597 1 from by
          refine ⟨by norm_num, ⟨96069872459336562662865, by norm_num⟩, by norm_num, ⟨144104808689004843994298, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 288209617378009687988597 27019651629188408248931 5 from by
          refine ⟨by norm_num, ⟨144104808689004843994298, by norm_num⟩, by norm_num, ⟨13509825814594204124465, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 27019651629188408248931 40529477443782612373397 1 from by
          refine ⟨by norm_num, ⟨13509825814594204124465, by norm_num⟩, by norm_num, ⟨20264738721891306186698, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 40529477443782612373397 1899819255177309955003 6 from by
          refine ⟨by norm_num, ⟨20264738721891306186698, by norm_num⟩, by norm_num, ⟨949909627588654977501, by norm_num⟩⟩)
        (Word.nil 1899819255177309955003)))))
theorem full_word_180 : Word word_180 6073590486387010830363 1899819255177309955003 := by
  unfold word_180
  have hp := shared_prefix_all 10536
  have ht := suffix_proof_180
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_180 : word_180.length = 45 := by decide
theorem word_sum_180 : word_180.sum = 73 := by decide
theorem infinite_family_180 (d : Nat) :
    ∃ z : Nat, Word word_180 (6073590486387010830363 + 2^74*d) z ∧
      z < 6073590486387010830363 + 2^74*d := by
  have h := word_uniform_descent full_word_180
    (show 1899819255177309955003 < 6073590486387010830363 by norm_num)
    (show 3^word_180.length < 2^word_180.sum by norm_num [word_180, sharedPrefix, suffix_180]) d
  simpa [word_sum_180] using h

/-- Certificate 181; shared prefix plus independently witnessed suffix. -/
def suffix_181 : List Nat := [2, 1, 5, 1, 7]
def word_181 : List Nat := sharedPrefix ++ suffix_181
theorem suffix_proof_181 : Word suffix_181 654568708320608276718809 2427065980864071826823 := by
  unfold suffix_181
  exact Word.cons
        (show ExactStep 654568708320608276718809 490926531240456207539107 2 from by
          refine ⟨by norm_num, ⟨327284354160304138359404, by norm_num⟩, by norm_num, ⟨245463265620228103769553, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 490926531240456207539107 736389796860684311308661 1 from by
          refine ⟨by norm_num, ⟨245463265620228103769553, by norm_num⟩, by norm_num, ⟨368194898430342155654330, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 736389796860684311308661 69036543455689154185187 5 from by
          refine ⟨by norm_num, ⟨368194898430342155654330, by norm_num⟩, by norm_num, ⟨34518271727844577092593, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 69036543455689154185187 103554815183533731277781 1 from by
          refine ⟨by norm_num, ⟨34518271727844577092593, by norm_num⟩, by norm_num, ⟨51777407591766865638890, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 103554815183533731277781 2427065980864071826823 7 from by
          refine ⟨by norm_num, ⟨51777407591766865638890, by norm_num⟩, by norm_num, ⟨1213532990432035913411, by norm_num⟩⟩)
        (Word.nil 2427065980864071826823)))))
theorem full_word_181 : Word word_181 15518323452126301257755 2427065980864071826823 := by
  unfold word_181
  have hp := shared_prefix_all 26920
  have ht := suffix_proof_181
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_181 : word_181.length = 45 := by decide
theorem word_sum_181 : word_181.sum = 74 := by decide
theorem infinite_family_181 (d : Nat) :
    ∃ z : Nat, Word word_181 (15518323452126301257755 + 2^75*d) z ∧
      z < 15518323452126301257755 + 2^75*d := by
  have h := word_uniform_descent full_word_181
    (show 2427065980864071826823 < 15518323452126301257755 by norm_num)
    (show 3^word_181.length < 2^word_181.sum by norm_num [word_181, sharedPrefix, suffix_181]) d
  simpa [word_sum_181] using h

/-- Certificate 182; shared prefix plus independently witnessed suffix. -/
def suffix_182 : List Nat := [2, 1, 5, 1, 4, 2]
def word_182 : List Nat := sharedPrefix ++ suffix_182
theorem suffix_proof_182 : Word suffix_182 156590731117636473029849 3483723235618804591027 := by
  unfold suffix_182
  exact Word.cons
        (show ExactStep 156590731117636473029849 117443048338227354772387 2 from by
          refine ⟨by norm_num, ⟨78295365558818236514924, by norm_num⟩, by norm_num, ⟨58721524169113677386193, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 117443048338227354772387 176164572507341032158581 1 from by
          refine ⟨by norm_num, ⟨58721524169113677386193, by norm_num⟩, by norm_num, ⟨88082286253670516079290, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 176164572507341032158581 16515428672563221764867 5 from by
          refine ⟨by norm_num, ⟨88082286253670516079290, by norm_num⟩, by norm_num, ⟨8257714336281610882433, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 16515428672563221764867 24773143008844832647301 1 from by
          refine ⟨by norm_num, ⟨8257714336281610882433, by norm_num⟩, by norm_num, ⟨12386571504422416323650, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 24773143008844832647301 4644964314158406121369 4 from by
          refine ⟨by norm_num, ⟨12386571504422416323650, by norm_num⟩, by norm_num, ⟨2322482157079203060684, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 4644964314158406121369 3483723235618804591027 2 from by
          refine ⟨by norm_num, ⟨2322482157079203060684, by norm_num⟩, by norm_num, ⟨1741861617809402295513, by norm_num⟩⟩)
        (Word.nil 3483723235618804591027))))))
theorem full_word_182 : Word word_182 3712407244952188223515 3483723235618804591027 := by
  unfold word_182
  have hp := shared_prefix_all 6440
  have ht := suffix_proof_182
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_182 : word_182.length = 46 := by decide
theorem word_sum_182 : word_182.sum = 73 := by decide
theorem infinite_family_182 (d : Nat) :
    ∃ z : Nat, Word word_182 (3712407244952188223515 + 2^74*d) z ∧
      z < 3712407244952188223515 + 2^74*d := by
  have h := word_uniform_descent full_word_182
    (show 3483723235618804591027 < 3712407244952188223515 by norm_num)
    (show 3^word_182.length < 2^word_182.sum by norm_num [word_182, sharedPrefix, suffix_182]) d
  simpa [word_sum_182] using h

/-- Certificate 183; shared prefix plus independently witnessed suffix. -/
def suffix_183 : List Nat := [2, 1, 5, 1, 4, 3]
def word_183 : List Nat := sharedPrefix ++ suffix_183
theorem suffix_proof_183 : Word suffix_183 1351737876404768801883353 15036268797288153939407 := by
  unfold suffix_183
  exact Word.cons
        (show ExactStep 1351737876404768801883353 1013803407303576601412515 2 from by
          refine ⟨by norm_num, ⟨675868938202384400941676, by norm_num⟩, by norm_num, ⟨506901703651788300706257, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1013803407303576601412515 1520705110955364902118773 1 from by
          refine ⟨by norm_num, ⟨506901703651788300706257, by norm_num⟩, by norm_num, ⟨760352555477682451059386, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1520705110955364902118773 142566104152065459573635 5 from by
          refine ⟨by norm_num, ⟨760352555477682451059386, by norm_num⟩, by norm_num, ⟨71283052076032729786817, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 142566104152065459573635 213849156228098189360453 1 from by
          refine ⟨by norm_num, ⟨71283052076032729786817, by norm_num⟩, by norm_num, ⟨106924578114049094680226, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 213849156228098189360453 40096716792768410505085 4 from by
          refine ⟨by norm_num, ⟨106924578114049094680226, by norm_num⟩, by norm_num, ⟨20048358396384205252542, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 40096716792768410505085 15036268797288153939407 3 from by
          refine ⟨by norm_num, ⟨20048358396384205252542, by norm_num⟩, by norm_num, ⟨7518134398644076969703, by norm_num⟩⟩)
        (Word.nil 15036268797288153939407))))))
theorem full_word_183 : Word word_183 32046606142170059505691 15036268797288153939407 := by
  unfold word_183
  have hp := shared_prefix_all 55592
  have ht := suffix_proof_183
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_183 : word_183.length = 46 := by decide
theorem word_sum_183 : word_183.sum = 74 := by decide
theorem infinite_family_183 (d : Nat) :
    ∃ z : Nat, Word word_183 (32046606142170059505691 + 2^75*d) z ∧
      z < 32046606142170059505691 + 2^75*d := by
  have h := word_uniform_descent full_word_183
    (show 15036268797288153939407 < 32046606142170059505691 by norm_num)
    (show 3^word_183.length < 2^word_183.sum by norm_num [word_183, sharedPrefix, suffix_183]) d
  simpa [word_sum_183] using h

/-- Certificate 184; shared prefix plus independently witnessed suffix. -/
def suffix_184 : List Nat := [2, 1, 5, 1, 2, 4]
def word_184 : List Nat := sharedPrefix ++ suffix_184
theorem suffix_proof_184 : Word suffix_184 32096236816893522107609 714055073227397998549 := by
  unfold suffix_184
  exact Word.cons
        (show ExactStep 32096236816893522107609 24072177612670141580707 2 from by
          refine ⟨by norm_num, ⟨16048118408446761053804, by norm_num⟩, by norm_num, ⟨12036088806335070790353, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 24072177612670141580707 36108266419005212371061 1 from by
          refine ⟨by norm_num, ⟨12036088806335070790353, by norm_num⟩, by norm_num, ⟨18054133209502606185530, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 36108266419005212371061 3385149976781738659787 5 from by
          refine ⟨by norm_num, ⟨18054133209502606185530, by norm_num⟩, by norm_num, ⟨1692574988390869329893, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 3385149976781738659787 5077724965172607989681 1 from by
          refine ⟨by norm_num, ⟨1692574988390869329893, by norm_num⟩, by norm_num, ⟨2538862482586303994840, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 5077724965172607989681 3808293723879455992261 2 from by
          refine ⟨by norm_num, ⟨2538862482586303994840, by norm_num⟩, by norm_num, ⟨1904146861939727996130, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 3808293723879455992261 714055073227397998549 4 from by
          refine ⟨by norm_num, ⟨1904146861939727996130, by norm_num⟩, by norm_num, ⟨357027536613698999274, by norm_num⟩⟩)
        (Word.nil 714055073227397998549))))))
theorem full_word_184 : Word word_184 760928193158659964955 714055073227397998549 := by
  unfold word_184
  have hp := shared_prefix_all 1320
  have ht := suffix_proof_184
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_184 : word_184.length = 46 := by decide
theorem word_sum_184 : word_184.sum = 73 := by decide
theorem infinite_family_184 (d : Nat) :
    ∃ z : Nat, Word word_184 (760928193158659964955 + 2^74*d) z ∧
      z < 760928193158659964955 + 2^74*d := by
  have h := word_uniform_descent full_word_184
    (show 714055073227397998549 < 760928193158659964955 by norm_num)
    (show 3^word_184.length < 2^word_184.sum by norm_num [word_184, sharedPrefix, suffix_184]) d
  simpa [word_sum_184] using h

/-- Certificate 185; shared prefix plus independently witnessed suffix. -/
def suffix_185 : List Nat := [2, 1, 5, 1, 2, 5]
def word_185 : List Nat := sharedPrefix ++ suffix_185
theorem suffix_proof_185 : Word suffix_185 430478618579270965058777 4788496596439949547239 := by
  unfold suffix_185
  exact Word.cons
        (show ExactStep 430478618579270965058777 322858963934453223794083 2 from by
          refine ⟨by norm_num, ⟨215239309289635482529388, by norm_num⟩, by norm_num, ⟨161429481967226611897041, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 322858963934453223794083 484288445901679835691125 1 from by
          refine ⟨by norm_num, ⟨161429481967226611897041, by norm_num⟩, by norm_num, ⟨242144222950839917845562, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 484288445901679835691125 45402041803282484596043 5 from by
          refine ⟨by norm_num, ⟨242144222950839917845562, by norm_num⟩, by norm_num, ⟨22701020901641242298021, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 45402041803282484596043 68103062704923726894065 1 from by
          refine ⟨by norm_num, ⟨22701020901641242298021, by norm_num⟩, by norm_num, ⟨34051531352461863447032, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 68103062704923726894065 51077297028692795170549 2 from by
          refine ⟨by norm_num, ⟨34051531352461863447032, by norm_num⟩, by norm_num, ⟨25538648514346397585274, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 51077297028692795170549 4788496596439949547239 5 from by
          refine ⟨by norm_num, ⟨25538648514346397585274, by norm_num⟩, by norm_num, ⟨2394248298219974773619, by norm_num⟩⟩)
        (Word.nil 4788496596439949547239))))))
theorem full_word_185 : Word word_185 10205661158897950392347 4788496596439949547239 := by
  unfold word_185
  have hp := shared_prefix_all 17704
  have ht := suffix_proof_185
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_185 : word_185.length = 46 := by decide
theorem word_sum_185 : word_185.sum = 74 := by decide
theorem infinite_family_185 (d : Nat) :
    ∃ z : Nat, Word word_185 (10205661158897950392347 + 2^75*d) z ∧
      z < 10205661158897950392347 + 2^75*d := by
  have h := word_uniform_descent full_word_185
    (show 4788496596439949547239 < 10205661158897950392347 by norm_num)
    (show 3^word_185.length < 2^word_185.sum by norm_num [word_185, sharedPrefix, suffix_185]) d
  simpa [word_sum_185] using h

/-- Certificate 186; shared prefix plus independently witnessed suffix. -/
def suffix_186 : List Nat := [2, 1, 5, 1, 1, 5]
def word_186 : List Nat := sharedPrefix ++ suffix_186
theorem suffix_proof_186 : Word suffix_186 144141281687562177937625 3206756419379663931779 := by
  unfold suffix_186
  exact Word.cons
        (show ExactStep 144141281687562177937625 108105961265671633453219 2 from by
          refine ⟨by norm_num, ⟨72070640843781088968812, by norm_num⟩, by norm_num, ⟨54052980632835816726609, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 108105961265671633453219 162158941898507450179829 1 from by
          refine ⟨by norm_num, ⟨54052980632835816726609, by norm_num⟩, by norm_num, ⟨81079470949253725089914, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 162158941898507450179829 15202400802985073454359 5 from by
          refine ⟨by norm_num, ⟨81079470949253725089914, by norm_num⟩, by norm_num, ⟨7601200401492536727179, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 15202400802985073454359 22803601204477610181539 1 from by
          refine ⟨by norm_num, ⟨7601200401492536727179, by norm_num⟩, by norm_num, ⟨11401800602238805090769, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 22803601204477610181539 34205401806716415272309 1 from by
          refine ⟨by norm_num, ⟨11401800602238805090769, by norm_num⟩, by norm_num, ⟨17102700903358207636154, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 34205401806716415272309 3206756419379663931779 5 from by
          refine ⟨by norm_num, ⟨17102700903358207636154, by norm_num⟩, by norm_num, ⟨1603378209689831965889, by norm_num⟩⟩)
        (Word.nil 3206756419379663931779))))))
theorem full_word_186 : Word word_186 3417259339772835397659 3206756419379663931779 := by
  unfold word_186
  have hp := shared_prefix_all 5928
  have ht := suffix_proof_186
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_186 : word_186.length = 46 := by decide
theorem word_sum_186 : word_186.sum = 73 := by decide
theorem infinite_family_186 (d : Nat) :
    ∃ z : Nat, Word word_186 (3417259339772835397659 + 2^74*d) z ∧
      z < 3417259339772835397659 + 2^74*d := by
  have h := word_uniform_descent full_word_186
    (show 3206756419379663931779 < 3417259339772835397659 by norm_num)
    (show 3^word_186.length < 2^word_186.sum by norm_num [word_186, sharedPrefix, suffix_186]) d
  simpa [word_sum_186] using h

/-- Certificate 187; shared prefix plus independently witnessed suffix. -/
def suffix_187 : List Nat := [2, 1, 5, 1, 1, 6]
def word_187 : List Nat := sharedPrefix ++ suffix_187
theorem suffix_proof_187 : Word suffix_187 1339288426974694506791129 14897785389168583609783 := by
  unfold suffix_187
  exact Word.cons
        (show ExactStep 1339288426974694506791129 1004466320231020880093347 2 from by
          refine ⟨by norm_num, ⟨669644213487347253395564, by norm_num⟩, by norm_num, ⟨502233160115510440046673, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1004466320231020880093347 1506699480346531320140021 1 from by
          refine ⟨by norm_num, ⟨502233160115510440046673, by norm_num⟩, by norm_num, ⟨753349740173265660070010, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1506699480346531320140021 141253076282487311263127 5 from by
          refine ⟨by norm_num, ⟨753349740173265660070010, by norm_num⟩, by norm_num, ⟨70626538141243655631563, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 141253076282487311263127 211879614423730966894691 1 from by
          refine ⟨by norm_num, ⟨70626538141243655631563, by norm_num⟩, by norm_num, ⟨105939807211865483447345, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 211879614423730966894691 317819421635596450342037 1 from by
          refine ⟨by norm_num, ⟨105939807211865483447345, by norm_num⟩, by norm_num, ⟨158909710817798225171018, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 317819421635596450342037 14897785389168583609783 6 from by
          refine ⟨by norm_num, ⟨158909710817798225171018, by norm_num⟩, by norm_num, ⟨7448892694584291804891, by norm_num⟩⟩)
        (Word.nil 14897785389168583609783))))))
theorem full_word_187 : Word word_187 31751458236990706679835 14897785389168583609783 := by
  unfold word_187
  have hp := shared_prefix_all 55080
  have ht := suffix_proof_187
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_187 : word_187.length = 46 := by decide
theorem word_sum_187 : word_187.sum = 74 := by decide
theorem infinite_family_187 (d : Nat) :
    ∃ z : Nat, Word word_187 (31751458236990706679835 + 2^75*d) z ∧
      z < 31751458236990706679835 + 2^75*d := by
  have h := word_uniform_descent full_word_187
    (show 14897785389168583609783 < 31751458236990706679835 by norm_num)
    (show 3^word_187.length < 2^word_187.sum by norm_num [word_187, sharedPrefix, suffix_187]) d
  simpa [word_sum_187] using h

/-- Certificate 188; shared prefix plus independently witnessed suffix. -/
def suffix_188 : List Nat := [2, 1, 8]
def word_188 : List Nat := sharedPrefix ++ suffix_188
theorem suffix_proof_188 : Word suffix_188 4084975599226358150105 53854658778863120143 := by
  unfold suffix_188
  exact Word.cons
        (show ExactStep 4084975599226358150105 3063731699419768612579 2 from by
          refine ⟨by norm_num, ⟨2042487799613179075052, by norm_num⟩, by norm_num, ⟨1531865849709884306289, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 3063731699419768612579 4595597549129652918869 1 from by
          refine ⟨by norm_num, ⟨1531865849709884306289, by norm_num⟩, by norm_num, ⟨2297798774564826459434, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 4595597549129652918869 53854658778863120143 8 from by
          refine ⟨by norm_num, ⟨2297798774564826459434, by norm_num⟩, by norm_num, ⟨26927329389431560071, by norm_num⟩⟩)
        (Word.nil 53854658778863120143)))
theorem full_word_188 : Word word_188 96845406505116106779 53854658778863120143 := by
  unfold word_188
  have hp := shared_prefix_all 168
  have ht := suffix_proof_188
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_188 : word_188.length = 43 := by decide
theorem word_sum_188 : word_188.sum = 69 := by decide
theorem infinite_family_188 (d : Nat) :
    ∃ z : Nat, Word word_188 (96845406505116106779 + 2^70*d) z ∧
      z < 96845406505116106779 + 2^70*d := by
  have h := word_uniform_descent full_word_188
    (show 53854658778863120143 < 96845406505116106779 by norm_num)
    (show 3^word_188.length < 2^word_188.sum by norm_num [word_188, sharedPrefix, suffix_188]) d
  simpa [word_sum_188] using h

/-- Certificate 189; shared prefix plus independently witnessed suffix. -/
def suffix_189 : List Nat := [2, 1, 9]
def word_189 : List Nat := sharedPrefix ++ suffix_189
theorem suffix_proof_189 : Word suffix_189 28983874459374948334553 191055813086700098885 := by
  unfold suffix_189
  exact Word.cons
        (show ExactStep 28983874459374948334553 21737905844531211250915 2 from by
          refine ⟨by norm_num, ⟨14491937229687474167276, by norm_num⟩, by norm_num, ⟨10868952922265605625457, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 21737905844531211250915 32606858766796816876373 1 from by
          refine ⟨by norm_num, ⟨10868952922265605625457, by norm_num⟩, by norm_num, ⟨16303429383398408438186, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 32606858766796816876373 191055813086700098885 9 from by
          refine ⟨by norm_num, ⟨16303429383398408438186, by norm_num⟩, by norm_num, ⟨95527906543350049442, by norm_num⟩⟩)
        (Word.nil 191055813086700098885)))
theorem full_word_189 : Word word_189 687141216863821758491 191055813086700098885 := by
  unfold word_189
  have hp := shared_prefix_all 1192
  have ht := suffix_proof_189
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_189 : word_189.length = 43 := by decide
theorem word_sum_189 : word_189.sum = 70 := by decide
theorem infinite_family_189 (d : Nat) :
    ∃ z : Nat, Word word_189 (687141216863821758491 + 2^71*d) z ∧
      z < 687141216863821758491 + 2^71*d := by
  have h := word_uniform_descent full_word_189
    (show 191055813086700098885 < 687141216863821758491 by norm_num)
    (show 3^word_189.length < 2^word_189.sum by norm_num [word_189, sharedPrefix, suffix_189]) d
  simpa [word_sum_189] using h

/-- Certificate 190; shared prefix plus independently witnessed suffix. -/
def suffix_190 : List Nat := [2, 1, 13]
def word_190 : List Nat := sharedPrefix ++ suffix_190
theorem suffix_proof_190 : Word suffix_190 875546435704427014605785 360714016174614401159 := by
  unfold suffix_190
  exact Word.cons
        (show ExactStep 875546435704427014605785 656659826778320260954339 2 from by
          refine ⟨by norm_num, ⟨437773217852213507302892, by norm_num⟩, by norm_num, ⟨328329913389160130477169, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 656659826778320260954339 984989740167480391431509 1 from by
          refine ⟨by norm_num, ⟨328329913389160130477169, by norm_num⟩, by norm_num, ⟨492494870083740195715754, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 984989740167480391431509 360714016174614401159 13 from by
          refine ⟨by norm_num, ⟨492494870083740195715754, by norm_num⟩, by norm_num, ⟨180357008087307200579, by norm_num⟩⟩)
        (Word.nil 360714016174614401159)))
theorem full_word_190 : Word word_190 20757198769059813916699 360714016174614401159 := by
  unfold word_190
  have hp := shared_prefix_all 36008
  have ht := suffix_proof_190
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_190 : word_190.length = 43 := by decide
theorem word_sum_190 : word_190.sum = 74 := by decide
theorem infinite_family_190 (d : Nat) :
    ∃ z : Nat, Word word_190 (20757198769059813916699 + 2^75*d) z ∧
      z < 20757198769059813916699 + 2^75*d := by
  have h := word_uniform_descent full_word_190
    (show 360714016174614401159 < 20757198769059813916699 by norm_num)
    (show 3^word_190.length < 2^word_190.sum by norm_num [word_190, sharedPrefix, suffix_190]) d
  simpa [word_sum_190] using h

/-- Certificate 191; shared prefix plus independently witnessed suffix. -/
def suffix_191 : List Nat := [2, 1, 12]
def word_191 : List Nat := sharedPrefix ++ suffix_191
theorem suffix_proof_191 : Word suffix_191 477164053942049571654617 393171064954691724691 := by
  unfold suffix_191
  exact Word.cons
        (show ExactStep 477164053942049571654617 357873040456537178740963 2 from by
          refine ⟨by norm_num, ⟨238582026971024785827308, by norm_num⟩, by norm_num, ⟨178936520228268589370481, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 357873040456537178740963 536809560684805768111445 1 from by
          refine ⟨by norm_num, ⟨178936520228268589370481, by norm_num⟩, by norm_num, ⟨268404780342402884055722, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 536809560684805768111445 393171064954691724691 12 from by
          refine ⟨by norm_num, ⟨268404780342402884055722, by norm_num⟩, by norm_num, ⟨196585532477345862345, by norm_num⟩⟩)
        (Word.nil 393171064954691724691)))
theorem full_word_191 : Word word_191 11312465803320523489307 393171064954691724691 := by
  unfold word_191
  have hp := shared_prefix_all 19624
  have ht := suffix_proof_191
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_191 : word_191.length = 43 := by decide
theorem word_sum_191 : word_191.sum = 73 := by decide
theorem infinite_family_191 (d : Nat) :
    ∃ z : Nat, Word word_191 (11312465803320523489307 + 2^74*d) z ∧
      z < 11312465803320523489307 + 2^74*d := by
  have h := word_uniform_descent full_word_191
    (show 393171064954691724691 < 11312465803320523489307 by norm_num)
    (show 3^word_191.length < 2^word_191.sum by norm_num [word_191, sharedPrefix, suffix_191]) d
  simpa [word_sum_191] using h

/-- Certificate 192; shared prefix plus independently witnessed suffix. -/
def suffix_192 : List Nat := [2, 1, 11]
def word_192 : List Nat := sharedPrefix ++ suffix_192
theorem suffix_proof_192 : Word suffix_192 277972863060860850179033 458085162514846371755 := by
  unfold suffix_192
  exact Word.cons
        (show ExactStep 277972863060860850179033 208479647295645637634275 2 from by
          refine ⟨by norm_num, ⟨138986431530430425089516, by norm_num⟩, by norm_num, ⟨104239823647822818817137, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 208479647295645637634275 312719470943468456451413 1 from by
          refine ⟨by norm_num, ⟨104239823647822818817137, by norm_num⟩, by norm_num, ⟨156359735471734228225706, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 312719470943468456451413 458085162514846371755 11 from by
          refine ⟨by norm_num, ⟨156359735471734228225706, by norm_num⟩, by norm_num, ⟨229042581257423185877, by norm_num⟩⟩)
        (Word.nil 458085162514846371755)))
theorem full_word_192 : Word word_192 6590099320450878275611 458085162514846371755 := by
  unfold word_192
  have hp := shared_prefix_all 11432
  have ht := suffix_proof_192
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_192 : word_192.length = 43 := by decide
theorem word_sum_192 : word_192.sum = 72 := by decide
theorem infinite_family_192 (d : Nat) :
    ∃ z : Nat, Word word_192 (6590099320450878275611 + 2^73*d) z ∧
      z < 6590099320450878275611 + 2^73*d := by
  have h := word_uniform_descent full_word_192
    (show 458085162514846371755 < 6590099320450878275611 by norm_num)
    (show 3^word_192.length < 2^word_192.sum by norm_num [word_192, sharedPrefix, suffix_192]) d
  simpa [word_sum_192] using h

/-- Certificate 193; shared prefix plus independently witnessed suffix. -/
def suffix_193 : List Nat := [2, 1, 10]
def word_193 : List Nat := sharedPrefix ++ suffix_193
theorem suffix_proof_193 : Word suffix_193 178377267620266489441241 587913357635155665883 := by
  unfold suffix_193
  exact Word.cons
        (show ExactStep 178377267620266489441241 133782950715199867080931 2 from by
          refine ⟨by norm_num, ⟨89188633810133244720620, by norm_num⟩, by norm_num, ⟨66891475357599933540465, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 133782950715199867080931 200674426072799800621397 1 from by
          refine ⟨by norm_num, ⟨66891475357599933540465, by norm_num⟩, by norm_num, ⟨100337213036399900310698, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 200674426072799800621397 587913357635155665883 10 from by
          refine ⟨by norm_num, ⟨100337213036399900310698, by norm_num⟩, by norm_num, ⟨293956678817577832941, by norm_num⟩⟩)
        (Word.nil 587913357635155665883)))
theorem full_word_193 : Word word_193 4228916079016055668763 587913357635155665883 := by
  unfold word_193
  have hp := shared_prefix_all 7336
  have ht := suffix_proof_193
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_193 : word_193.length = 43 := by decide
theorem word_sum_193 : word_193.sum = 71 := by decide
theorem infinite_family_193 (d : Nat) :
    ∃ z : Nat, Word word_193 (4228916079016055668763 + 2^72*d) z ∧
      z < 4228916079016055668763 + 2^72*d := by
  have h := word_uniform_descent full_word_193
    (show 587913357635155665883 < 4228916079016055668763 by norm_num)
    (show 3^word_193.length < 2^word_193.sum by norm_num [word_193, sharedPrefix, suffix_193]) d
  simpa [word_sum_193] using h

/-- Certificate 194; shared prefix plus independently witnessed suffix. -/
def suffix_194 : List Nat := [2, 1, 7, 2]
def word_194 : List Nat := sharedPrefix ++ suffix_194
theorem suffix_proof_194 : Word suffix_194 16534425029300653242329 326974713714197488435 := by
  unfold suffix_194
  exact Word.cons
        (show ExactStep 16534425029300653242329 12400818771975489931747 2 from by
          refine ⟨by norm_num, ⟨8267212514650326621164, by norm_num⟩, by norm_num, ⟨6200409385987744965873, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 12400818771975489931747 18601228157963234897621 1 from by
          refine ⟨by norm_num, ⟨6200409385987744965873, by norm_num⟩, by norm_num, ⟨9300614078981617448810, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 18601228157963234897621 435966284952263317913 7 from by
          refine ⟨by norm_num, ⟨9300614078981617448810, by norm_num⟩, by norm_num, ⟨217983142476131658956, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 435966284952263317913 326974713714197488435 2 from by
          refine ⟨by norm_num, ⟨217983142476131658956, by norm_num⟩, by norm_num, ⟨163487356857098744217, by norm_num⟩⟩)
        (Word.nil 326974713714197488435))))
theorem full_word_194 : Word word_194 391993311684468932635 326974713714197488435 := by
  unfold word_194
  have hp := shared_prefix_all 680
  have ht := suffix_proof_194
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_194 : word_194.length = 44 := by decide
theorem word_sum_194 : word_194.sum = 70 := by decide
theorem infinite_family_194 (d : Nat) :
    ∃ z : Nat, Word word_194 (391993311684468932635 + 2^71*d) z ∧
      z < 391993311684468932635 + 2^71*d := by
  have h := word_uniform_descent full_word_194
    (show 326974713714197488435 < 391993311684468932635 by norm_num)
    (show 3^word_194.length < 2^word_194.sum by norm_num [word_194, sharedPrefix, suffix_194]) d
  simpa [word_sum_194] using h

/-- Certificate 195; shared prefix plus independently witnessed suffix. -/
def suffix_195 : List Nat := [2, 1, 7, 4]
def word_195 : List Nat := sharedPrefix ++ suffix_195
theorem suffix_proof_195 : Word suffix_195 66332222749597833611225 327936403974452180329 := by
  unfold suffix_195
  exact Word.cons
        (show ExactStep 66332222749597833611225 49749167062198375208419 2 from by
          refine ⟨by norm_num, ⟨33166111374798916805612, by norm_num⟩, by norm_num, ⟨24874583531099187604209, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 49749167062198375208419 74623750593297562812629 1 from by
          refine ⟨by norm_num, ⟨24874583531099187604209, by norm_num⟩, by norm_num, ⟨37311875296648781406314, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 74623750593297562812629 1748994154530411628421 7 from by
          refine ⟨by norm_num, ⟨37311875296648781406314, by norm_num⟩, by norm_num, ⟨874497077265205814210, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1748994154530411628421 327936403974452180329 4 from by
          refine ⟨by norm_num, ⟨874497077265205814210, by norm_num⟩, by norm_num, ⟨163968201987226090164, by norm_num⟩⟩)
        (Word.nil 327936403974452180329))))
theorem full_word_195 : Word word_195 1572584932401880236059 327936403974452180329 := by
  unfold word_195
  have hp := shared_prefix_all 2728
  have ht := suffix_proof_195
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_195 : word_195.length = 44 := by decide
theorem word_sum_195 : word_195.sum = 72 := by decide
theorem infinite_family_195 (d : Nat) :
    ∃ z : Nat, Word word_195 (1572584932401880236059 + 2^73*d) z ∧
      z < 1572584932401880236059 + 2^73*d := by
  have h := word_uniform_descent full_word_195
    (show 327936403974452180329 < 1572584932401880236059 by norm_num)
    (show 3^word_195.length < 2^word_195.sum by norm_num [word_195, sharedPrefix, suffix_195]) d
  simpa [word_sum_195] using h

/-- Certificate 196; shared prefix plus independently witnessed suffix. -/
def suffix_196 : List Nat := [2, 1, 7, 5]
def word_196 : List Nat := sharedPrefix ++ suffix_196
theorem suffix_proof_196 : Word suffix_196 265523413630786555086809 656353653079031706605 := by
  unfold suffix_196
  exact Word.cons
        (show ExactStep 265523413630786555086809 199142560223089916315107 2 from by
          refine ⟨by norm_num, ⟨132761706815393277543404, by norm_num⟩, by norm_num, ⟨99571280111544958157553, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 199142560223089916315107 298713840334634874472661 1 from by
          refine ⟨by norm_num, ⟨99571280111544958157553, by norm_num⟩, by norm_num, ⟨149356920167317437236330, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 298713840334634874472661 7001105632843004870453 7 from by
          refine ⟨by norm_num, ⟨149356920167317437236330, by norm_num⟩, by norm_num, ⟨3500552816421502435226, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 7001105632843004870453 656353653079031706605 5 from by
          refine ⟨by norm_num, ⟨3500552816421502435226, by norm_num⟩, by norm_num, ⟨328176826539515853302, by norm_num⟩⟩)
        (Word.nil 656353653079031706605))))
theorem full_word_196 : Word word_196 6294951415271525449755 656353653079031706605 := by
  unfold word_196
  have hp := shared_prefix_all 10920
  have ht := suffix_proof_196
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_196 : word_196.length = 44 := by decide
theorem word_sum_196 : word_196.sum = 73 := by decide
theorem infinite_family_196 (d : Nat) :
    ∃ z : Nat, Word word_196 (6294951415271525449755 + 2^74*d) z ∧
      z < 6294951415271525449755 + 2^74*d := by
  have h := word_uniform_descent full_word_196
    (show 656353653079031706605 < 6294951415271525449755 by norm_num)
    (show 3^word_196.length < 2^word_196.sum by norm_num [word_196, sharedPrefix, suffix_196]) d
  simpa [word_sum_196] using h

/-- Certificate 197; shared prefix plus independently witnessed suffix. -/
def suffix_197 : List Nat := [2, 1, 7, 6]
def word_197 : List Nat := sharedPrefix ++ suffix_197
theorem suffix_proof_197 : Word suffix_197 663905795393163998037977 820562277631321469743 := by
  unfold suffix_197
  exact Word.cons
        (show ExactStep 663905795393163998037977 497929346544872998528483 2 from by
          refine ⟨by norm_num, ⟨331952897696581999018988, by norm_num⟩, by norm_num, ⟨248964673272436499264241, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 497929346544872998528483 746894019817309497792725 1 from by
          refine ⟨by norm_num, ⟨248964673272436499264241, by norm_num⟩, by norm_num, ⟨373447009908654748896362, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 746894019817309497792725 17505328589468191354517 7 from by
          refine ⟨by norm_num, ⟨373447009908654748896362, by norm_num⟩, by norm_num, ⟨8752664294734095677258, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 17505328589468191354517 820562277631321469743 6 from by
          refine ⟨by norm_num, ⟨8752664294734095677258, by norm_num⟩, by norm_num, ⟨410281138815660734871, by norm_num⟩⟩)
        (Word.nil 820562277631321469743))))
theorem full_word_197 : Word word_197 15739684381010815877147 820562277631321469743 := by
  unfold word_197
  have hp := shared_prefix_all 27304
  have ht := suffix_proof_197
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_197 : word_197.length = 44 := by decide
theorem word_sum_197 : word_197.sum = 74 := by decide
theorem infinite_family_197 (d : Nat) :
    ∃ z : Nat, Word word_197 (15739684381010815877147 + 2^75*d) z ∧
      z < 15739684381010815877147 + 2^75*d := by
  have h := word_uniform_descent full_word_197
    (show 820562277631321469743 < 15739684381010815877147 by norm_num)
    (show 3^word_197.length < 2^word_197.sum by norm_num [word_197, sharedPrefix, suffix_197]) d
  simpa [word_sum_197] using h

/-- Certificate 198; shared prefix plus independently witnessed suffix. -/
def suffix_198 : List Nat := [2, 1, 7, 3]
def word_198 : List Nat := sharedPrefix ++ suffix_198
theorem suffix_proof_198 : Word suffix_198 165927818190192194349017 1640643710132515593539 := by
  unfold suffix_198
  exact Word.cons
        (show ExactStep 165927818190192194349017 124445863642644145761763 2 from by
          refine ⟨by norm_num, ⟨82963909095096097174508, by norm_num⟩, by norm_num, ⟨62222931821322072880881, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 124445863642644145761763 186668795463966218642645 1 from by
          refine ⟨by norm_num, ⟨62222931821322072880881, by norm_num⟩, by norm_num, ⟨93334397731983109321322, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 186668795463966218642645 4375049893686708249437 7 from by
          refine ⟨by norm_num, ⟨93334397731983109321322, by norm_num⟩, by norm_num, ⟨2187524946843354124718, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 4375049893686708249437 1640643710132515593539 3 from by
          refine ⟨by norm_num, ⟨2187524946843354124718, by norm_num⟩, by norm_num, ⟨820321855066257796769, by norm_num⟩⟩)
        (Word.nil 1640643710132515593539))))
theorem full_word_198 : Word word_198 3933768173836702842907 1640643710132515593539 := by
  unfold word_198
  have hp := shared_prefix_all 6824
  have ht := suffix_proof_198
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_198 : word_198.length = 44 := by decide
theorem word_sum_198 : word_198.sum = 71 := by decide
theorem infinite_family_198 (d : Nat) :
    ∃ z : Nat, Word word_198 (3933768173836702842907 + 2^72*d) z ∧
      z < 3933768173836702842907 + 2^72*d := by
  have h := word_uniform_descent full_word_198
    (show 1640643710132515593539 < 3933768173836702842907 by norm_num)
    (show 3^word_198.length < 2^word_198.sum by norm_num [word_198, sharedPrefix, suffix_198]) d
  simpa [word_sum_198] using h

/-- Certificate 199; shared prefix plus independently witnessed suffix. -/
def suffix_199 : List Nat := [2, 1, 7, 1, 1, 4]
def word_199 : List Nat := sharedPrefix ++ suffix_199
theorem suffix_proof_199 : Word suffix_199 1136984873735987211542489 12647430007225565753395 := by
  unfold suffix_199
  exact Word.cons
        (show ExactStep 1136984873735987211542489 852738655301990408656867 2 from by
          refine ⟨by norm_num, ⟨568492436867993605771244, by norm_num⟩, by norm_num, ⟨426369327650995204328433, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 852738655301990408656867 1279107982952985612985301 1 from by
          refine ⟨by norm_num, ⟨426369327650995204328433, by norm_num⟩, by norm_num, ⟨639553991476492806492650, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1279107982952985612985301 29979093350460600304343 7 from by
          refine ⟨by norm_num, ⟨639553991476492806492650, by norm_num⟩, by norm_num, ⟨14989546675230300152171, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 29979093350460600304343 44968640025690900456515 1 from by
          refine ⟨by norm_num, ⟨14989546675230300152171, by norm_num⟩, by norm_num, ⟨22484320012845450228257, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 44968640025690900456515 67452960038536350684773 1 from by
          refine ⟨by norm_num, ⟨22484320012845450228257, by norm_num⟩, by norm_num, ⟨33726480019268175342386, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 67452960038536350684773 12647430007225565753395 4 from by
          refine ⟨by norm_num, ⟨33726480019268175342386, by norm_num⟩, by norm_num, ⟨6323715003612782876697, by norm_num⟩⟩)
        (Word.nil 12647430007225565753395))))))
theorem full_word_199 : Word word_199 26955304777826223259675 12647430007225565753395 := by
  unfold word_199
  have hp := shared_prefix_all 46760
  have ht := suffix_proof_199
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_199 : word_199.length = 46 := by decide
theorem word_sum_199 : word_199.sum = 74 := by decide
theorem infinite_family_199 (d : Nat) :
    ∃ z : Nat, Word word_199 (26955304777826223259675 + 2^75*d) z ∧
      z < 26955304777826223259675 + 2^75*d := by
  have h := word_uniform_descent full_word_199
    (show 12647430007225565753395 < 26955304777826223259675 by norm_num)
    (show 3^word_199.length < 2^word_199.sum by norm_num [word_199, sharedPrefix, suffix_199]) d
  simpa [word_sum_199] using h

/-- Certificate 200; shared prefix plus independently witnessed suffix. -/
def suffix_200 : List Nat := [2, 1, 7, 1, 1, 3]
def word_200 : List Nat := sharedPrefix ++ suffix_200
theorem suffix_proof_200 : Word suffix_200 738602491973609768591321 16431921894798630410861 := by
  unfold suffix_200
  exact Word.cons
        (show ExactStep 738602491973609768591321 553951868980207326443491 2 from by
          refine ⟨by norm_num, ⟨369301245986804884295660, by norm_num⟩, by norm_num, ⟨276975934490103663221745, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 553951868980207326443491 830927803470310989665237 1 from by
          refine ⟨by norm_num, ⟨276975934490103663221745, by norm_num⟩, by norm_num, ⟨415463901735155494832618, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 830927803470310989665237 19474870393835413820279 7 from by
          refine ⟨by norm_num, ⟨415463901735155494832618, by norm_num⟩, by norm_num, ⟨9737435196917706910139, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 19474870393835413820279 29212305590753120730419 1 from by
          refine ⟨by norm_num, ⟨9737435196917706910139, by norm_num⟩, by norm_num, ⟨14606152795376560365209, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 29212305590753120730419 43818458386129681095629 1 from by
          refine ⟨by norm_num, ⟨14606152795376560365209, by norm_num⟩, by norm_num, ⟨21909229193064840547814, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 43818458386129681095629 16431921894798630410861 3 from by
          refine ⟨by norm_num, ⟨21909229193064840547814, by norm_num⟩, by norm_num, ⟨8215960947399315205430, by norm_num⟩⟩)
        (Word.nil 16431921894798630410861))))))
theorem full_word_200 : Word word_200 17510571812086932832283 16431921894798630410861 := by
  unfold word_200
  have hp := shared_prefix_all 30376
  have ht := suffix_proof_200
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_200 : word_200.length = 46 := by decide
theorem word_sum_200 : word_200.sum = 73 := by decide
theorem infinite_family_200 (d : Nat) :
    ∃ z : Nat, Word word_200 (17510571812086932832283 + 2^74*d) z ∧
      z < 17510571812086932832283 + 2^74*d := by
  have h := word_uniform_descent full_word_200
    (show 16431921894798630410861 < 17510571812086932832283 by norm_num)
    (show 3^word_200.length < 2^word_200.sum by norm_num [word_200, sharedPrefix, suffix_200]) d
  simpa [word_sum_200] using h

/-- Certificate 201; shared prefix plus independently witnessed suffix. -/
def suffix_201 : List Nat := [2, 1, 7, 1, 2, 2]
def word_201 : List Nat := sharedPrefix ++ suffix_201
theorem suffix_proof_201 : Word suffix_201 290422312490935145271257 6461116510189566677941 := by
  unfold suffix_201
  exact Word.cons
        (show ExactStep 290422312490935145271257 217816734368201358953443 2 from by
          refine ⟨by norm_num, ⟨145211156245467572635628, by norm_num⟩, by norm_num, ⟨108908367184100679476721, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 217816734368201358953443 326725101552302038430165 1 from by
          refine ⟨by norm_num, ⟨108908367184100679476721, by norm_num⟩, by norm_num, ⟨163362550776151019215082, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 326725101552302038430165 7657619567632079025707 7 from by
          refine ⟨by norm_num, ⟨163362550776151019215082, by norm_num⟩, by norm_num, ⟨3828809783816039512853, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 7657619567632079025707 11486429351448118538561 1 from by
          refine ⟨by norm_num, ⟨3828809783816039512853, by norm_num⟩, by norm_num, ⟨5743214675724059269280, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 11486429351448118538561 8614822013586088903921 2 from by
          refine ⟨by norm_num, ⟨5743214675724059269280, by norm_num⟩, by norm_num, ⟨4307411006793044451960, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 8614822013586088903921 6461116510189566677941 2 from by
          refine ⟨by norm_num, ⟨4307411006793044451960, by norm_num⟩, by norm_num, ⟨3230558255094783338970, by norm_num⟩⟩)
        (Word.nil 6461116510189566677941))))))
theorem full_word_201 : Word word_201 6885247225630231101467 6461116510189566677941 := by
  unfold word_201
  have hp := shared_prefix_all 11944
  have ht := suffix_proof_201
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_201 : word_201.length = 46 := by decide
theorem word_sum_201 : word_201.sum = 73 := by decide
theorem infinite_family_201 (d : Nat) :
    ∃ z : Nat, Word word_201 (6885247225630231101467 + 2^74*d) z ∧
      z < 6885247225630231101467 + 2^74*d := by
  have h := word_uniform_descent full_word_201
    (show 6461116510189566677941 < 6885247225630231101467 by norm_num)
    (show 3^word_201.length < 2^word_201.sum by norm_num [word_201, sharedPrefix, suffix_201]) d
  simpa [word_sum_201] using h

/-- Certificate 202; shared prefix plus independently witnessed suffix. -/
def suffix_202 : List Nat := [2, 1, 7, 1, 2, 3]
def word_202 : List Nat := sharedPrefix ++ suffix_202
theorem suffix_proof_202 : Word suffix_202 688804694253312588222425 7662027314921033886935 := by
  unfold suffix_202
  exact Word.cons
        (show ExactStep 688804694253312588222425 516603520689984441166819 2 from by
          refine ⟨by norm_num, ⟨344402347126656294111212, by norm_num⟩, by norm_num, ⟨258301760344992220583409, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 516603520689984441166819 774905281034976661750229 1 from by
          refine ⟨by norm_num, ⟨258301760344992220583409, by norm_num⟩, by norm_num, ⟨387452640517488330875114, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 774905281034976661750229 18161842524257265509771 7 from by
          refine ⟨by norm_num, ⟨387452640517488330875114, by norm_num⟩, by norm_num, ⟨9080921262128632754885, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 18161842524257265509771 27242763786385898264657 1 from by
          refine ⟨by norm_num, ⟨9080921262128632754885, by norm_num⟩, by norm_num, ⟨13621381893192949132328, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 27242763786385898264657 20432072839789423698493 2 from by
          refine ⟨by norm_num, ⟨13621381893192949132328, by norm_num⟩, by norm_num, ⟨10216036419894711849246, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 20432072839789423698493 7662027314921033886935 3 from by
          refine ⟨by norm_num, ⟨10216036419894711849246, by norm_num⟩, by norm_num, ⟨3831013657460516943467, by norm_num⟩⟩)
        (Word.nil 7662027314921033886935))))))
theorem full_word_202 : Word word_202 16329980191369521528859 7662027314921033886935 := by
  unfold word_202
  have hp := shared_prefix_all 28328
  have ht := suffix_proof_202
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_202 : word_202.length = 46 := by decide
theorem word_sum_202 : word_202.sum = 74 := by decide
theorem infinite_family_202 (d : Nat) :
    ∃ z : Nat, Word word_202 (16329980191369521528859 + 2^75*d) z ∧
      z < 16329980191369521528859 + 2^75*d := by
  have h := word_uniform_descent full_word_202
    (show 7662027314921033886935 < 16329980191369521528859 by norm_num)
    (show 3^word_202.length < 2^word_202.sum by norm_num [word_202, sharedPrefix, suffix_202]) d
  simpa [word_sum_202] using h

/-- Certificate 203; shared prefix plus independently witnessed suffix. -/
def suffix_203 : List Nat := [2, 1, 7, 1, 3]
def word_203 : List Nat := sharedPrefix ++ suffix_203
theorem suffix_proof_203 : Word suffix_203 190826717050340784533465 2830254653517627602639 := by
  unfold suffix_203
  exact Word.cons
        (show ExactStep 190826717050340784533465 143120037787755588400099 2 from by
          refine ⟨by norm_num, ⟨95413358525170392266732, by norm_num⟩, by norm_num, ⟨71560018893877794200049, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 143120037787755588400099 214680056681633382600149 1 from by
          refine ⟨by norm_num, ⟨71560018893877794200049, by norm_num⟩, by norm_num, ⟨107340028340816691300074, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 214680056681633382600149 5031563828475782404691 7 from by
          refine ⟨by norm_num, ⟨107340028340816691300074, by norm_num⟩, by norm_num, ⟨2515781914237891202345, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 5031563828475782404691 7547345742713673607037 1 from by
          refine ⟨by norm_num, ⟨2515781914237891202345, by norm_num⟩, by norm_num, ⟨3773672871356836803518, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 7547345742713673607037 2830254653517627602639 3 from by
          refine ⟨by norm_num, ⟨3773672871356836803518, by norm_num⟩, by norm_num, ⟨1415127326758813801319, by norm_num⟩⟩)
        (Word.nil 2830254653517627602639)))))
theorem full_word_203 : Word word_203 4524063984195408494619 2830254653517627602639 := by
  unfold word_203
  have hp := shared_prefix_all 7848
  have ht := suffix_proof_203
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_203 : word_203.length = 45 := by decide
theorem word_sum_203 : word_203.sum = 72 := by decide
theorem infinite_family_203 (d : Nat) :
    ∃ z : Nat, Word word_203 (4524063984195408494619 + 2^73*d) z ∧
      z < 4524063984195408494619 + 2^73*d := by
  have h := word_uniform_descent full_word_203
    (show 2830254653517627602639 < 4524063984195408494619 by norm_num)
    (show 3^word_203.length < 2^word_203.sum by norm_num [word_203, sharedPrefix, suffix_203]) d
  simpa [word_sum_203] using h

/-- Certificate 204; shared prefix plus independently witnessed suffix. -/
def suffix_204 : List Nat := [2, 1, 7, 1, 4]
def word_204 : List Nat := sharedPrefix ++ suffix_204
theorem suffix_proof_204 : Word suffix_204 390017907931529506009049 2892283680034230650641 := by
  unfold suffix_204
  exact Word.cons
        (show ExactStep 390017907931529506009049 292513430948647129506787 2 from by
          refine ⟨by norm_num, ⟨195008953965764753004524, by norm_num⟩, by norm_num, ⟨146256715474323564753393, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 292513430948647129506787 438770146422970694260181 1 from by
          refine ⟨by norm_num, ⟨146256715474323564753393, by norm_num⟩, by norm_num, ⟨219385073211485347130090, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 438770146422970694260181 10283675306788375646723 7 from by
          refine ⟨by norm_num, ⟨219385073211485347130090, by norm_num⟩, by norm_num, ⟨5141837653394187823361, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 10283675306788375646723 15425512960182563470085 1 from by
          refine ⟨by norm_num, ⟨5141837653394187823361, by norm_num⟩, by norm_num, ⟨7712756480091281735042, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 15425512960182563470085 2892283680034230650641 4 from by
          refine ⟨by norm_num, ⟨7712756480091281735042, by norm_num⟩, by norm_num, ⟨1446141840017115325320, by norm_num⟩⟩)
        (Word.nil 2892283680034230650641)))))
theorem full_word_204 : Word word_204 9246430467065053708315 2892283680034230650641 := by
  unfold word_204
  have hp := shared_prefix_all 16040
  have ht := suffix_proof_204
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_204 : word_204.length = 45 := by decide
theorem word_sum_204 : word_204.sum = 73 := by decide
theorem infinite_family_204 (d : Nat) :
    ∃ z : Nat, Word word_204 (9246430467065053708315 + 2^74*d) z ∧
      z < 9246430467065053708315 + 2^74*d := by
  have h := word_uniform_descent full_word_204
    (show 2892283680034230650641 < 9246430467065053708315 by norm_num)
    (show 3^word_204.length < 2^word_204.sum by norm_num [word_204, sharedPrefix, suffix_204]) d
  simpa [word_sum_204] using h

/-- Certificate 205; shared prefix plus independently witnessed suffix. -/
def suffix_205 : List Nat := [2, 1, 7, 1, 5]
def word_205 : List Nat := sharedPrefix ++ suffix_205
theorem suffix_proof_205 : Word suffix_205 1585165053218661834862553 5877610899843365873285 := by
  unfold suffix_205
  exact Word.cons
        (show ExactStep 1585165053218661834862553 1188873789913996376146915 2 from by
          refine ⟨by norm_num, ⟨792582526609330917431276, by norm_num⟩, by norm_num, ⟨594436894956998188073457, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1188873789913996376146915 1783310684870994564220373 1 from by
          refine ⟨by norm_num, ⟨594436894956998188073457, by norm_num⟩, by norm_num, ⟨891655342435497282110186, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1783310684870994564220373 41796344176663935098915 7 from by
          refine ⟨by norm_num, ⟨891655342435497282110186, by norm_num⟩, by norm_num, ⟨20898172088331967549457, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 41796344176663935098915 62694516264995902648373 1 from by
          refine ⟨by norm_num, ⟨20898172088331967549457, by norm_num⟩, by norm_num, ⟨31347258132497951324186, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 62694516264995902648373 5877610899843365873285 5 from by
          refine ⟨by norm_num, ⟨31347258132497951324186, by norm_num⟩, by norm_num, ⟨2938805449921682936642, by norm_num⟩⟩)
        (Word.nil 5877610899843365873285)))))
theorem full_word_205 : Word word_205 37580629364282924990491 5877610899843365873285 := by
  unfold word_205
  have hp := shared_prefix_all 65192
  have ht := suffix_proof_205
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_205 : word_205.length = 45 := by decide
theorem word_sum_205 : word_205.sum = 74 := by decide
theorem infinite_family_205 (d : Nat) :
    ∃ z : Nat, Word word_205 (37580629364282924990491 + 2^75*d) z ∧
      z < 37580629364282924990491 + 2^75*d := by
  have h := word_uniform_descent full_word_205
    (show 5877610899843365873285 < 37580629364282924990491 by norm_num)
    (show 3^word_205.length < 2^word_205.sum by norm_num [word_205, sharedPrefix, suffix_205]) d
  simpa [word_sum_205] using h

/-- Certificate 206; shared prefix plus independently witnessed suffix. -/
def suffix_206 : List Nat := [2, 1, 6, 1, 1, 5]
def word_206 : List Nat := sharedPrefix ++ suffix_206
theorem suffix_proof_206 : Word suffix_206 209500891195452227171801 2330416102317576196415 := by
  unfold suffix_206
  exact Word.cons
        (show ExactStep 209500891195452227171801 157125668396589170378851 2 from by
          refine ⟨by norm_num, ⟨104750445597726113585900, by norm_num⟩, by norm_num, ⟨78562834198294585189425, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 157125668396589170378851 235688502594883755568277 1 from by
          refine ⟨by norm_num, ⟨78562834198294585189425, by norm_num⟩, by norm_num, ⟨117844251297441877784138, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 235688502594883755568277 11047898559135176042263 6 from by
          refine ⟨by norm_num, ⟨117844251297441877784138, by norm_num⟩, by norm_num, ⟨5523949279567588021131, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 11047898559135176042263 16571847838702764063395 1 from by
          refine ⟨by norm_num, ⟨5523949279567588021131, by norm_num⟩, by norm_num, ⟨8285923919351382031697, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 16571847838702764063395 24857771758054146095093 1 from by
          refine ⟨by norm_num, ⟨8285923919351382031697, by norm_num⟩, by norm_num, ⟨12428885879027073047546, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 24857771758054146095093 2330416102317576196415 5 from by
          refine ⟨by norm_num, ⟨12428885879027073047546, by norm_num⟩, by norm_num, ⟨1165208051158788098207, by norm_num⟩⟩)
        (Word.nil 2330416102317576196415))))))
theorem full_word_206 : Word word_206 4966785841964437733403 2330416102317576196415 := by
  unfold word_206
  have hp := shared_prefix_all 8616
  have ht := suffix_proof_206
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_206 : word_206.length = 46 := by decide
theorem word_sum_206 : word_206.sum = 74 := by decide
theorem infinite_family_206 (d : Nat) :
    ∃ z : Nat, Word word_206 (4966785841964437733403 + 2^75*d) z ∧
      z < 4966785841964437733403 + 2^75*d := by
  have h := word_uniform_descent full_word_206
    (show 2330416102317576196415 < 4966785841964437733403 by norm_num)
    (show 3^word_206.length < 2^word_206.sum by norm_num [word_206, sharedPrefix, suffix_206]) d
  simpa [word_sum_206] using h

/-- Certificate 207; shared prefix plus independently witnessed suffix. -/
def suffix_207 : List Nat := [2, 1, 6, 1, 1, 4]
def word_207 : List Nat := sharedPrefix ++ suffix_207
theorem suffix_proof_207 : Word suffix_207 607883272957829670122969 13523770324287653488759 := by
  unfold suffix_207
  exact Word.cons
        (show ExactStep 607883272957829670122969 455912454718372252592227 2 from by
          refine ⟨by norm_num, ⟨303941636478914835061484, by norm_num⟩, by norm_num, ⟨227956227359186126296113, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 455912454718372252592227 683868682077558378888341 1 from by
          refine ⟨by norm_num, ⟨227956227359186126296113, by norm_num⟩, by norm_num, ⟨341934341038779189444170, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 683868682077558378888341 32056344472385549010391 6 from by
          refine ⟨by norm_num, ⟨341934341038779189444170, by norm_num⟩, by norm_num, ⟨16028172236192774505195, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 32056344472385549010391 48084516708578323515587 1 from by
          refine ⟨by norm_num, ⟨16028172236192774505195, by norm_num⟩, by norm_num, ⟨24042258354289161757793, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 48084516708578323515587 72126775062867485273381 1 from by
          refine ⟨by norm_num, ⟨24042258354289161757793, by norm_num⟩, by norm_num, ⟨36063387531433742636690, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 72126775062867485273381 13523770324287653488759 4 from by
          refine ⟨by norm_num, ⟨36063387531433742636690, by norm_num⟩, by norm_num, ⟨6761885162143826744379, by norm_num⟩⟩)
        (Word.nil 13523770324287653488759))))))
theorem full_word_207 : Word word_207 14411518807703728160795 13523770324287653488759 := by
  unfold word_207
  have hp := shared_prefix_all 25000
  have ht := suffix_proof_207
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_207 : word_207.length = 46 := by decide
theorem word_sum_207 : word_207.sum = 73 := by decide
theorem infinite_family_207 (d : Nat) :
    ∃ z : Nat, Word word_207 (14411518807703728160795 + 2^74*d) z ∧
      z < 14411518807703728160795 + 2^74*d := by
  have h := word_uniform_descent full_word_207
    (show 13523770324287653488759 < 14411518807703728160795 by norm_num)
    (show 3^word_207.length < 2^word_207.sum by norm_num [word_207, sharedPrefix, suffix_207]) d
  simpa [word_sum_207] using h

/-- Certificate 208; shared prefix plus independently witnessed suffix. -/
def suffix_208 : List Nat := [2, 1, 6, 1, 5]
def word_208 : List Nat := sharedPrefix ++ suffix_208
theorem suffix_proof_208 : Word suffix_208 35208599174412095880665 261098925762394387787 := by
  unfold suffix_208
  exact Word.cons
        (show ExactStep 35208599174412095880665 26406449380809071910499 2 from by
          refine ⟨by norm_num, ⟨17604299587206047940332, by norm_num⟩, by norm_num, ⟨13203224690404535955249, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 26406449380809071910499 39609674071213607865749 1 from by
          refine ⟨by norm_num, ⟨13203224690404535955249, by norm_num⟩, by norm_num, ⟨19804837035606803932874, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 39609674071213607865749 1856703472088137868707 6 from by
          refine ⟨by norm_num, ⟨19804837035606803932874, by norm_num⟩, by norm_num, ⟨928351736044068934353, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1856703472088137868707 2785055208132206803061 1 from by
          refine ⟨by norm_num, ⟨928351736044068934353, by norm_num⟩, by norm_num, ⟨1392527604066103401530, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2785055208132206803061 261098925762394387787 5 from by
          refine ⟨by norm_num, ⟨1392527604066103401530, by norm_num⟩, by norm_num, ⟨130549462881197193893, by norm_num⟩⟩)
        (Word.nil 261098925762394387787)))))
theorem full_word_208 : Word word_208 834715169453498171419 261098925762394387787 := by
  unfold word_208
  have hp := shared_prefix_all 1448
  have ht := suffix_proof_208
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_208 : word_208.length = 45 := by decide
theorem word_sum_208 : word_208.sum = 73 := by decide
theorem infinite_family_208 (d : Nat) :
    ∃ z : Nat, Word word_208 (834715169453498171419 + 2^74*d) z ∧
      z < 834715169453498171419 + 2^74*d := by
  have h := word_uniform_descent full_word_208
    (show 261098925762394387787 < 834715169453498171419 by norm_num)
    (show 3^word_208.length < 2^word_208.sum by norm_num [word_208, sharedPrefix, suffix_208]) d
  simpa [word_sum_208] using h

/-- Certificate 209; shared prefix plus independently witnessed suffix. -/
def suffix_209 : List Nat := [2, 1, 6, 1, 6]
def word_209 : List Nat := sharedPrefix ++ suffix_209
theorem suffix_proof_209 : Word suffix_209 433590980936789538831833 1607705816156614043215 := by
  unfold suffix_209
  exact Word.cons
        (show ExactStep 433590980936789538831833 325193235702592154123875 2 from by
          refine ⟨by norm_num, ⟨216795490468394769415916, by norm_num⟩, by norm_num, ⟨162596617851296077061937, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 325193235702592154123875 487789853553888231185813 1 from by
          refine ⟨by norm_num, ⟨162596617851296077061937, by norm_num⟩, by norm_num, ⟨243894926776944115592906, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 487789853553888231185813 22865149385338510836835 6 from by
          refine ⟨by norm_num, ⟨243894926776944115592906, by norm_num⟩, by norm_num, ⟨11432574692669255418417, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 22865149385338510836835 34297724078007766255253 1 from by
          refine ⟨by norm_num, ⟨11432574692669255418417, by norm_num⟩, by norm_num, ⟨17148862039003883127626, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 34297724078007766255253 1607705816156614043215 6 from by
          refine ⟨by norm_num, ⟨17148862039003883127626, by norm_num⟩, by norm_num, ⟨803852908078307021607, by norm_num⟩⟩)
        (Word.nil 1607705816156614043215)))))
theorem full_word_209 : Word word_209 10279448135192788598811 1607705816156614043215 := by
  unfold word_209
  have hp := shared_prefix_all 17832
  have ht := suffix_proof_209
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_209 : word_209.length = 45 := by decide
theorem word_sum_209 : word_209.sum = 74 := by decide
theorem infinite_family_209 (d : Nat) :
    ∃ z : Nat, Word word_209 (10279448135192788598811 + 2^75*d) z ∧
      z < 10279448135192788598811 + 2^75*d := by
  have h := word_uniform_descent full_word_209
    (show 1607705816156614043215 < 10279448135192788598811 by norm_num)
    (show 3^word_209.length < 2^word_209.sum by norm_num [word_209, sharedPrefix, suffix_209]) d
  simpa [word_sum_209] using h

/-- Certificate 210; shared prefix plus independently witnessed suffix. -/
def suffix_210 : List Nat := [2, 1, 6, 1, 4]
def word_210 : List Nat := sharedPrefix ++ suffix_210
theorem suffix_proof_210 : Word suffix_210 234399790055600817356249 3476510558075622474217 := by
  unfold suffix_210
  exact Word.cons
        (show ExactStep 234399790055600817356249 175799842541700613017187 2 from by
          refine ⟨by norm_num, ⟨117199895027800408678124, by norm_num⟩, by norm_num, ⟨87899921270850306508593, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 175799842541700613017187 263699763812550919525781 1 from by
          refine ⟨by norm_num, ⟨87899921270850306508593, by norm_num⟩, by norm_num, ⟨131849881906275459762890, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 263699763812550919525781 12360926428713324352771 6 from by
          refine ⟨by norm_num, ⟨131849881906275459762890, by norm_num⟩, by norm_num, ⟨6180463214356662176385, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 12360926428713324352771 18541389643069986529157 1 from by
          refine ⟨by norm_num, ⟨6180463214356662176385, by norm_num⟩, by norm_num, ⟨9270694821534993264578, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 18541389643069986529157 3476510558075622474217 4 from by
          refine ⟨by norm_num, ⟨9270694821534993264578, by norm_num⟩, by norm_num, ⟨1738255279037811237108, by norm_num⟩⟩)
        (Word.nil 3476510558075622474217)))))
theorem full_word_210 : Word word_210 5557081652323143385115 3476510558075622474217 := by
  unfold word_210
  have hp := shared_prefix_all 9640
  have ht := suffix_proof_210
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_210 : word_210.length = 45 := by decide
theorem word_sum_210 : word_210.sum = 72 := by decide
theorem infinite_family_210 (d : Nat) :
    ∃ z : Nat, Word word_210 (5557081652323143385115 + 2^73*d) z ∧
      z < 5557081652323143385115 + 2^73*d := by
  have h := word_uniform_descent full_word_210
    (show 3476510558075622474217 < 5557081652323143385115 by norm_num)
    (show 3^word_210.length < 2^word_210.sum by norm_num [word_210, sharedPrefix, suffix_210]) d
  simpa [word_sum_210] using h

/-- Certificate 211; shared prefix plus independently witnessed suffix. -/
def suffix_211 : List Nat := [2, 1, 6, 1, 3, 3]
def word_211 : List Nat := sharedPrefix ++ suffix_211
theorem suffix_proof_211 : Word suffix_211 1130760149020950063996377 12578188303165780588583 := by
  unfold suffix_211
  exact Word.cons
        (show ExactStep 1130760149020950063996377 848070111765712547997283 2 from by
          refine ⟨by norm_num, ⟨565380074510475031998188, by norm_num⟩, by norm_num, ⟨424035055882856273998641, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 848070111765712547997283 1272105167648568821995925 1 from by
          refine ⟨by norm_num, ⟨424035055882856273998641, by norm_num⟩, by norm_num, ⟨636052583824284410997962, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1272105167648568821995925 59629929733526663531059 6 from by
          refine ⟨by norm_num, ⟨636052583824284410997962, by norm_num⟩, by norm_num, ⟨29814964866763331765529, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 59629929733526663531059 89444894600289995296589 1 from by
          refine ⟨by norm_num, ⟨29814964866763331765529, by norm_num⟩, by norm_num, ⟨44722447300144997648294, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 89444894600289995296589 33541835475108748236221 3 from by
          refine ⟨by norm_num, ⟨44722447300144997648294, by norm_num⟩, by norm_num, ⟨16770917737554374118110, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 33541835475108748236221 12578188303165780588583 3 from by
          refine ⟨by norm_num, ⟨16770917737554374118110, by norm_num⟩, by norm_num, ⟨6289094151582890294291, by norm_num⟩⟩)
        (Word.nil 12578188303165780588583))))))
theorem full_word_211 : Word word_211 26807730825236546846747 12578188303165780588583 := by
  unfold word_211
  have hp := shared_prefix_all 46504
  have ht := suffix_proof_211
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_211 : word_211.length = 46 := by decide
theorem word_sum_211 : word_211.sum = 74 := by decide
theorem infinite_family_211 (d : Nat) :
    ∃ z : Nat, Word word_211 (26807730825236546846747 + 2^75*d) z ∧
      z < 26807730825236546846747 + 2^75*d := by
  have h := word_uniform_descent full_word_211
    (show 12578188303165780588583 < 26807730825236546846747 by norm_num)
    (show 3^word_211.length < 2^word_211.sum by norm_num [word_211, sharedPrefix, suffix_211]) d
  simpa [word_sum_211] using h

/-- Certificate 212; shared prefix plus independently witnessed suffix. -/
def suffix_212 : List Nat := [2, 1, 6, 1, 3, 2]
def word_212 : List Nat := sharedPrefix ++ suffix_212
theorem suffix_proof_212 : Word suffix_212 732377767258572621045209 16293438486679060081237 := by
  unfold suffix_212
  exact Word.cons
        (show ExactStep 732377767258572621045209 549283325443929465783907 2 from by
          refine ⟨by norm_num, ⟨366188883629286310522604, by norm_num⟩, by norm_num, ⟨274641662721964732891953, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 549283325443929465783907 823924988165894198675861 1 from by
          refine ⟨by norm_num, ⟨274641662721964732891953, by norm_num⟩, by norm_num, ⟨411962494082947099337930, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 823924988165894198675861 38621483820276290562931 6 from by
          refine ⟨by norm_num, ⟨411962494082947099337930, by norm_num⟩, by norm_num, ⟨19310741910138145281465, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 38621483820276290562931 57932225730414435844397 1 from by
          refine ⟨by norm_num, ⟨19310741910138145281465, by norm_num⟩, by norm_num, ⟨28966112865207217922198, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 57932225730414435844397 21724584648905413441649 3 from by
          refine ⟨by norm_num, ⟨28966112865207217922198, by norm_num⟩, by norm_num, ⟨10862292324452706720824, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 21724584648905413441649 16293438486679060081237 2 from by
          refine ⟨by norm_num, ⟨10862292324452706720824, by norm_num⟩, by norm_num, ⟨8146719243339530040618, by norm_num⟩⟩)
        (Word.nil 16293438486679060081237))))))
theorem full_word_212 : Word word_212 17362997859497256419355 16293438486679060081237 := by
  unfold word_212
  have hp := shared_prefix_all 30120
  have ht := suffix_proof_212
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_212 : word_212.length = 46 := by decide
theorem word_sum_212 : word_212.sum = 73 := by decide
theorem infinite_family_212 (d : Nat) :
    ∃ z : Nat, Word word_212 (17362997859497256419355 + 2^74*d) z ∧
      z < 17362997859497256419355 + 2^74*d := by
  have h := word_uniform_descent full_word_212
    (show 16293438486679060081237 < 17362997859497256419355 by norm_num)
    (show 3^word_212.length < 2^word_212.sum by norm_num [word_212, sharedPrefix, suffix_212]) d
  simpa [word_sum_212] using h

/-- Certificate 213; shared prefix plus independently witnessed suffix. -/
def suffix_213 : List Nat := [2, 1, 6, 1, 2, 3]
def word_213 : List Nat := sharedPrefix ++ suffix_213
theorem suffix_proof_213 : Word suffix_213 383793183216492358462937 8538367631983121622299 := by
  unfold suffix_213
  exact Word.cons
        (show ExactStep 383793183216492358462937 287844887412369268847203 2 from by
          refine ⟨by norm_num, ⟨191896591608246179231468, by norm_num⟩, by norm_num, ⟨143922443706184634423601, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 287844887412369268847203 431767331118553903270805 1 from by
          refine ⟨by norm_num, ⟨143922443706184634423601, by norm_num⟩, by norm_num, ⟨215883665559276951635402, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 431767331118553903270805 20239093646182214215819 6 from by
          refine ⟨by norm_num, ⟨215883665559276951635402, by norm_num⟩, by norm_num, ⟨10119546823091107107909, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 20239093646182214215819 30358640469273321323729 1 from by
          refine ⟨by norm_num, ⟨10119546823091107107909, by norm_num⟩, by norm_num, ⟨15179320234636660661864, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 30358640469273321323729 22768980351954990992797 2 from by
          refine ⟨by norm_num, ⟨15179320234636660661864, by norm_num⟩, by norm_num, ⟨11384490175977495496398, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 22768980351954990992797 8538367631983121622299 3 from by
          refine ⟨by norm_num, ⟨11384490175977495496398, by norm_num⟩, by norm_num, ⟨4269183815991560811149, by norm_num⟩⟩)
        (Word.nil 8538367631983121622299))))))
theorem full_word_213 : Word word_213 9098856514475377295387 8538367631983121622299 := by
  unfold word_213
  have hp := shared_prefix_all 15784
  have ht := suffix_proof_213
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_213 : word_213.length = 46 := by decide
theorem word_sum_213 : word_213.sum = 73 := by decide
theorem infinite_family_213 (d : Nat) :
    ∃ z : Nat, Word word_213 (9098856514475377295387 + 2^74*d) z ∧
      z < 9098856514475377295387 + 2^74*d := by
  have h := word_uniform_descent full_word_213
    (show 8538367631983121622299 < 9098856514475377295387 by norm_num)
    (show 3^word_213.length < 2^word_213.sum by norm_num [word_213, sharedPrefix, suffix_213]) d
  simpa [word_sum_213] using h

/-- Certificate 214; shared prefix plus independently witnessed suffix. -/
def suffix_214 : List Nat := [2, 1, 6, 1, 2, 4]
def word_214 : List Nat := sharedPrefix ++ suffix_214
theorem suffix_proof_214 : Word suffix_214 1578940328503624687316441 17563590995470312455043 := by
  unfold suffix_214
  exact Word.cons
        (show ExactStep 1578940328503624687316441 1184205246377718515487331 2 from by
          refine ⟨by norm_num, ⟨789470164251812343658220, by norm_num⟩, by norm_num, ⟨592102623188859257743665, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1184205246377718515487331 1776307869566577773230997 1 from by
          refine ⟨by norm_num, ⟨592102623188859257743665, by norm_num⟩, by norm_num, ⟨888153934783288886615498, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1776307869566577773230997 83264431385933333120203 6 from by
          refine ⟨by norm_num, ⟨888153934783288886615498, by norm_num⟩, by norm_num, ⟨41632215692966666560101, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 83264431385933333120203 124896647078899999680305 1 from by
          refine ⟨by norm_num, ⟨41632215692966666560101, by norm_num⟩, by norm_num, ⟨62448323539449999840152, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 124896647078899999680305 93672485309174999760229 2 from by
          refine ⟨by norm_num, ⟨62448323539449999840152, by norm_num⟩, by norm_num, ⟨46836242654587499880114, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 93672485309174999760229 17563590995470312455043 4 from by
          refine ⟨by norm_num, ⟨46836242654587499880114, by norm_num⟩, by norm_num, ⟨8781795497735156227521, by norm_num⟩⟩)
        (Word.nil 17563590995470312455043))))))
theorem full_word_214 : Word word_214 37433055411693248577563 17563590995470312455043 := by
  unfold word_214
  have hp := shared_prefix_all 64936
  have ht := suffix_proof_214
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_214 : word_214.length = 46 := by decide
theorem word_sum_214 : word_214.sum = 74 := by decide
theorem infinite_family_214 (d : Nat) :
    ∃ z : Nat, Word word_214 (37433055411693248577563 + 2^75*d) z ∧
      z < 37433055411693248577563 + 2^75*d := by
  have h := word_uniform_descent full_word_214
    (show 17563590995470312455043 < 37433055411693248577563 by norm_num)
    (show 3^word_214.length < 2^word_214.sum by norm_num [word_214, sharedPrefix, suffix_214]) d
  simpa [word_sum_214] using h

/-- Certificate 215; shared prefix plus independently witnessed suffix. -/
def suffix_215 : List Nat := [2, 1, 6, 3]
def word_215 : List Nat := sharedPrefix ++ suffix_215
theorem suffix_proof_215 : Word suffix_215 22759149744337800788441 450071076487148892545 := by
  unfold suffix_215
  exact Word.cons
        (show ExactStep 22759149744337800788441 17069362308253350591331 2 from by
          refine ⟨by norm_num, ⟨11379574872168900394220, by norm_num⟩, by norm_num, ⟨8534681154126675295665, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 17069362308253350591331 25604043462380025886997 1 from by
          refine ⟨by norm_num, ⟨8534681154126675295665, by norm_num⟩, by norm_num, ⟨12802021731190012943498, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 25604043462380025886997 1200189537299063713453 6 from by
          refine ⟨by norm_num, ⟨12802021731190012943498, by norm_num⟩, by norm_num, ⟨600094768649531856726, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1200189537299063713453 450071076487148892545 3 from by
          refine ⟨by norm_num, ⟨600094768649531856726, by norm_num⟩, by norm_num, ⟨225035538243574446272, by norm_num⟩⟩)
        (Word.nil 450071076487148892545))))
theorem full_word_215 : Word word_215 539567264274145345563 450071076487148892545 := by
  unfold word_215
  have hp := shared_prefix_all 936
  have ht := suffix_proof_215
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_215 : word_215.length = 44 := by decide
theorem word_sum_215 : word_215.sum = 70 := by decide
theorem infinite_family_215 (d : Nat) :
    ∃ z : Nat, Word word_215 (539567264274145345563 + 2^71*d) z ∧
      z < 539567264274145345563 + 2^71*d := by
  have h := word_uniform_descent full_word_215
    (show 450071076487148892545 < 539567264274145345563 by norm_num)
    (show 3^word_215.length < 2^word_215.sum by norm_num [word_215, sharedPrefix, suffix_215]) d
  simpa [word_sum_215] using h

/-- Certificate 216; shared prefix plus independently witnessed suffix. -/
def suffix_216 : List Nat := [2, 1, 6, 4]
def word_216 : List Nat := sharedPrefix ++ suffix_216
theorem suffix_proof_216 : Word suffix_216 72556947464634981157337 717420989335380062713 := by
  unfold suffix_216
  exact Word.cons
        (show ExactStep 72556947464634981157337 54417710598476235868003 2 from by
          refine ⟨by norm_num, ⟨36278473732317490578668, by norm_num⟩, by norm_num, ⟨27208855299238117934001, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 54417710598476235868003 81626565897714353802005 1 from by
          refine ⟨by norm_num, ⟨27208855299238117934001, by norm_num⟩, by norm_num, ⟨40813282948857176901002, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 81626565897714353802005 3826245276455360334469 6 from by
          refine ⟨by norm_num, ⟨40813282948857176901002, by norm_num⟩, by norm_num, ⟨1913122638227680167234, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 3826245276455360334469 717420989335380062713 4 from by
          refine ⟨by norm_num, ⟨1913122638227680167234, by norm_num⟩, by norm_num, ⟨358710494667690031356, by norm_num⟩⟩)
        (Word.nil 717420989335380062713))))
theorem full_word_216 : Word word_216 1720158884991556648987 717420989335380062713 := by
  unfold word_216
  have hp := shared_prefix_all 2984
  have ht := suffix_proof_216
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_216 : word_216.length = 44 := by decide
theorem word_sum_216 : word_216.sum = 71 := by decide
theorem infinite_family_216 (d : Nat) :
    ∃ z : Nat, Word word_216 (1720158884991556648987 + 2^72*d) z ∧
      z < 1720158884991556648987 + 2^72*d := by
  have h := word_uniform_descent full_word_216
    (show 717420989335380062713 < 1720158884991556648987 by norm_num)
    (show 3^word_216.length < 2^word_216.sum by norm_num [word_216, sharedPrefix, suffix_216]) d
  simpa [word_sum_216] using h

/-- Certificate 217; shared prefix plus independently witnessed suffix. -/
def suffix_217 : List Nat := [2, 1, 6, 5]
def word_217 : List Nat := sharedPrefix ++ suffix_217
theorem suffix_proof_217 : Word suffix_217 172152542905229341895129 851095945759495647797 := by
  unfold suffix_217
  exact Word.cons
        (show ExactStep 172152542905229341895129 129114407178922006421347 2 from by
          refine ⟨by norm_num, ⟨86076271452614670947564, by norm_num⟩, by norm_num, ⟨64557203589461003210673, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 129114407178922006421347 193671610768383009632021 1 from by
          refine ⟨by norm_num, ⟨64557203589461003210673, by norm_num⟩, by norm_num, ⟨96835805384191504816010, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 193671610768383009632021 9078356754767953576501 6 from by
          refine ⟨by norm_num, ⟨96835805384191504816010, by norm_num⟩, by norm_num, ⟨4539178377383976788250, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 9078356754767953576501 851095945759495647797 5 from by
          refine ⟨by norm_num, ⟨4539178377383976788250, by norm_num⟩, by norm_num, ⟨425547972879747823898, by norm_num⟩⟩)
        (Word.nil 851095945759495647797))))
theorem full_word_217 : Word word_217 4081342126426379255835 851095945759495647797 := by
  unfold word_217
  have hp := shared_prefix_all 7080
  have ht := suffix_proof_217
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_217 : word_217.length = 44 := by decide
theorem word_sum_217 : word_217.sum = 72 := by decide
theorem infinite_family_217 (d : Nat) :
    ∃ z : Nat, Word word_217 (4081342126426379255835 + 2^73*d) z ∧
      z < 4081342126426379255835 + 2^73*d := by
  have h := word_uniform_descent full_word_217
    (show 851095945759495647797 < 4081342126426379255835 by norm_num)
    (show 3^word_217.length < 2^word_217.sum by norm_num [word_217, sharedPrefix, suffix_217]) d
  simpa [word_sum_217] using h

/-- Certificate 218; shared prefix plus independently witnessed suffix. -/
def suffix_218 : List Nat := [2, 1, 6, 6]
def word_218 : List Nat := sharedPrefix ++ suffix_218
theorem suffix_proof_218 : Word suffix_218 371343733786418063370713 917933423971553440339 := by
  unfold suffix_218
  exact Word.cons
        (show ExactStep 371343733786418063370713 278507800339813547528035 2 from by
          refine ⟨by norm_num, ⟨185671866893209031685356, by norm_num⟩, by norm_num, ⟨139253900169906773764017, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 278507800339813547528035 417761700509720321292053 1 from by
          refine ⟨by norm_num, ⟨139253900169906773764017, by norm_num⟩, by norm_num, ⟨208880850254860160646026, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 417761700509720321292053 19582579711393140060565 6 from by
          refine ⟨by norm_num, ⟨208880850254860160646026, by norm_num⟩, by norm_num, ⟨9791289855696570030282, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 19582579711393140060565 917933423971553440339 6 from by
          refine ⟨by norm_num, ⟨9791289855696570030282, by norm_num⟩, by norm_num, ⟨458966711985776720169, by norm_num⟩⟩)
        (Word.nil 917933423971553440339))))
theorem full_word_218 : Word word_218 8803708609296024469531 917933423971553440339 := by
  unfold word_218
  have hp := shared_prefix_all 15272
  have ht := suffix_proof_218
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_218 : word_218.length = 44 := by decide
theorem word_sum_218 : word_218.sum = 73 := by decide
theorem infinite_family_218 (d : Nat) :
    ∃ z : Nat, Word word_218 (8803708609296024469531 + 2^74*d) z ∧
      z < 8803708609296024469531 + 2^74*d := by
  have h := word_uniform_descent full_word_218
    (show 917933423971553440339 < 8803708609296024469531 by norm_num)
    (show 3^word_218.length < 2^word_218.sum by norm_num [word_218, sharedPrefix, suffix_218]) d
  simpa [word_sum_218] using h

/-- Certificate 219; shared prefix plus independently witnessed suffix. -/
def suffix_219 : List Nat := [2, 1, 6, 7]
def word_219 : List Nat := sharedPrefix ++ suffix_219
theorem suffix_proof_219 : Word suffix_219 1566490879073550392224217 1936123065261193569491 := by
  unfold suffix_219
  exact Word.cons
        (show ExactStep 1566490879073550392224217 1174868159305162794168163 2 from by
          refine ⟨by norm_num, ⟨783245439536775196112108, by norm_num⟩, by norm_num, ⟨587434079652581397084081, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1174868159305162794168163 1762302238957744191252245 1 from by
          refine ⟨by norm_num, ⟨587434079652581397084081, by norm_num⟩, by norm_num, ⟨881151119478872095626122, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1762302238957744191252245 82607917451144258964949 6 from by
          refine ⟨by norm_num, ⟨881151119478872095626122, by norm_num⟩, by norm_num, ⟨41303958725572129482474, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 82607917451144258964949 1936123065261193569491 7 from by
          refine ⟨by norm_num, ⟨41303958725572129482474, by norm_num⟩, by norm_num, ⟨968061532630596784745, by norm_num⟩⟩)
        (Word.nil 1936123065261193569491))))
theorem full_word_219 : Word word_219 37137907506513895751707 1936123065261193569491 := by
  unfold word_219
  have hp := shared_prefix_all 64424
  have ht := suffix_proof_219
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_219 : word_219.length = 44 := by decide
theorem word_sum_219 : word_219.sum = 74 := by decide
theorem infinite_family_219 (d : Nat) :
    ∃ z : Nat, Word word_219 (37137907506513895751707 + 2^75*d) z ∧
      z < 37137907506513895751707 + 2^75*d := by
  have h := word_uniform_descent full_word_219
    (show 1936123065261193569491 < 37137907506513895751707 by norm_num)
    (show 3^word_219.length < 2^word_219.sum by norm_num [word_219, sharedPrefix, suffix_219]) d
  simpa [word_sum_219] using h

/-- Certificate 220; shared prefix plus independently witnessed suffix. -/
def suffix_220 : List Nat := [2, 1, 6, 2, 1, 3]
def word_220 : List Nat := sharedPrefix ++ suffix_220
theorem suffix_proof_220 : Word suffix_220 47658048604486390972889 1060263593526323822609 := by
  unfold suffix_220
  exact Word.cons
        (show ExactStep 47658048604486390972889 35743536453364793229667 2 from by
          refine ⟨by norm_num, ⟨23829024302243195486444, by norm_num⟩, by norm_num, ⟨17871768226682396614833, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 35743536453364793229667 53615304680047189844501 1 from by
          refine ⟨by norm_num, ⟨17871768226682396614833, by norm_num⟩, by norm_num, ⟨26807652340023594922250, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 53615304680047189844501 2513217406877212023961 6 from by
          refine ⟨by norm_num, ⟨26807652340023594922250, by norm_num⟩, by norm_num, ⟨1256608703438606011980, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2513217406877212023961 1884913055157909017971 2 from by
          refine ⟨by norm_num, ⟨1256608703438606011980, by norm_num⟩, by norm_num, ⟨942456527578954508985, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1884913055157909017971 2827369582736863526957 1 from by
          refine ⟨by norm_num, ⟨942456527578954508985, by norm_num⟩, by norm_num, ⟨1413684791368431763478, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2827369582736863526957 1060263593526323822609 3 from by
          refine ⟨by norm_num, ⟨1413684791368431763478, by norm_num⟩, by norm_num, ⟨530131796763161911304, by norm_num⟩⟩)
        (Word.nil 1060263593526323822609))))))
theorem full_word_220 : Word word_220 1129863074632850997275 1060263593526323822609 := by
  unfold word_220
  have hp := shared_prefix_all 1960
  have ht := suffix_proof_220
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_220 : word_220.length = 46 := by decide
theorem word_sum_220 : word_220.sum = 73 := by decide
theorem infinite_family_220 (d : Nat) :
    ∃ z : Nat, Word word_220 (1129863074632850997275 + 2^74*d) z ∧
      z < 1129863074632850997275 + 2^74*d := by
  have h := word_uniform_descent full_word_220
    (show 1060263593526323822609 < 1129863074632850997275 by norm_num)
    (show 3^word_220.length < 2^word_220.sum by norm_num [word_220, sharedPrefix, suffix_220]) d
  simpa [word_sum_220] using h

/-- Certificate 221; shared prefix plus independently witnessed suffix. -/
def suffix_221 : List Nat := [2, 1, 6, 2, 1, 4]
def word_221 : List Nat := sharedPrefix ++ suffix_221
theorem suffix_proof_221 : Word suffix_221 446040430366863833924057 4961600856589412459269 := by
  unfold suffix_221
  exact Word.cons
        (show ExactStep 446040430366863833924057 334530322775147875443043 2 from by
          refine ⟨by norm_num, ⟨223020215183431916962028, by norm_num⟩, by norm_num, ⟨167265161387573937721521, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 334530322775147875443043 501795484162721813164565 1 from by
          refine ⟨by norm_num, ⟨167265161387573937721521, by norm_num⟩, by norm_num, ⟨250897742081360906582282, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 501795484162721813164565 23521663320127584992089 6 from by
          refine ⟨by norm_num, ⟨250897742081360906582282, by norm_num⟩, by norm_num, ⟨11760831660063792496044, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 23521663320127584992089 17641247490095688744067 2 from by
          refine ⟨by norm_num, ⟨11760831660063792496044, by norm_num⟩, by norm_num, ⟨8820623745047844372033, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 17641247490095688744067 26461871235143533116101 1 from by
          refine ⟨by norm_num, ⟨8820623745047844372033, by norm_num⟩, by norm_num, ⟨13230935617571766558050, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 26461871235143533116101 4961600856589412459269 4 from by
          refine ⟨by norm_num, ⟨13230935617571766558050, by norm_num⟩, by norm_num, ⟨2480800428294706229634, by norm_num⟩⟩)
        (Word.nil 4961600856589412459269))))))
theorem full_word_221 : Word word_221 10574596040372141424667 4961600856589412459269 := by
  unfold word_221
  have hp := shared_prefix_all 18344
  have ht := suffix_proof_221
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_221 : word_221.length = 46 := by decide
theorem word_sum_221 : word_221.sum = 74 := by decide
theorem infinite_family_221 (d : Nat) :
    ∃ z : Nat, Word word_221 (10574596040372141424667 + 2^75*d) z ∧
      z < 10574596040372141424667 + 2^75*d := by
  have h := word_uniform_descent full_word_221
    (show 4961600856589412459269 < 10574596040372141424667 by norm_num)
    (show 3^word_221.length < 2^word_221.sum by norm_num [word_221, sharedPrefix, suffix_221]) d
  simpa [word_sum_221] using h

/-- Certificate 222; shared prefix plus independently witnessed suffix. -/
def suffix_222 : List Nat := [2, 1, 6, 2, 5]
def word_222 : List Nat := sharedPrefix ++ suffix_222
theorem suffix_proof_222 : Word suffix_222 894220609849538457244121 3315667849631314775243 := by
  unfold suffix_222
  exact Word.cons
        (show ExactStep 894220609849538457244121 670665457387153842933091 2 from by
          refine ⟨by norm_num, ⟨447110304924769228622060, by norm_num⟩, by norm_num, ⟨335332728693576921466545, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 670665457387153842933091 1005998186080730764399637 1 from by
          refine ⟨by norm_num, ⟨335332728693576921466545, by norm_num⟩, by norm_num, ⟨502999093040365382199818, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1005998186080730764399637 47156164972534254581233 6 from by
          refine ⟨by norm_num, ⟨502999093040365382199818, by norm_num⟩, by norm_num, ⟨23578082486267127290616, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 47156164972534254581233 35367123729400690935925 2 from by
          refine ⟨by norm_num, ⟨23578082486267127290616, by norm_num⟩, by norm_num, ⟨17683561864700345467962, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 35367123729400690935925 3315667849631314775243 5 from by
          refine ⟨by norm_num, ⟨17683561864700345467962, by norm_num⟩, by norm_num, ⟨1657833924815657387621, by norm_num⟩⟩)
        (Word.nil 3315667849631314775243)))))
theorem full_word_222 : Word word_222 21199920626828843155483 3315667849631314775243 := by
  unfold word_222
  have hp := shared_prefix_all 36776
  have ht := suffix_proof_222
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_222 : word_222.length = 45 := by decide
theorem word_sum_222 : word_222.sum = 74 := by decide
theorem infinite_family_222 (d : Nat) :
    ∃ z : Nat, Word word_222 (21199920626828843155483 + 2^75*d) z ∧
      z < 21199920626828843155483 + 2^75*d := by
  have h := word_uniform_descent full_word_222
    (show 3315667849631314775243 < 21199920626828843155483 by norm_num)
    (show 3^word_222.length < 2^word_222.sum by norm_num [word_222, sharedPrefix, suffix_222]) d
  simpa [word_sum_222] using h

/-- Certificate 223; shared prefix plus independently witnessed suffix. -/
def suffix_223 : List Nat := [2, 1, 6, 2, 4]
def word_223 : List Nat := sharedPrefix ++ suffix_223
theorem suffix_proof_223 : Word suffix_223 495838228087161014292953 3677022992711795851843 := by
  unfold suffix_223
  exact Word.cons
        (show ExactStep 495838228087161014292953 371878671065370760719715 2 from by
          refine ⟨by norm_num, ⟨247919114043580507146476, by norm_num⟩, by norm_num, ⟨185939335532685380359857, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 371878671065370760719715 557818006598056141079573 1 from by
          refine ⟨by norm_num, ⟨185939335532685380359857, by norm_num⟩, by norm_num, ⟨278909003299028070539786, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 557818006598056141079573 26147719059283881613105 6 from by
          refine ⟨by norm_num, ⟨278909003299028070539786, by norm_num⟩, by norm_num, ⟨13073859529641940806552, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 26147719059283881613105 19610789294462911209829 2 from by
          refine ⟨by norm_num, ⟨13073859529641940806552, by norm_num⟩, by norm_num, ⟨9805394647231455604914, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 19610789294462911209829 3677022992711795851843 4 from by
          refine ⟨by norm_num, ⟨9805394647231455604914, by norm_num⟩, by norm_num, ⟨1838511496355897925921, by norm_num⟩⟩)
        (Word.nil 3677022992711795851843)))))
theorem full_word_223 : Word word_223 11755187661089552728091 3677022992711795851843 := by
  unfold word_223
  have hp := shared_prefix_all 20392
  have ht := suffix_proof_223
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_223 : word_223.length = 45 := by decide
theorem word_sum_223 : word_223.sum = 73 := by decide
theorem infinite_family_223 (d : Nat) :
    ∃ z : Nat, Word word_223 (11755187661089552728091 + 2^74*d) z ∧
      z < 11755187661089552728091 + 2^74*d := by
  have h := word_uniform_descent full_word_223
    (show 3677022992711795851843 < 11755187661089552728091 by norm_num)
    (show 3^word_223.length < 2^word_223.sum by norm_num [word_223, sharedPrefix, suffix_223]) d
  simpa [word_sum_223] using h

/-- Certificate 224; shared prefix plus independently witnessed suffix. -/
def suffix_224 : List Nat := [2, 1, 6, 2, 3]
def word_224 : List Nat := sharedPrefix ++ suffix_224
theorem suffix_proof_224 : Word suffix_224 296647037205972292817369 4399733278872758005043 := by
  unfold suffix_224
  exact Word.cons
        (show ExactStep 296647037205972292817369 222485277904479219613027 2 from by
          refine ⟨by norm_num, ⟨148323518602986146408684, by norm_num⟩, by norm_num, ⟨111242638952239609806513, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 222485277904479219613027 333727916856718829419541 1 from by
          refine ⟨by norm_num, ⟨111242638952239609806513, by norm_num⟩, by norm_num, ⟨166863958428359414709770, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 333727916856718829419541 15643496102658695129041 6 from by
          refine ⟨by norm_num, ⟨166863958428359414709770, by norm_num⟩, by norm_num, ⟨7821748051329347564520, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 15643496102658695129041 11732622076994021346781 2 from by
          refine ⟨by norm_num, ⟨7821748051329347564520, by norm_num⟩, by norm_num, ⟨5866311038497010673390, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 11732622076994021346781 4399733278872758005043 3 from by
          refine ⟨by norm_num, ⟨5866311038497010673390, by norm_num⟩, by norm_num, ⟨2199866639436379002521, by norm_num⟩⟩)
        (Word.nil 4399733278872758005043)))))
theorem full_word_224 : Word word_224 7032821178219907514395 4399733278872758005043 := by
  unfold word_224
  have hp := shared_prefix_all 12200
  have ht := suffix_proof_224
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_224 : word_224.length = 45 := by decide
theorem word_sum_224 : word_224.sum = 72 := by decide
theorem infinite_family_224 (d : Nat) :
    ∃ z : Nat, Word word_224 (7032821178219907514395 + 2^73*d) z ∧
      z < 7032821178219907514395 + 2^73*d := by
  have h := word_uniform_descent full_word_224
    (show 4399733278872758005043 < 7032821178219907514395 by norm_num)
    (show 3^word_224.length < 2^word_224.sum by norm_num [word_224, sharedPrefix, suffix_224]) d
  simpa [word_sum_224] using h

/-- Certificate 225; shared prefix plus independently witnessed suffix. -/
def suffix_225 : List Nat := [2, 1, 6, 2, 2, 2]
def word_225 : List Nat := sharedPrefix ++ suffix_225
theorem suffix_proof_225 : Word suffix_225 396242632646566653555161 8815334448222262281547 := by
  unfold suffix_225
  exact Word.cons
        (show ExactStep 396242632646566653555161 297181974484924990166371 2 from by
          refine ⟨by norm_num, ⟨198121316323283326777580, by norm_num⟩, by norm_num, ⟨148590987242462495083185, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 297181974484924990166371 445772961727387485249557 1 from by
          refine ⟨by norm_num, ⟨148590987242462495083185, by norm_num⟩, by norm_num, ⟨222886480863693742624778, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 445772961727387485249557 20895607580971288371073 6 from by
          refine ⟨by norm_num, ⟨222886480863693742624778, by norm_num⟩, by norm_num, ⟨10447803790485644185536, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 20895607580971288371073 15671705685728466278305 2 from by
          refine ⟨by norm_num, ⟨10447803790485644185536, by norm_num⟩, by norm_num, ⟨7835852842864233139152, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 15671705685728466278305 11753779264296349708729 2 from by
          refine ⟨by norm_num, ⟨7835852842864233139152, by norm_num⟩, by norm_num, ⟨5876889632148174854364, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 11753779264296349708729 8815334448222262281547 2 from by
          refine ⟨by norm_num, ⟨5876889632148174854364, by norm_num⟩, by norm_num, ⟨4407667224111131140773, by norm_num⟩⟩)
        (Word.nil 8815334448222262281547))))))
theorem full_word_225 : Word word_225 9394004419654730121243 8815334448222262281547 := by
  unfold word_225
  have hp := shared_prefix_all 16296
  have ht := suffix_proof_225
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_225 : word_225.length = 46 := by decide
theorem word_sum_225 : word_225.sum = 73 := by decide
theorem infinite_family_225 (d : Nat) :
    ∃ z : Nat, Word word_225 (9394004419654730121243 + 2^74*d) z ∧
      z < 9394004419654730121243 + 2^74*d := by
  have h := word_uniform_descent full_word_225
    (show 8815334448222262281547 < 9394004419654730121243 by norm_num)
    (show 3^word_225.length < 2^word_225.sum by norm_num [word_225, sharedPrefix, suffix_225]) d
  simpa [word_sum_225] using h

/-- Certificate 226; shared prefix plus independently witnessed suffix. -/
def suffix_226 : List Nat := [2, 1, 6, 2, 2, 3]
def word_226 : List Nat := sharedPrefix ++ suffix_226
theorem suffix_proof_226 : Word suffix_226 1591389777933698982408665 17702074403589882784667 := by
  unfold suffix_226
  exact Word.cons
        (show ExactStep 1591389777933698982408665 1193542333450274236806499 2 from by
          refine ⟨by norm_num, ⟨795694888966849491204332, by norm_num⟩, by norm_num, ⟨596771166725137118403249, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1193542333450274236806499 1790313500175411355209749 1 from by
          refine ⟨by norm_num, ⟨596771166725137118403249, by norm_num⟩, by norm_num, ⟨895156750087705677604874, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1790313500175411355209749 83920945320722407275457 6 from by
          refine ⟨by norm_num, ⟨895156750087705677604874, by norm_num⟩, by norm_num, ⟨41960472660361203637728, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 83920945320722407275457 62940708990541805456593 2 from by
          refine ⟨by norm_num, ⟨41960472660361203637728, by norm_num⟩, by norm_num, ⟨31470354495270902728296, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 62940708990541805456593 47205531742906354092445 2 from by
          refine ⟨by norm_num, ⟨31470354495270902728296, by norm_num⟩, by norm_num, ⟨23602765871453177046222, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 47205531742906354092445 17702074403589882784667 3 from by
          refine ⟨by norm_num, ⟨23602765871453177046222, by norm_num⟩, by norm_num, ⟨8851037201794941392333, by norm_num⟩⟩)
        (Word.nil 17702074403589882784667))))))
theorem full_word_226 : Word word_226 37728203316872601403419 17702074403589882784667 := by
  unfold word_226
  have hp := shared_prefix_all 65448
  have ht := suffix_proof_226
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_226 : word_226.length = 46 := by decide
theorem word_sum_226 : word_226.sum = 74 := by decide
theorem infinite_family_226 (d : Nat) :
    ∃ z : Nat, Word word_226 (37728203316872601403419 + 2^75*d) z ∧
      z < 37728203316872601403419 + 2^75*d := by
  have h := word_uniform_descent full_word_226
    (show 17702074403589882784667 < 37728203316872601403419 by norm_num)
    (show 3^word_226.length < 2^word_226.sum by norm_num [word_226, sharedPrefix, suffix_226]) d
  simpa [word_sum_226] using h

/-- Certificate 227; shared prefix plus independently witnessed suffix. -/
def suffix_227 : List Nat := [2, 1, 4, 5]
def word_227 : List Nat := sharedPrefix ++ suffix_227
theorem suffix_proof_227 : Word suffix_227 2528794420467071263577 50007897475056829187 := by
  unfold suffix_227
  exact Word.cons
        (show ExactStep 2528794420467071263577 1896595815350303447683 2 from by
          refine ⟨by norm_num, ⟨1264397210233535631788, by norm_num⟩, by norm_num, ⟨948297907675151723841, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1896595815350303447683 2844893723025455171525 1 from by
          refine ⟨by norm_num, ⟨948297907675151723841, by norm_num⟩, by norm_num, ⟨1422446861512727585762, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 2844893723025455171525 533417573067272844661 4 from by
          refine ⟨by norm_num, ⟨1422446861512727585762, by norm_num⟩, by norm_num, ⟨266708786533636422330, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 533417573067272844661 50007897475056829187 5 from by
          refine ⟨by norm_num, ⟨266708786533636422330, by norm_num⟩, by norm_num, ⟨25003948737528414593, by norm_num⟩⟩)
        (Word.nil 50007897475056829187))))
theorem full_word_227 : Word word_227 59951918357697003547 50007897475056829187 := by
  unfold word_227
  have hp := shared_prefix_all 104
  have ht := suffix_proof_227
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_227 : word_227.length = 44 := by decide
theorem word_sum_227 : word_227.sum = 70 := by decide
theorem infinite_family_227 (d : Nat) :
    ∃ z : Nat, Word word_227 (59951918357697003547 + 2^71*d) z ∧
      z < 59951918357697003547 + 2^71*d := by
  have h := word_uniform_descent full_word_227
    (show 50007897475056829187 < 59951918357697003547 by norm_num)
    (show 3^word_227.length < 2^word_227.sum by norm_num [word_227, sharedPrefix, suffix_227]) d
  simpa [word_sum_227] using h

/-- Certificate 228; shared prefix plus independently witnessed suffix. -/
def suffix_228 : List Nat := [2, 1, 4, 7]
def word_228 : List Nat := sharedPrefix ++ suffix_228
theorem suffix_proof_228 : Word suffix_228 52326592140764251632473 258694699914667015517 := by
  unfold suffix_228
  exact Word.cons
        (show ExactStep 52326592140764251632473 39244944105573188724355 2 from by
          refine ⟨by norm_num, ⟨26163296070382125816236, by norm_num⟩, by norm_num, ⟨19622472052786594362177, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 39244944105573188724355 58867416158359783086533 1 from by
          refine ⟨by norm_num, ⟨19622472052786594362177, by norm_num⟩, by norm_num, ⟨29433708079179891543266, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 58867416158359783086533 11037640529692459328725 4 from by
          refine ⟨by norm_num, ⟨29433708079179891543266, by norm_num⟩, by norm_num, ⟨5518820264846229664362, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 11037640529692459328725 258694699914667015517 7 from by
          refine ⟨by norm_num, ⟨5518820264846229664362, by norm_num⟩, by norm_num, ⟨129347349957333507758, by norm_num⟩⟩)
        (Word.nil 258694699914667015517))))
theorem full_word_228 : Word word_228 1240543539075108306971 258694699914667015517 := by
  unfold word_228
  have hp := shared_prefix_all 2152
  have ht := suffix_proof_228
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_228 : word_228.length = 44 := by decide
theorem word_sum_228 : word_228.sum = 72 := by decide
theorem infinite_family_228 (d : Nat) :
    ∃ z : Nat, Word word_228 (1240543539075108306971 + 2^73*d) z ∧
      z < 1240543539075108306971 + 2^73*d := by
  have h := word_uniform_descent full_word_228
    (show 258694699914667015517 < 1240543539075108306971 by norm_num)
    (show 3^word_228.length < 2^word_228.sum by norm_num [word_228, sharedPrefix, suffix_228]) d
  simpa [word_sum_228] using h

/-- Certificate 229; shared prefix plus independently witnessed suffix. -/
def suffix_229 : List Nat := [2, 1, 4, 8]
def word_229 : List Nat := sharedPrefix ++ suffix_229
theorem suffix_proof_229 : Word suffix_229 251517783021952973108057 621732801049139124199 := by
  unfold suffix_229
  exact Word.cons
        (show ExactStep 251517783021952973108057 188638337266464729831043 2 from by
          refine ⟨by norm_num, ⟨125758891510976486554028, by norm_num⟩, by norm_num, ⟨94319168633232364915521, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 188638337266464729831043 282957505899697094746565 1 from by
          refine ⟨by norm_num, ⟨94319168633232364915521, by norm_num⟩, by norm_num, ⟨141478752949848547373282, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 282957505899697094746565 53054532356193205264981 4 from by
          refine ⟨by norm_num, ⟨141478752949848547373282, by norm_num⟩, by norm_num, ⟨26527266178096602632490, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 53054532356193205264981 621732801049139124199 8 from by
          refine ⟨by norm_num, ⟨26527266178096602632490, by norm_num⟩, by norm_num, ⟨310866400524569562099, by norm_num⟩⟩)
        (Word.nil 621732801049139124199))))
theorem full_word_229 : Word word_229 5962910021944753520667 621732801049139124199 := by
  unfold word_229
  have hp := shared_prefix_all 10344
  have ht := suffix_proof_229
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_229 : word_229.length = 44 := by decide
theorem word_sum_229 : word_229.sum = 73 := by decide
theorem infinite_family_229 (d : Nat) :
    ∃ z : Nat, Word word_229 (5962910021944753520667 + 2^74*d) z ∧
      z < 5962910021944753520667 + 2^74*d := by
  have h := word_uniform_descent full_word_229
    (show 621732801049139124199 < 5962910021944753520667 by norm_num)
    (show 3^word_229.length < 2^word_229.sum by norm_num [word_229, sharedPrefix, suffix_229]) d
  simpa [word_sum_229] using h

/-- Certificate 230; shared prefix plus independently witnessed suffix. -/
def suffix_230 : List Nat := [2, 1, 4, 9]
def word_230 : List Nat := sharedPrefix ++ suffix_230
theorem suffix_proof_230 : Word suffix_230 1446664928309085301961561 1788022753799986411421 := by
  unfold suffix_230
  exact Word.cons
        (show ExactStep 1446664928309085301961561 1084998696231813976471171 2 from by
          refine ⟨by norm_num, ⟨723332464154542650980780, by norm_num⟩, by norm_num, ⟨542499348115906988235585, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1084998696231813976471171 1627498044347720964706757 1 from by
          refine ⟨by norm_num, ⟨542499348115906988235585, by norm_num⟩, by norm_num, ⟨813749022173860482353378, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1627498044347720964706757 305155883315197680882517 4 from by
          refine ⟨by norm_num, ⟨813749022173860482353378, by norm_num⟩, by norm_num, ⟨152577941657598840441258, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 305155883315197680882517 1788022753799986411421 9 from by
          refine ⟨by norm_num, ⟨152577941657598840441258, by norm_num⟩, by norm_num, ⟨894011376899993205710, by norm_num⟩⟩)
        (Word.nil 1788022753799986411421))))
theorem full_word_230 : Word word_230 34297108919162624802843 1788022753799986411421 := by
  unfold word_230
  have hp := shared_prefix_all 59496
  have ht := suffix_proof_230
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_230 : word_230.length = 44 := by decide
theorem word_sum_230 : word_230.sum = 74 := by decide
theorem infinite_family_230 (d : Nat) :
    ∃ z : Nat, Word word_230 (34297108919162624802843 + 2^75*d) z ∧
      z < 34297108919162624802843 + 2^75*d := by
  have h := word_uniform_descent full_word_230
    (show 1788022753799986411421 < 34297108919162624802843 by norm_num)
    (show 3^word_230.length < 2^word_230.sum by norm_num [word_230, sharedPrefix, suffix_230]) d
  simpa [word_sum_230] using h

/-- Certificate 231; shared prefix plus independently witnessed suffix. -/
def suffix_231 : List Nat := [2, 1, 4, 6]
def word_231 : List Nat := sharedPrefix ++ suffix_231
theorem suffix_proof_231 : Word suffix_231 151922187581358612370265 1502160302012945263915 := by
  unfold suffix_231
  exact Word.cons
        (show ExactStep 151922187581358612370265 113941640686018959277699 2 from by
          refine ⟨by norm_num, ⟨75961093790679306185132, by norm_num⟩, by norm_num, ⟨56970820343009479638849, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 113941640686018959277699 170912461029028438916549 1 from by
          refine ⟨by norm_num, ⟨56970820343009479638849, by norm_num⟩, by norm_num, ⟨85456230514514219458274, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 170912461029028438916549 32046086442942832296853 4 from by
          refine ⟨by norm_num, ⟨85456230514514219458274, by norm_num⟩, by norm_num, ⟨16023043221471416148426, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 32046086442942832296853 1502160302012945263915 6 from by
          refine ⟨by norm_num, ⟨16023043221471416148426, by norm_num⟩, by norm_num, ⟨751080151006472631957, by norm_num⟩⟩)
        (Word.nil 1502160302012945263915))))
theorem full_word_231 : Word word_231 3601726780509930913819 1502160302012945263915 := by
  unfold word_231
  have hp := shared_prefix_all 6248
  have ht := suffix_proof_231
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_231 : word_231.length = 44 := by decide
theorem word_sum_231 : word_231.sum = 71 := by decide
theorem infinite_family_231 (d : Nat) :
    ∃ z : Nat, Word word_231 (3601726780509930913819 + 2^72*d) z ∧
      z < 3601726780509930913819 + 2^72*d := by
  have h := word_uniform_descent full_word_231
    (show 1502160302012945263915 < 3601726780509930913819 by norm_num)
    (show 3^word_231.length < 2^word_231.sum by norm_num [word_231, sharedPrefix, suffix_231]) d
  simpa [word_sum_231] using h

/-- Certificate 232; shared prefix plus independently witnessed suffix. -/
def suffix_232 : List Nat := [2, 1, 4, 4, 1, 4]
def word_232 : List Nat := sharedPrefix ++ suffix_232
theorem suffix_proof_232 : Word suffix_232 326214479602398743661401 3628698053438548036639 := by
  unfold suffix_232
  exact Word.cons
        (show ExactStep 326214479602398743661401 244660859701799057746051 2 from by
          refine ⟨by norm_num, ⟨163107239801199371830700, by norm_num⟩, by norm_num, ⟨122330429850899528873025, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 244660859701799057746051 366991289552698586619077 1 from by
          refine ⟨by norm_num, ⟨122330429850899528873025, by norm_num⟩, by norm_num, ⟨183495644776349293309538, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 366991289552698586619077 68810866791130984991077 4 from by
          refine ⟨by norm_num, ⟨183495644776349293309538, by norm_num⟩, by norm_num, ⟨34405433395565492495538, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 68810866791130984991077 12902037523337059685827 4 from by
          refine ⟨by norm_num, ⟨34405433395565492495538, by norm_num⟩, by norm_num, ⟨6451018761668529842913, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 12902037523337059685827 19353056285005589528741 1 from by
          refine ⟨by norm_num, ⟨6451018761668529842913, by norm_num⟩, by norm_num, ⟨9676528142502794764370, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 19353056285005589528741 3628698053438548036639 4 from by
          refine ⟨by norm_num, ⟨9676528142502794764370, by norm_num⟩, by norm_num, ⟨1814349026719274018319, by norm_num⟩⟩)
        (Word.nil 3628698053438548036639))))))
theorem full_word_232 : Word word_232 7733797453020870475803 3628698053438548036639 := by
  unfold word_232
  have hp := shared_prefix_all 13416
  have ht := suffix_proof_232
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_232 : word_232.length = 46 := by decide
theorem word_sum_232 : word_232.sum = 74 := by decide
theorem infinite_family_232 (d : Nat) :
    ∃ z : Nat, Word word_232 (7733797453020870475803 + 2^75*d) z ∧
      z < 7733797453020870475803 + 2^75*d := by
  have h := word_uniform_descent full_word_232
    (show 3628698053438548036639 < 7733797453020870475803 by norm_num)
    (show 3^word_232.length < 2^word_232.sum by norm_num [word_232, sharedPrefix, suffix_232]) d
  simpa [word_sum_232] using h

/-- Certificate 233; shared prefix plus independently witnessed suffix. -/
def suffix_233 : List Nat := [2, 1, 4, 4, 1, 3]
def word_233 : List Nat := sharedPrefix ++ suffix_233
theorem suffix_proof_233 : Word suffix_233 724596861364776186612569 16120334226529597169207 := by
  unfold suffix_233
  exact Word.cons
        (show ExactStep 724596861364776186612569 543447646023582139959427 2 from by
          refine ⟨by norm_num, ⟨362298430682388093306284, by norm_num⟩, by norm_num, ⟨271723823011791069979713, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 543447646023582139959427 815171469035373209939141 1 from by
          refine ⟨by norm_num, ⟨271723823011791069979713, by norm_num⟩, by norm_num, ⟨407585734517686604969570, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 815171469035373209939141 152844650444132476863589 4 from by
          refine ⟨by norm_num, ⟨407585734517686604969570, by norm_num⟩, by norm_num, ⟨76422325222066238431794, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 152844650444132476863589 28658371958274839411923 4 from by
          refine ⟨by norm_num, ⟨76422325222066238431794, by norm_num⟩, by norm_num, ⟨14329185979137419705961, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 28658371958274839411923 42987557937412259117885 1 from by
          refine ⟨by norm_num, ⟨14329185979137419705961, by norm_num⟩, by norm_num, ⟨21493778968706129558942, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 42987557937412259117885 16120334226529597169207 3 from by
          refine ⟨by norm_num, ⟨21493778968706129558942, by norm_num⟩, by norm_num, ⟨8060167113264798584603, by norm_num⟩⟩)
        (Word.nil 16120334226529597169207))))))
theorem full_word_233 : Word word_233 17178530418760160903195 16120334226529597169207 := by
  unfold word_233
  have hp := shared_prefix_all 29800
  have ht := suffix_proof_233
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_233 : word_233.length = 46 := by decide
theorem word_sum_233 : word_233.sum = 73 := by decide
theorem infinite_family_233 (d : Nat) :
    ∃ z : Nat, Word word_233 (17178530418760160903195 + 2^74*d) z ∧
      z < 17178530418760160903195 + 2^74*d := by
  have h := word_uniform_descent full_word_233
    (show 16120334226529597169207 < 17178530418760160903195 by norm_num)
    (show 3^word_233.length < 2^word_233.sum by norm_num [word_233, sharedPrefix, suffix_233]) d
  simpa [word_sum_233] using h

/-- Certificate 234; shared prefix plus independently witnessed suffix. -/
def suffix_234 : List Nat := [2, 1, 4, 4, 2, 2]
def word_234 : List Nat := sharedPrefix ++ suffix_234
theorem suffix_proof_234 : Word suffix_234 276416681882101563292505 6149528841920533436287 := by
  unfold suffix_234
  exact Word.cons
        (show ExactStep 276416681882101563292505 207312511411576172469379 2 from by
          refine ⟨by norm_num, ⟨138208340941050781646252, by norm_num⟩, by norm_num, ⟨103656255705788086234689, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 207312511411576172469379 310968767117364258704069 1 from by
          refine ⟨by norm_num, ⟨103656255705788086234689, by norm_num⟩, by norm_num, ⟨155484383558682129352034, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 310968767117364258704069 58306643834505798507013 4 from by
          refine ⟨by norm_num, ⟨155484383558682129352034, by norm_num⟩, by norm_num, ⟨29153321917252899253506, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 58306643834505798507013 10932495718969837220065 4 from by
          refine ⟨by norm_num, ⟨29153321917252899253506, by norm_num⟩, by norm_num, ⟨5466247859484918610032, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 10932495718969837220065 8199371789227377915049 2 from by
          refine ⟨by norm_num, ⟨5466247859484918610032, by norm_num⟩, by norm_num, ⟨4099685894613688957524, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 8199371789227377915049 6149528841920533436287 2 from by
          refine ⟨by norm_num, ⟨4099685894613688957524, by norm_num⟩, by norm_num, ⟨3074764420960266718143, by norm_num⟩⟩)
        (Word.nil 6149528841920533436287))))))
theorem full_word_234 : Word word_234 6553205832303459172379 6149528841920533436287 := by
  unfold word_234
  have hp := shared_prefix_all 11368
  have ht := suffix_proof_234
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_234 : word_234.length = 46 := by decide
theorem word_sum_234 : word_234.sum = 73 := by decide
theorem infinite_family_234 (d : Nat) :
    ∃ z : Nat, Word word_234 (6553205832303459172379 + 2^74*d) z ∧
      z < 6553205832303459172379 + 2^74*d := by
  have h := word_uniform_descent full_word_234
    (show 6149528841920533436287 < 6553205832303459172379 by norm_num)
    (show 3^word_234.length < 2^word_234.sum by norm_num [word_234, sharedPrefix, suffix_234]) d
  simpa [word_sum_234] using h

/-- Certificate 235; shared prefix plus independently witnessed suffix. -/
def suffix_235 : List Nat := [2, 1, 4, 4, 2, 3]
def word_235 : List Nat := sharedPrefix ++ suffix_235
theorem suffix_proof_235 : Word suffix_235 1471563827169233892146009 16369171600439018362037 := by
  unfold suffix_235
  exact Word.cons
        (show ExactStep 1471563827169233892146009 1103672870376925419109507 2 from by
          refine ⟨by norm_num, ⟨735781913584616946073004, by norm_num⟩, by norm_num, ⟨551836435188462709554753, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1103672870376925419109507 1655509305565388128664261 1 from by
          refine ⟨by norm_num, ⟨551836435188462709554753, by norm_num⟩, by norm_num, ⟨827754652782694064332130, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1655509305565388128664261 310407994793510274124549 4 from by
          refine ⟨by norm_num, ⟨827754652782694064332130, by norm_num⟩, by norm_num, ⟨155203997396755137062274, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 310407994793510274124549 58201499023783176398353 4 from by
          refine ⟨by norm_num, ⟨155203997396755137062274, by norm_num⟩, by norm_num, ⟨29100749511891588199176, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 58201499023783176398353 43651124267837382298765 2 from by
          refine ⟨by norm_num, ⟨29100749511891588199176, by norm_num⟩, by norm_num, ⟨21825562133918691149382, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 43651124267837382298765 16369171600439018362037 3 from by
          refine ⟨by norm_num, ⟨21825562133918691149382, by norm_num⟩, by norm_num, ⟨8184585800219509181018, by norm_num⟩⟩)
        (Word.nil 16369171600439018362037))))))
theorem full_word_235 : Word word_235 34887404729521330454555 16369171600439018362037 := by
  unfold word_235
  have hp := shared_prefix_all 60520
  have ht := suffix_proof_235
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_235 : word_235.length = 46 := by decide
theorem word_sum_235 : word_235.sum = 74 := by decide
theorem infinite_family_235 (d : Nat) :
    ∃ z : Nat, Word word_235 (34887404729521330454555 + 2^75*d) z ∧
      z < 34887404729521330454555 + 2^75*d := by
  have h := word_uniform_descent full_word_235
    (show 16369171600439018362037 < 34887404729521330454555 by norm_num)
    (show 3^word_235.length < 2^word_235.sum by norm_num [word_235, sharedPrefix, suffix_235]) d
  simpa [word_sum_235] using h

/-- Certificate 236; shared prefix plus independently witnessed suffix. -/
def suffix_236 : List Nat := [2, 1, 4, 4, 3]
def word_236 : List Nat := sharedPrefix ++ suffix_236
theorem suffix_proof_236 : Word suffix_236 176821086441507202554713 2622529541338272108203 := by
  unfold suffix_236
  exact Word.cons
        (show ExactStep 176821086441507202554713 132615814831130401916035 2 from by
          refine ⟨by norm_num, ⟨88410543220753601277356, by norm_num⟩, by norm_num, ⟨66307907415565200958017, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 132615814831130401916035 198923722246695602874053 1 from by
          refine ⟨by norm_num, ⟨66307907415565200958017, by norm_num⟩, by norm_num, ⟨99461861123347801437026, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 198923722246695602874053 37298197921255425538885 4 from by
          refine ⟨by norm_num, ⟨99461861123347801437026, by norm_num⟩, by norm_num, ⟨18649098960627712769442, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 37298197921255425538885 6993412110235392288541 4 from by
          refine ⟨by norm_num, ⟨18649098960627712769442, by norm_num⟩, by norm_num, ⟨3496706055117696144270, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 6993412110235392288541 2622529541338272108203 3 from by
          refine ⟨by norm_num, ⟨3496706055117696144270, by norm_num⟩, by norm_num, ⟨1311264770669136054101, by norm_num⟩⟩)
        (Word.nil 2622529541338272108203)))))
theorem full_word_236 : Word word_236 4192022590868636565531 2622529541338272108203 := by
  unfold word_236
  have hp := shared_prefix_all 7272
  have ht := suffix_proof_236
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_236 : word_236.length = 45 := by decide
theorem word_sum_236 : word_236.sum = 72 := by decide
theorem infinite_family_236 (d : Nat) :
    ∃ z : Nat, Word word_236 (4192022590868636565531 + 2^73*d) z ∧
      z < 4192022590868636565531 + 2^73*d := by
  have h := word_uniform_descent full_word_236
    (show 2622529541338272108203 < 4192022590868636565531 by norm_num)
    (show 3^word_236.length < 2^word_236.sum by norm_num [word_236, sharedPrefix, suffix_236]) d
  simpa [word_sum_236] using h

/-- Certificate 237; shared prefix plus independently witnessed suffix. -/
def suffix_237 : List Nat := [2, 1, 4, 4, 4]
def word_237 : List Nat := sharedPrefix ++ suffix_237
theorem suffix_proof_237 : Word suffix_237 376012277322695924030297 2788421123944552903423 := by
  unfold suffix_237
  exact Word.cons
        (show ExactStep 376012277322695924030297 282009207992021943022723 2 from by
          refine ⟨by norm_num, ⟨188006138661347962015148, by norm_num⟩, by norm_num, ⟨141004603996010971511361, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 282009207992021943022723 423013811988032914534085 1 from by
          refine ⟨by norm_num, ⟨141004603996010971511361, by norm_num⟩, by norm_num, ⟨211506905994016457267042, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 423013811988032914534085 79315089747756171475141 4 from by
          refine ⟨by norm_num, ⟨211506905994016457267042, by norm_num⟩, by norm_num, ⟨39657544873878085737570, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 79315089747756171475141 14871579327704282151589 4 from by
          refine ⟨by norm_num, ⟨39657544873878085737570, by norm_num⟩, by norm_num, ⟨7435789663852141075794, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 14871579327704282151589 2788421123944552903423 4 from by
          refine ⟨by norm_num, ⟨7435789663852141075794, by norm_num⟩, by norm_num, ⟨1394210561972276451711, by norm_num⟩⟩)
        (Word.nil 2788421123944552903423)))))
theorem full_word_237 : Word word_237 8914389073738281779227 2788421123944552903423 := by
  unfold word_237
  have hp := shared_prefix_all 15464
  have ht := suffix_proof_237
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_237 : word_237.length = 45 := by decide
theorem word_sum_237 : word_237.sum = 73 := by decide
theorem infinite_family_237 (d : Nat) :
    ∃ z : Nat, Word word_237 (8914389073738281779227 + 2^74*d) z ∧
      z < 8914389073738281779227 + 2^74*d := by
  have h := word_uniform_descent full_word_237
    (show 2788421123944552903423 < 8914389073738281779227 by norm_num)
    (show 3^word_237.length < 2^word_237.sum by norm_num [word_237, sharedPrefix, suffix_237]) d
  simpa [word_sum_237] using h

/-- Certificate 238; shared prefix plus independently witnessed suffix. -/
def suffix_238 : List Nat := [2, 1, 4, 4, 5]
def word_238 : List Nat := sharedPrefix ++ suffix_238
theorem suffix_proof_238 : Word suffix_238 774394659085073366981465 2871366915247693301033 := by
  unfold suffix_238
  exact Word.cons
        (show ExactStep 774394659085073366981465 580795994313805025236099 2 from by
          refine ⟨by norm_num, ⟨387197329542536683490732, by norm_num⟩, by norm_num, ⟨290397997156902512618049, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 580795994313805025236099 871193991470707537854149 1 from by
          refine ⟨by norm_num, ⟨290397997156902512618049, by norm_num⟩, by norm_num, ⟨435596995735353768927074, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 871193991470707537854149 163348873400757663347653 4 from by
          refine ⟨by norm_num, ⟨435596995735353768927074, by norm_num⟩, by norm_num, ⟨81674436700378831673826, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 163348873400757663347653 30627913762642061877685 4 from by
          refine ⟨by norm_num, ⟨81674436700378831673826, by norm_num⟩, by norm_num, ⟨15313956881321030938842, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 30627913762642061877685 2871366915247693301033 5 from by
          refine ⟨by norm_num, ⟨15313956881321030938842, by norm_num⟩, by norm_num, ⟨1435683457623846650516, by norm_num⟩⟩)
        (Word.nil 2871366915247693301033)))))
theorem full_word_238 : Word word_238 18359122039477572206619 2871366915247693301033 := by
  unfold word_238
  have hp := shared_prefix_all 31848
  have ht := suffix_proof_238
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_238 : word_238.length = 45 := by decide
theorem word_sum_238 : word_238.sum = 74 := by decide
theorem infinite_family_238 (d : Nat) :
    ∃ z : Nat, Word word_238 (18359122039477572206619 + 2^75*d) z ∧
      z < 18359122039477572206619 + 2^75*d := by
  have h := word_uniform_descent full_word_238
    (show 2871366915247693301033 < 18359122039477572206619 by norm_num)
    (show 3^word_238.length < 2^word_238.sum by norm_num [word_238, sharedPrefix, suffix_238]) d
  simpa [word_sum_238] using h

/-- Certificate 239; shared prefix plus independently witnessed suffix. -/
def suffix_239 : List Nat := [2, 1, 4, 3, 3, 3]
def word_239 : List Nat := sharedPrefix ++ suffix_239
theorem suffix_proof_239 : Word suffix_239 1010934198256484973733721 11245285500014916165953 := by
  unfold suffix_239
  exact Word.cons
        (show ExactStep 1010934198256484973733721 758200648692363730300291 2 from by
          refine ⟨by norm_num, ⟨505467099128242486866860, by norm_num⟩, by norm_num, ⟨379100324346181865150145, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 758200648692363730300291 1137300973038545595450437 1 from by
          refine ⟨by norm_num, ⟨379100324346181865150145, by norm_num⟩, by norm_num, ⟨568650486519272797725218, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1137300973038545595450437 213243932444727299146957 4 from by
          refine ⟨by norm_num, ⟨568650486519272797725218, by norm_num⟩, by norm_num, ⟨106621966222363649573478, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 213243932444727299146957 79966474666772737180109 3 from by
          refine ⟨by norm_num, ⟨106621966222363649573478, by norm_num⟩, by norm_num, ⟨39983237333386368590054, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 79966474666772737180109 29987428000039776442541 3 from by
          refine ⟨by norm_num, ⟨39983237333386368590054, by norm_num⟩, by norm_num, ⟨14993714000019888221270, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 29987428000039776442541 11245285500014916165953 3 from by
          refine ⟨by norm_num, ⟨14993714000019888221270, by norm_num⟩, by norm_num, ⟨5622642750007458082976, by norm_num⟩⟩)
        (Word.nil 11245285500014916165953))))))
theorem full_word_239 : Word word_239 23966932237885275897883 11245285500014916165953 := by
  unfold word_239
  have hp := shared_prefix_all 41576
  have ht := suffix_proof_239
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_239 : word_239.length = 46 := by decide
theorem word_sum_239 : word_239.sum = 74 := by decide
theorem infinite_family_239 (d : Nat) :
    ∃ z : Nat, Word word_239 (23966932237885275897883 + 2^75*d) z ∧
      z < 23966932237885275897883 + 2^75*d := by
  have h := word_uniform_descent full_word_239
    (show 11245285500014916165953 < 23966932237885275897883 by norm_num)
    (show 3^word_239.length < 2^word_239.sum by norm_num [word_239, sharedPrefix, suffix_239]) d
  simpa [word_sum_239] using h

/-- Certificate 240; shared prefix plus independently witnessed suffix. -/
def suffix_240 : List Nat := [2, 1, 4, 3, 3, 2]
def word_240 : List Nat := sharedPrefix ++ suffix_240
theorem suffix_proof_240 : Word suffix_240 612551816494107530782553 13627632880377331235977 := by
  unfold suffix_240
  exact Word.cons
        (show ExactStep 612551816494107530782553 459413862370580648086915 2 from by
          refine ⟨by norm_num, ⟨306275908247053765391276, by norm_num⟩, by norm_num, ⟨229706931185290324043457, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 459413862370580648086915 689120793555870972130373 1 from by
          refine ⟨by norm_num, ⟨229706931185290324043457, by norm_num⟩, by norm_num, ⟨344560396777935486065186, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 689120793555870972130373 129210148791725807274445 4 from by
          refine ⟨by norm_num, ⟨344560396777935486065186, by norm_num⟩, by norm_num, ⟨64605074395862903637222, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 129210148791725807274445 48453805796897177727917 3 from by
          refine ⟨by norm_num, ⟨64605074395862903637222, by norm_num⟩, by norm_num, ⟨24226902898448588863958, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 48453805796897177727917 18170177173836441647969 3 from by
          refine ⟨by norm_num, ⟨24226902898448588863958, by norm_num⟩, by norm_num, ⟨9085088586918220823984, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 18170177173836441647969 13627632880377331235977 2 from by
          refine ⟨by norm_num, ⟨9085088586918220823984, by norm_num⟩, by norm_num, ⟨6813816440188665617988, by norm_num⟩⟩)
        (Word.nil 13627632880377331235977))))))
theorem full_word_240 : Word word_240 14522199272145985470491 13627632880377331235977 := by
  unfold word_240
  have hp := shared_prefix_all 25192
  have ht := suffix_proof_240
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_240 : word_240.length = 46 := by decide
theorem word_sum_240 : word_240.sum = 73 := by decide
theorem infinite_family_240 (d : Nat) :
    ∃ z : Nat, Word word_240 (14522199272145985470491 + 2^74*d) z ∧
      z < 14522199272145985470491 + 2^74*d := by
  have h := word_uniform_descent full_word_240
    (show 13627632880377331235977 < 14522199272145985470491 by norm_num)
    (show 3^word_240.length < 2^word_240.sum by norm_num [word_240, sharedPrefix, suffix_240]) d
  simpa [word_sum_240] using h

/-- Certificate 241; shared prefix plus independently witnessed suffix. -/
def suffix_241 : List Nat := [2, 1, 4, 3, 4]
def word_241 : List Nat := sharedPrefix ++ suffix_241
theorem suffix_proof_241 : Word suffix_241 114573839291135727093593 1699306820541136577377 := by
  unfold suffix_241
  exact Word.cons
        (show ExactStep 114573839291135727093593 85930379468351795320195 2 from by
          refine ⟨by norm_num, ⟨57286919645567863546796, by norm_num⟩, by norm_num, ⟨42965189734175897660097, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 85930379468351795320195 128895569202527692980293 1 from by
          refine ⟨by norm_num, ⟨42965189734175897660097, by norm_num⟩, by norm_num, ⟨64447784601263846490146, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 128895569202527692980293 24167919225473942433805 4 from by
          refine ⟨by norm_num, ⟨64447784601263846490146, by norm_num⟩, by norm_num, ⟨12083959612736971216902, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 24167919225473942433805 9062969709552728412677 3 from by
          refine ⟨by norm_num, ⟨12083959612736971216902, by norm_num⟩, by norm_num, ⟨4531484854776364206338, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 9062969709552728412677 1699306820541136577377 4 from by
          refine ⟨by norm_num, ⟨4531484854776364206338, by norm_num⟩, by norm_num, ⟨849653410270568288688, by norm_num⟩⟩)
        (Word.nil 1699306820541136577377)))))
theorem full_word_241 : Word word_241 2716283064971872436251 1699306820541136577377 := by
  unfold word_241
  have hp := shared_prefix_all 4712
  have ht := suffix_proof_241
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_241 : word_241.length = 45 := by decide
theorem word_sum_241 : word_241.sum = 72 := by decide
theorem infinite_family_241 (d : Nat) :
    ∃ z : Nat, Word word_241 (2716283064971872436251 + 2^73*d) z ∧
      z < 2716283064971872436251 + 2^73*d := by
  have h := word_uniform_descent full_word_241
    (show 1699306820541136577377 < 2716283064971872436251 by norm_num)
    (show 3^word_241.length < 2^word_241.sum by norm_num [word_241, sharedPrefix, suffix_241]) d
  simpa [word_sum_241] using h

/-- Certificate 242; shared prefix plus independently witnessed suffix. -/
def suffix_242 : List Nat := [2, 1, 4, 3, 6]
def word_242 : List Nat := sharedPrefix ++ suffix_242
theorem suffix_proof_242 : Word suffix_242 313765030172324448569177 1163404881772992569005 := by
  unfold suffix_242
  exact Word.cons
        (show ExactStep 313765030172324448569177 235323772629243336426883 2 from by
          refine ⟨by norm_num, ⟨156882515086162224284588, by norm_num⟩, by norm_num, ⟨117661886314621668213441, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 235323772629243336426883 352985658943865004640325 1 from by
          refine ⟨by norm_num, ⟨117661886314621668213441, by norm_num⟩, by norm_num, ⟨176492829471932502320162, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 352985658943865004640325 66184811051974688370061 4 from by
          refine ⟨by norm_num, ⟨176492829471932502320162, by norm_num⟩, by norm_num, ⟨33092405525987344185030, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 66184811051974688370061 24819304144490508138773 3 from by
          refine ⟨by norm_num, ⟨33092405525987344185030, by norm_num⟩, by norm_num, ⟨12409652072245254069386, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 24819304144490508138773 1163404881772992569005 6 from by
          refine ⟨by norm_num, ⟨12409652072245254069386, by norm_num⟩, by norm_num, ⟨581702440886496284502, by norm_num⟩⟩)
        (Word.nil 1163404881772992569005)))))
theorem full_word_242 : Word word_242 7438649547841517649947 1163404881772992569005 := by
  unfold word_242
  have hp := shared_prefix_all 12904
  have ht := suffix_proof_242
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_242 : word_242.length = 45 := by decide
theorem word_sum_242 : word_242.sum = 74 := by decide
theorem infinite_family_242 (d : Nat) :
    ∃ z : Nat, Word word_242 (7438649547841517649947 + 2^75*d) z ∧
      z < 7438649547841517649947 + 2^75*d := by
  have h := word_uniform_descent full_word_242
    (show 1163404881772992569005 < 7438649547841517649947 by norm_num)
    (show 3^word_242.length < 2^word_242.sum by norm_num [word_242, sharedPrefix, suffix_242]) d
  simpa [word_sum_242] using h

/-- Certificate 243; shared prefix plus independently witnessed suffix. -/
def suffix_243 : List Nat := [2, 1, 4, 3, 5]
def word_243 : List Nat := sharedPrefix ++ suffix_243
theorem suffix_proof_243 : Word suffix_243 712147411934701891520345 5281122470096818836653 := by
  unfold suffix_243
  exact Word.cons
        (show ExactStep 712147411934701891520345 534110558951026418640259 2 from by
          refine ⟨by norm_num, ⟨356073705967350945760172, by norm_num⟩, by norm_num, ⟨267055279475513209320129, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 534110558951026418640259 801165838426539627960389 1 from by
          refine ⟨by norm_num, ⟨267055279475513209320129, by norm_num⟩, by norm_num, ⟨400582919213269813980194, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 801165838426539627960389 150218594704976180242573 4 from by
          refine ⟨by norm_num, ⟨400582919213269813980194, by norm_num⟩, by norm_num, ⟨75109297352488090121286, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 150218594704976180242573 56331973014366067590965 3 from by
          refine ⟨by norm_num, ⟨75109297352488090121286, by norm_num⟩, by norm_num, ⟨28165986507183033795482, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 56331973014366067590965 5281122470096818836653 5 from by
          refine ⟨by norm_num, ⟨28165986507183033795482, by norm_num⟩, by norm_num, ⟨2640561235048409418326, by norm_num⟩⟩)
        (Word.nil 5281122470096818836653)))))
theorem full_word_243 : Word word_243 16883382513580808077339 5281122470096818836653 := by
  unfold word_243
  have hp := shared_prefix_all 29288
  have ht := suffix_proof_243
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_243 : word_243.length = 45 := by decide
theorem word_sum_243 : word_243.sum = 73 := by decide
theorem infinite_family_243 (d : Nat) :
    ∃ z : Nat, Word word_243 (16883382513580808077339 + 2^74*d) z ∧
      z < 16883382513580808077339 + 2^74*d := by
  have h := word_uniform_descent full_word_243
    (show 5281122470096818836653 < 16883382513580808077339 by norm_num)
    (show 3^word_243.length < 2^word_243.sum by norm_num [word_243, sharedPrefix, suffix_243]) d
  simpa [word_sum_243] using h

/-- Certificate 244; shared prefix plus independently witnessed suffix. -/
def suffix_244 : List Nat := [2, 1, 4, 3, 2, 3]
def word_244 : List Nat := sharedPrefix ++ suffix_244
theorem suffix_proof_244 : Word suffix_244 263967232452027268200281 5872562025681392777039 := by
  unfold suffix_244
  exact Word.cons
        (show ExactStep 263967232452027268200281 197975424339020451150211 2 from by
          refine ⟨by norm_num, ⟨131983616226013634100140, by norm_num⟩, by norm_num, ⟨98987712169510225575105, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 197975424339020451150211 296963136508530676725317 1 from by
          refine ⟨by norm_num, ⟨98987712169510225575105, by norm_num⟩, by norm_num, ⟨148481568254265338362658, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 296963136508530676725317 55680588095349501885997 4 from by
          refine ⟨by norm_num, ⟨148481568254265338362658, by norm_num⟩, by norm_num, ⟨27840294047674750942998, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 55680588095349501885997 20880220535756063207249 3 from by
          refine ⟨by norm_num, ⟨27840294047674750942998, by norm_num⟩, by norm_num, ⟨10440110267878031603624, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 20880220535756063207249 15660165401817047405437 2 from by
          refine ⟨by norm_num, ⟨10440110267878031603624, by norm_num⟩, by norm_num, ⟨7830082700908523702718, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 15660165401817047405437 5872562025681392777039 3 from by
          refine ⟨by norm_num, ⟨7830082700908523702718, by norm_num⟩, by norm_num, ⟨2936281012840696388519, by norm_num⟩⟩)
        (Word.nil 5872562025681392777039))))))
theorem full_word_244 : Word word_244 6258057927124106346523 5872562025681392777039 := by
  unfold word_244
  have hp := shared_prefix_all 10856
  have ht := suffix_proof_244
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_244 : word_244.length = 46 := by decide
theorem word_sum_244 : word_244.sum = 73 := by decide
theorem infinite_family_244 (d : Nat) :
    ∃ z : Nat, Word word_244 (6258057927124106346523 + 2^74*d) z ∧
      z < 6258057927124106346523 + 2^74*d := by
  have h := word_uniform_descent full_word_244
    (show 5872562025681392777039 < 6258057927124106346523 by norm_num)
    (show 3^word_244.length < 2^word_244.sum by norm_num [word_244, sharedPrefix, suffix_244]) d
  simpa [word_sum_244] using h

/-- Certificate 245; shared prefix plus independently witnessed suffix. -/
def suffix_245 : List Nat := [2, 1, 4, 3, 2, 4]
def word_245 : List Nat := sharedPrefix ++ suffix_245
theorem suffix_proof_245 : Word suffix_245 1459114377739159597053785 16230688192319448032413 := by
  unfold suffix_245
  exact Word.cons
        (show ExactStep 1459114377739159597053785 1094335783304369697790339 2 from by
          refine ⟨by norm_num, ⟨729557188869579798526892, by norm_num⟩, by norm_num, ⟨547167891652184848895169, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1094335783304369697790339 1641503674956554546685509 1 from by
          refine ⟨by norm_num, ⟨547167891652184848895169, by norm_num⟩, by norm_num, ⟨820751837478277273342754, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1641503674956554546685509 307781939054353977503533 4 from by
          refine ⟨by norm_num, ⟨820751837478277273342754, by norm_num⟩, by norm_num, ⟨153890969527176988751766, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 307781939054353977503533 115418227145382741563825 3 from by
          refine ⟨by norm_num, ⟨153890969527176988751766, by norm_num⟩, by norm_num, ⟨57709113572691370781912, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 115418227145382741563825 86563670359037056172869 2 from by
          refine ⟨by norm_num, ⟨57709113572691370781912, by norm_num⟩, by norm_num, ⟨43281835179518528086434, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 86563670359037056172869 16230688192319448032413 4 from by
          refine ⟨by norm_num, ⟨43281835179518528086434, by norm_num⟩, by norm_num, ⟨8115344096159724016206, by norm_num⟩⟩)
        (Word.nil 16230688192319448032413))))))
theorem full_word_245 : Word word_245 34592256824341977628699 16230688192319448032413 := by
  unfold word_245
  have hp := shared_prefix_all 60008
  have ht := suffix_proof_245
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_245 : word_245.length = 46 := by decide
theorem word_sum_245 : word_245.sum = 74 := by decide
theorem infinite_family_245 (d : Nat) :
    ∃ z : Nat, Word word_245 (34592256824341977628699 + 2^75*d) z ∧
      z < 34592256824341977628699 + 2^75*d := by
  have h := word_uniform_descent full_word_245
    (show 16230688192319448032413 < 34592256824341977628699 by norm_num)
    (show 3^word_245.length < 2^word_245.sum by norm_num [word_245, sharedPrefix, suffix_245]) d
  simpa [word_sum_245] using h

/-- Certificate 246; shared prefix plus independently witnessed suffix. -/
def suffix_246 : List Nat := [2, 1, 4, 3, 1, 5]
def word_246 : List Nat := sharedPrefix ++ suffix_246
theorem suffix_proof_246 : Word suffix_246 89674940430987136909145 997513299166711773785 := by
  unfold suffix_246
  exact Word.cons
        (show ExactStep 89674940430987136909145 67256205323240352681859 2 from by
          refine ⟨by norm_num, ⟨44837470215493568454572, by norm_num⟩, by norm_num, ⟨33628102661620176340929, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 67256205323240352681859 100884307984860529022789 1 from by
          refine ⟨by norm_num, ⟨33628102661620176340929, by norm_num⟩, by norm_num, ⟨50442153992430264511394, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 100884307984860529022789 18915807747161349191773 4 from by
          refine ⟨by norm_num, ⟨50442153992430264511394, by norm_num⟩, by norm_num, ⟨9457903873580674595886, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 18915807747161349191773 7093427905185505946915 3 from by
          refine ⟨by norm_num, ⟨9457903873580674595886, by norm_num⟩, by norm_num, ⟨3546713952592752973457, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 7093427905185505946915 10640141857778258920373 1 from by
          refine ⟨by norm_num, ⟨3546713952592752973457, by norm_num⟩, by norm_num, ⟨5320070928889129460186, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 10640141857778258920373 997513299166711773785 5 from by
          refine ⟨by norm_num, ⟨5320070928889129460186, by norm_num⟩, by norm_num, ⟨498756649583355886892, by norm_num⟩⟩)
        (Word.nil 997513299166711773785))))))
theorem full_word_246 : Word word_246 2125987254613166784539 997513299166711773785 := by
  unfold word_246
  have hp := shared_prefix_all 3688
  have ht := suffix_proof_246
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_246 : word_246.length = 46 := by decide
theorem word_sum_246 : word_246.sum = 74 := by decide
theorem infinite_family_246 (d : Nat) :
    ∃ z : Nat, Word word_246 (2125987254613166784539 + 2^75*d) z ∧
      z < 2125987254613166784539 + 2^75*d := by
  have h := word_uniform_descent full_word_246
    (show 997513299166711773785 < 2125987254613166784539 by norm_num)
    (show 3^word_246.length < 2^word_246.sum by norm_num [word_246, sharedPrefix, suffix_246]) d
  simpa [word_sum_246] using h

/-- Certificate 247; shared prefix plus independently witnessed suffix. -/
def suffix_247 : List Nat := [2, 1, 4, 3, 1, 4]
def word_247 : List Nat := sharedPrefix ++ suffix_247
theorem suffix_proof_247 : Word suffix_247 488057322193364579860313 10857964717985924643499 := by
  unfold suffix_247
  exact Word.cons
        (show ExactStep 488057322193364579860313 366042991645023434895235 2 from by
          refine ⟨by norm_num, ⟨244028661096682289930156, by norm_num⟩, by norm_num, ⟨183021495822511717447617, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 366042991645023434895235 549064487467535152342853 1 from by
          refine ⟨by norm_num, ⟨183021495822511717447617, by norm_num⟩, by norm_num, ⟨274532243733767576171426, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 549064487467535152342853 102949591400162841064285 4 from by
          refine ⟨by norm_num, ⟨274532243733767576171426, by norm_num⟩, by norm_num, ⟨51474795700081420532142, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 102949591400162841064285 38606096775061065399107 3 from by
          refine ⟨by norm_num, ⟨51474795700081420532142, by norm_num⟩, by norm_num, ⟨19303048387530532699553, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 38606096775061065399107 57909145162591598098661 1 from by
          refine ⟨by norm_num, ⟨19303048387530532699553, by norm_num⟩, by norm_num, ⟨28954572581295799049330, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 57909145162591598098661 10857964717985924643499 4 from by
          refine ⟨by norm_num, ⟨28954572581295799049330, by norm_num⟩, by norm_num, ⟨5428982358992962321749, by norm_num⟩⟩)
        (Word.nil 10857964717985924643499))))))
theorem full_word_247 : Word word_247 11570720220352457211931 10857964717985924643499 := by
  unfold word_247
  have hp := shared_prefix_all 20072
  have ht := suffix_proof_247
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_247 : word_247.length = 46 := by decide
theorem word_sum_247 : word_247.sum = 73 := by decide
theorem infinite_family_247 (d : Nat) :
    ∃ z : Nat, Word word_247 (11570720220352457211931 + 2^74*d) z ∧
      z < 11570720220352457211931 + 2^74*d := by
  have h := word_uniform_descent full_word_247
    (show 10857964717985924643499 < 11570720220352457211931 by norm_num)
    (show 3^word_247.length < 2^word_247.sum by norm_num [word_247, sharedPrefix, suffix_247]) d
  simpa [word_sum_247] using h

/-- Certificate 248; shared prefix plus independently witnessed suffix. -/
def suffix_248 : List Nat := [2, 1, 4, 2, 2, 4]
def word_248 : List Nat := sharedPrefix ++ suffix_248
theorem suffix_proof_248 : Word suffix_248 257742507736990120654169 5734078617561822447415 := by
  unfold suffix_248
  exact Word.cons
        (show ExactStep 257742507736990120654169 193306880802742590490627 2 from by
          refine ⟨by norm_num, ⟨128871253868495060327084, by norm_num⟩, by norm_num, ⟨96653440401371295245313, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 193306880802742590490627 289960321204113885735941 1 from by
          refine ⟨by norm_num, ⟨96653440401371295245313, by norm_num⟩, by norm_num, ⟨144980160602056942867970, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 289960321204113885735941 54367560225771353575489 4 from by
          refine ⟨by norm_num, ⟨144980160602056942867970, by norm_num⟩, by norm_num, ⟨27183780112885676787744, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 54367560225771353575489 40775670169328515181617 2 from by
          refine ⟨by norm_num, ⟨27183780112885676787744, by norm_num⟩, by norm_num, ⟨20387835084664257590808, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 40775670169328515181617 30581752626996386386213 2 from by
          refine ⟨by norm_num, ⟨20387835084664257590808, by norm_num⟩, by norm_num, ⟨15290876313498193193106, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 30581752626996386386213 5734078617561822447415 4 from by
          refine ⟨by norm_num, ⟨15290876313498193193106, by norm_num⟩, by norm_num, ⟨2867039308780911223707, by norm_num⟩⟩)
        (Word.nil 5734078617561822447415))))))
theorem full_word_248 : Word word_248 6110483974534429933595 5734078617561822447415 := by
  unfold word_248
  have hp := shared_prefix_all 10600
  have ht := suffix_proof_248
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_248 : word_248.length = 46 := by decide
theorem word_sum_248 : word_248.sum = 73 := by decide
theorem infinite_family_248 (d : Nat) :
    ∃ z : Nat, Word word_248 (6110483974534429933595 + 2^74*d) z ∧
      z < 6110483974534429933595 + 2^74*d := by
  have h := word_uniform_descent full_word_248
    (show 5734078617561822447415 < 6110483974534429933595 by norm_num)
    (show 3^word_248.length < 2^word_248.sum by norm_num [word_248, sharedPrefix, suffix_248]) d
  simpa [word_sum_248] using h

/-- Certificate 249; shared prefix plus independently witnessed suffix. -/
def suffix_249 : List Nat := [2, 1, 4, 2, 2, 5]
def word_249 : List Nat := sharedPrefix ++ suffix_249
theorem suffix_proof_249 : Word suffix_249 1452889653024122449507673 16161446488259662867601 := by
  unfold suffix_249
  exact Word.cons
        (show ExactStep 1452889653024122449507673 1089667239768091837130755 2 from by
          refine ⟨by norm_num, ⟨726444826512061224753836, by norm_num⟩, by norm_num, ⟨544833619884045918565377, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1089667239768091837130755 1634500859652137755696133 1 from by
          refine ⟨by norm_num, ⟨544833619884045918565377, by norm_num⟩, by norm_num, ⟨817250429826068877848066, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 1634500859652137755696133 306468911184775829193025 4 from by
          refine ⟨by norm_num, ⟨817250429826068877848066, by norm_num⟩, by norm_num, ⟨153234455592387914596512, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 306468911184775829193025 229851683388581871894769 2 from by
          refine ⟨by norm_num, ⟨153234455592387914596512, by norm_num⟩, by norm_num, ⟨114925841694290935947384, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 229851683388581871894769 172388762541436403921077 2 from by
          refine ⟨by norm_num, ⟨114925841694290935947384, by norm_num⟩, by norm_num, ⟨86194381270718201960538, by norm_num⟩⟩)
        (Word.cons
        (show ExactStep 172388762541436403921077 16161446488259662867601 5 from by
          refine ⟨by norm_num, ⟨86194381270718201960538, by norm_num⟩, by norm_num, ⟨8080723244129831433800, by norm_num⟩⟩)
        (Word.nil 16161446488259662867601))))))
theorem full_word_249 : Word word_249 34444682871752301215771 16161446488259662867601 := by
  unfold word_249
  have hp := shared_prefix_all 59752
  have ht := suffix_proof_249
  have h := word_append hp ht
  convert h using 1 <;> norm_num

theorem word_length_249 : word_249.length = 46 := by decide
theorem word_sum_249 : word_249.sum = 74 := by decide
theorem infinite_family_249 (d : Nat) :
    ∃ z : Nat, Word word_249 (34444682871752301215771 + 2^75*d) z ∧
      z < 34444682871752301215771 + 2^75*d := by
  have h := word_uniform_descent full_word_249
    (show 16161446488259662867601 < 34444682871752301215771 by norm_num)
    (show 3^word_249.length < 2^word_249.sum by norm_num [word_249, sharedPrefix, suffix_249]) d
  simpa [word_sum_249] using h

#print axioms shared_prefix_all
#print axioms infinite_family_0
#print axioms infinite_family_1
#print axioms infinite_family_2
#print axioms infinite_family_3
#print axioms infinite_family_4
#print axioms infinite_family_5
#print axioms infinite_family_6
#print axioms infinite_family_7
#print axioms infinite_family_8
#print axioms infinite_family_9
#print axioms infinite_family_10
#print axioms infinite_family_11
#print axioms infinite_family_12
#print axioms infinite_family_13
#print axioms infinite_family_14
#print axioms infinite_family_15
#print axioms infinite_family_16
#print axioms infinite_family_17
#print axioms infinite_family_18
#print axioms infinite_family_19
#print axioms infinite_family_20
#print axioms infinite_family_21
#print axioms infinite_family_22
#print axioms infinite_family_23
#print axioms infinite_family_24
#print axioms infinite_family_25
#print axioms infinite_family_26
#print axioms infinite_family_27
#print axioms infinite_family_28
#print axioms infinite_family_29
#print axioms infinite_family_30
#print axioms infinite_family_31
#print axioms infinite_family_32
#print axioms infinite_family_33
#print axioms infinite_family_34
#print axioms infinite_family_35
#print axioms infinite_family_36
#print axioms infinite_family_37
#print axioms infinite_family_38
#print axioms infinite_family_39
#print axioms infinite_family_40
#print axioms infinite_family_41
#print axioms infinite_family_42
#print axioms infinite_family_43
#print axioms infinite_family_44
#print axioms infinite_family_45
#print axioms infinite_family_46
#print axioms infinite_family_47
#print axioms infinite_family_48
#print axioms infinite_family_49
#print axioms infinite_family_50
#print axioms infinite_family_51
#print axioms infinite_family_52
#print axioms infinite_family_53
#print axioms infinite_family_54
#print axioms infinite_family_55
#print axioms infinite_family_56
#print axioms infinite_family_57
#print axioms infinite_family_58
#print axioms infinite_family_59
#print axioms infinite_family_60
#print axioms infinite_family_61
#print axioms infinite_family_62
#print axioms infinite_family_63
#print axioms infinite_family_64
#print axioms infinite_family_65
#print axioms infinite_family_66
#print axioms infinite_family_67
#print axioms infinite_family_68
#print axioms infinite_family_69
#print axioms infinite_family_70
#print axioms infinite_family_71
#print axioms infinite_family_72
#print axioms infinite_family_73
#print axioms infinite_family_74
#print axioms infinite_family_75
#print axioms infinite_family_76
#print axioms infinite_family_77
#print axioms infinite_family_78
#print axioms infinite_family_79
#print axioms infinite_family_80
#print axioms infinite_family_81
#print axioms infinite_family_82
#print axioms infinite_family_83
#print axioms infinite_family_84
#print axioms infinite_family_85
#print axioms infinite_family_86
#print axioms infinite_family_87
#print axioms infinite_family_88
#print axioms infinite_family_89
#print axioms infinite_family_90
#print axioms infinite_family_91
#print axioms infinite_family_92
#print axioms infinite_family_93
#print axioms infinite_family_94
#print axioms infinite_family_95
#print axioms infinite_family_96
#print axioms infinite_family_97
#print axioms infinite_family_98
#print axioms infinite_family_99
#print axioms infinite_family_100
#print axioms infinite_family_101
#print axioms infinite_family_102
#print axioms infinite_family_103
#print axioms infinite_family_104
#print axioms infinite_family_105
#print axioms infinite_family_106
#print axioms infinite_family_107
#print axioms infinite_family_108
#print axioms infinite_family_109
#print axioms infinite_family_110
#print axioms infinite_family_111
#print axioms infinite_family_112
#print axioms infinite_family_113
#print axioms infinite_family_114
#print axioms infinite_family_115
#print axioms infinite_family_116
#print axioms infinite_family_117
#print axioms infinite_family_118
#print axioms infinite_family_119
#print axioms infinite_family_120
#print axioms infinite_family_121
#print axioms infinite_family_122
#print axioms infinite_family_123
#print axioms infinite_family_124
#print axioms infinite_family_125
#print axioms infinite_family_126
#print axioms infinite_family_127
#print axioms infinite_family_128
#print axioms infinite_family_129
#print axioms infinite_family_130
#print axioms infinite_family_131
#print axioms infinite_family_132
#print axioms infinite_family_133
#print axioms infinite_family_134
#print axioms infinite_family_135
#print axioms infinite_family_136
#print axioms infinite_family_137
#print axioms infinite_family_138
#print axioms infinite_family_139
#print axioms infinite_family_140
#print axioms infinite_family_141
#print axioms infinite_family_142
#print axioms infinite_family_143
#print axioms infinite_family_144
#print axioms infinite_family_145
#print axioms infinite_family_146
#print axioms infinite_family_147
#print axioms infinite_family_148
#print axioms infinite_family_149
#print axioms infinite_family_150
#print axioms infinite_family_151
#print axioms infinite_family_152
#print axioms infinite_family_153
#print axioms infinite_family_154
#print axioms infinite_family_155
#print axioms infinite_family_156
#print axioms infinite_family_157
#print axioms infinite_family_158
#print axioms infinite_family_159
#print axioms infinite_family_160
#print axioms infinite_family_161
#print axioms infinite_family_162
#print axioms infinite_family_163
#print axioms infinite_family_164
#print axioms infinite_family_165
#print axioms infinite_family_166
#print axioms infinite_family_167
#print axioms infinite_family_168
#print axioms infinite_family_169
#print axioms infinite_family_170
#print axioms infinite_family_171
#print axioms infinite_family_172
#print axioms infinite_family_173
#print axioms infinite_family_174
#print axioms infinite_family_175
#print axioms infinite_family_176
#print axioms infinite_family_177
#print axioms infinite_family_178
#print axioms infinite_family_179
#print axioms infinite_family_180
#print axioms infinite_family_181
#print axioms infinite_family_182
#print axioms infinite_family_183
#print axioms infinite_family_184
#print axioms infinite_family_185
#print axioms infinite_family_186
#print axioms infinite_family_187
#print axioms infinite_family_188
#print axioms infinite_family_189
#print axioms infinite_family_190
#print axioms infinite_family_191
#print axioms infinite_family_192
#print axioms infinite_family_193
#print axioms infinite_family_194
#print axioms infinite_family_195
#print axioms infinite_family_196
#print axioms infinite_family_197
#print axioms infinite_family_198
#print axioms infinite_family_199
#print axioms infinite_family_200
#print axioms infinite_family_201
#print axioms infinite_family_202
#print axioms infinite_family_203
#print axioms infinite_family_204
#print axioms infinite_family_205
#print axioms infinite_family_206
#print axioms infinite_family_207
#print axioms infinite_family_208
#print axioms infinite_family_209
#print axioms infinite_family_210
#print axioms infinite_family_211
#print axioms infinite_family_212
#print axioms infinite_family_213
#print axioms infinite_family_214
#print axioms infinite_family_215
#print axioms infinite_family_216
#print axioms infinite_family_217
#print axioms infinite_family_218
#print axioms infinite_family_219
#print axioms infinite_family_220
#print axioms infinite_family_221
#print axioms infinite_family_222
#print axioms infinite_family_223
#print axioms infinite_family_224
#print axioms infinite_family_225
#print axioms infinite_family_226
#print axioms infinite_family_227
#print axioms infinite_family_228
#print axioms infinite_family_229
#print axioms infinite_family_230
#print axioms infinite_family_231
#print axioms infinite_family_232
#print axioms infinite_family_233
#print axioms infinite_family_234
#print axioms infinite_family_235
#print axioms infinite_family_236
#print axioms infinite_family_237
#print axioms infinite_family_238
#print axioms infinite_family_239
#print axioms infinite_family_240
#print axioms infinite_family_241
#print axioms infinite_family_242
#print axioms infinite_family_243
#print axioms infinite_family_244
#print axioms infinite_family_245
#print axioms infinite_family_246
#print axioms infinite_family_247
#print axioms infinite_family_248
#print axioms infinite_family_249
end CPOQWord
