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
end CPOQWord
