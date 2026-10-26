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

/-- First actual row of the frozen 18,767-row O5/8 dataset. -/
def certificateWord : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 8]

theorem certificate_word : Word certificateWord 6271892985179388510235 5885544845192602495441 := by
  unfold certificateWord
  exact Word.cons
      (show ExactStep 6271892985179388510235 9407839477769082765353 1 from by
        refine ⟨by norm_num, ⟨3135946492589694255117, by norm_num⟩, by norm_num, ⟨4703919738884541382676, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 9407839477769082765353 7055879608326812074015 2 from by
        refine ⟨by norm_num, ⟨4703919738884541382676, by norm_num⟩, by norm_num, ⟨3527939804163406037007, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 7055879608326812074015 10583819412490218111023 1 from by
        refine ⟨by norm_num, ⟨3527939804163406037007, by norm_num⟩, by norm_num, ⟨5291909706245109055511, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 10583819412490218111023 15875729118735327166535 1 from by
        refine ⟨by norm_num, ⟨5291909706245109055511, by norm_num⟩, by norm_num, ⟨7937864559367663583267, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 15875729118735327166535 23813593678102990749803 1 from by
        refine ⟨by norm_num, ⟨7937864559367663583267, by norm_num⟩, by norm_num, ⟨11906796839051495374901, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 23813593678102990749803 35720390517154486124705 1 from by
        refine ⟨by norm_num, ⟨11906796839051495374901, by norm_num⟩, by norm_num, ⟨17860195258577243062352, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 35720390517154486124705 26790292887865864593529 2 from by
        refine ⟨by norm_num, ⟨17860195258577243062352, by norm_num⟩, by norm_num, ⟨13395146443932932296764, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 26790292887865864593529 20092719665899398445147 2 from by
        refine ⟨by norm_num, ⟨13395146443932932296764, by norm_num⟩, by norm_num, ⟨10046359832949699222573, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 20092719665899398445147 30139079498849097667721 1 from by
        refine ⟨by norm_num, ⟨10046359832949699222573, by norm_num⟩, by norm_num, ⟨15069539749424548833860, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 30139079498849097667721 22604309624136823250791 2 from by
        refine ⟨by norm_num, ⟨15069539749424548833860, by norm_num⟩, by norm_num, ⟨11302154812068411625395, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 22604309624136823250791 33906464436205234876187 1 from by
        refine ⟨by norm_num, ⟨11302154812068411625395, by norm_num⟩, by norm_num, ⟨16953232218102617438093, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 33906464436205234876187 50859696654307852314281 1 from by
        refine ⟨by norm_num, ⟨16953232218102617438093, by norm_num⟩, by norm_num, ⟨25429848327153926157140, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 50859696654307852314281 38144772490730889235711 2 from by
        refine ⟨by norm_num, ⟨25429848327153926157140, by norm_num⟩, by norm_num, ⟨19072386245365444617855, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 38144772490730889235711 57217158736096333853567 1 from by
        refine ⟨by norm_num, ⟨19072386245365444617855, by norm_num⟩, by norm_num, ⟨28608579368048166926783, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 57217158736096333853567 85825738104144500780351 1 from by
        refine ⟨by norm_num, ⟨28608579368048166926783, by norm_num⟩, by norm_num, ⟨42912869052072250390175, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 85825738104144500780351 128738607156216751170527 1 from by
        refine ⟨by norm_num, ⟨42912869052072250390175, by norm_num⟩, by norm_num, ⟨64369303578108375585263, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 128738607156216751170527 193107910734325126755791 1 from by
        refine ⟨by norm_num, ⟨64369303578108375585263, by norm_num⟩, by norm_num, ⟨96553955367162563377895, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 193107910734325126755791 289661866101487690133687 1 from by
        refine ⟨by norm_num, ⟨96553955367162563377895, by norm_num⟩, by norm_num, ⟨144830933050743845066843, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 289661866101487690133687 434492799152231535200531 1 from by
        refine ⟨by norm_num, ⟨144830933050743845066843, by norm_num⟩, by norm_num, ⟨217246399576115767600265, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 434492799152231535200531 651739198728347302800797 1 from by
        refine ⟨by norm_num, ⟨217246399576115767600265, by norm_num⟩, by norm_num, ⟨325869599364173651400398, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 651739198728347302800797 244402199523130238550299 3 from by
        refine ⟨by norm_num, ⟨325869599364173651400398, by norm_num⟩, by norm_num, ⟨122201099761565119275149, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 244402199523130238550299 366603299284695357825449 1 from by
        refine ⟨by norm_num, ⟨122201099761565119275149, by norm_num⟩, by norm_num, ⟨183301649642347678912724, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 366603299284695357825449 274952474463521518369087 2 from by
        refine ⟨by norm_num, ⟨183301649642347678912724, by norm_num⟩, by norm_num, ⟨137476237231760759184543, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 274952474463521518369087 412428711695282277553631 1 from by
        refine ⟨by norm_num, ⟨137476237231760759184543, by norm_num⟩, by norm_num, ⟨206214355847641138776815, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 412428711695282277553631 618643067542923416330447 1 from by
        refine ⟨by norm_num, ⟨206214355847641138776815, by norm_num⟩, by norm_num, ⟨309321533771461708165223, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 618643067542923416330447 927964601314385124495671 1 from by
        refine ⟨by norm_num, ⟨309321533771461708165223, by norm_num⟩, by norm_num, ⟨463982300657192562247835, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 927964601314385124495671 1391946901971577686743507 1 from by
        refine ⟨by norm_num, ⟨463982300657192562247835, by norm_num⟩, by norm_num, ⟨695973450985788843371753, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 1391946901971577686743507 2087920352957366530115261 1 from by
        refine ⟨by norm_num, ⟨695973450985788843371753, by norm_num⟩, by norm_num, ⟨1043960176478683265057630, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 2087920352957366530115261 782970132359012448793223 3 from by
        refine ⟨by norm_num, ⟨1043960176478683265057630, by norm_num⟩, by norm_num, ⟨391485066179506224396611, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 782970132359012448793223 1174455198538518673189835 1 from by
        refine ⟨by norm_num, ⟨391485066179506224396611, by norm_num⟩, by norm_num, ⟨587227599269259336594917, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 1174455198538518673189835 1761682797807778009784753 1 from by
        refine ⟨by norm_num, ⟨587227599269259336594917, by norm_num⟩, by norm_num, ⟨880841398903889004892376, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 1761682797807778009784753 1321262098355833507338565 2 from by
        refine ⟨by norm_num, ⟨880841398903889004892376, by norm_num⟩, by norm_num, ⟨660631049177916753669282, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 1321262098355833507338565 247736643441718782625981 4 from by
        refine ⟨by norm_num, ⟨660631049177916753669282, by norm_num⟩, by norm_num, ⟨123868321720859391312990, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 247736643441718782625981 92901241290644543484743 3 from by
        refine ⟨by norm_num, ⟨123868321720859391312990, by norm_num⟩, by norm_num, ⟨46450620645322271742371, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 92901241290644543484743 139351861935966815227115 1 from by
        refine ⟨by norm_num, ⟨46450620645322271742371, by norm_num⟩, by norm_num, ⟨69675930967983407613557, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 139351861935966815227115 209027792903950222840673 1 from by
        refine ⟨by norm_num, ⟨69675930967983407613557, by norm_num⟩, by norm_num, ⟨104513896451975111420336, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 209027792903950222840673 156770844677962667130505 2 from by
        refine ⟨by norm_num, ⟨104513896451975111420336, by norm_num⟩, by norm_num, ⟨78385422338981333565252, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 156770844677962667130505 117578133508472000347879 2 from by
        refine ⟨by norm_num, ⟨78385422338981333565252, by norm_num⟩, by norm_num, ⟨58789066754236000173939, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 117578133508472000347879 176367200262708000521819 1 from by
        refine ⟨by norm_num, ⟨58789066754236000173939, by norm_num⟩, by norm_num, ⟨88183600131354000260909, by norm_num⟩⟩)
      (Word.cons
      (show ExactStep 176367200262708000521819 264550800394062000782729 1 from by
        refine ⟨by norm_num, ⟨88183600131354000260909, by norm_num⟩, by norm_num, ⟨132275400197031000391364, by norm_num⟩⟩)
      (Word.cons
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
      (Word.nil 5885544845192602495441))))))))))))))))))))))))))))))))))))))))))))))

theorem certificate_word_length : certificateWord.length = 46 := by
  decide

theorem certificate_word_sum : certificateWord.sum = 73 := by
  decide

theorem certificate_base_descent : 5885544845192602495441 < 6271892985179388510235 := by
  norm_num

theorem certificate_slope : 3^certificateWord.length < 2^certificateWord.sum := by
  norm_num [certificateWord]

/-- Actual certified cylinder: q = 10880 + 2^15 * d. -/
theorem certificate_infinite_family (d : Nat) :
    ∃ z : Nat,
      Word certificateWord
        (6271892985179388510235 + 2^74 * d) z ∧
      z < 6271892985179388510235 + 2^74 * d := by
  have h := word_uniform_descent certificate_word
    certificate_base_descent certificate_slope d
  simpa [certificate_word_sum] using h

#print axioms certificate_word
#print axioms certificate_infinite_family
end CPOQWord
