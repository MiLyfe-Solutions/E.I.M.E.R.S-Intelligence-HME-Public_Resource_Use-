import V185TrunkScan23Chunk0805

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4767098 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_4767098 : Nat := 118140960795 + 4767098 * 2 ^ 59
def prefixEnd_4767098 : Nat := 4983230072969 + 3 ^ 40 * 4767098 * 2
def baseEnd_4767098 : Nat := 2447812601087094940851521

theorem tailTrace_4767098 : CollatzResearch.WordTrace tailWord_4767098 prefixEnd_4767098 2447812601087094940851521 := by
  unfold tailWord_4767098
  simp only [CollatzResearch.WordTrace]
  refine ⟨43467587020906394091319487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115913565389083717576851965 43467587020906394091319487)
  ·
    refine ⟨65201380531359591136979231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43467587020906394091319487 65201380531359591136979231)
    ·
      refine ⟨97802070797039386705468847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65201380531359591136979231 97802070797039386705468847)
      ·
        refine ⟨146703106195559080058203271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97802070797039386705468847 146703106195559080058203271)
        ·
          refine ⟨220054659293338620087304907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146703106195559080058203271 220054659293338620087304907)
          ·
            refine ⟨330081988940007930130957361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220054659293338620087304907 330081988940007930130957361)
            ·
              refine ⟨247561491705005947598218021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330081988940007930130957361 247561491705005947598218021)
              ·
                refine ⟨46417779694688615174665879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247561491705005947598218021 46417779694688615174665879)
                ·
                  refine ⟨69626669542032922761998819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46417779694688615174665879 69626669542032922761998819)
                  ·
                    refine ⟨104440004313049384142998229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69626669542032922761998819 104440004313049384142998229)
                    ·
                      refine ⟨2447812601087094940851521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104440004313049384142998229 2447812601087094940851521)
                      ·
                        rfl

theorem cell23_4767098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_4767098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767098 prefixEnd_4767098 := by exact prefixLift 4767098
  have htrace : WordTrace (prefixWord ++ tailWord_4767098) baseStart_4767098 baseEnd_4767098 := by
    simpa [prefixWord, tailWord_4767098, baseEnd_4767098] using wordTrace_append hprefix tailTrace_4767098
  have hstable : (prefixWord ++ tailWord_4767098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767098).length < 2 ^ (prefixWord ++ tailWord_4767098).sum := by decide
  have hdescent : baseEnd_4767098 < baseStart_4767098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767125 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_4767125 : Nat := 118140960795 + 4767125 * 2 ^ 59
def prefixEnd_4767125 : Nat := 4983230072969 + 3 ^ 40 * 4767125 * 2
def baseEnd_4767125 : Nat := 2447826465064766335213897

theorem tailTrace_4767125 : CollatzResearch.WordTrace tailWord_4767125 prefixEnd_4767125 2447826465064766335213897 := by
  unfold tailWord_4767125
  simp only [CollatzResearch.WordTrace]
  refine ⟨173871332854527759976510829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115914221903018506651007219 173871332854527759976510829)
  ·
    refine ⟨65201749820447909991191561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173871332854527759976510829 65201749820447909991191561)
    ·
      refine ⟨48901312365335932493393671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65201749820447909991191561 48901312365335932493393671)
      ·
        refine ⟨73351968548003898740090507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48901312365335932493393671 73351968548003898740090507)
        ·
          refine ⟨110027952822005848110135761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73351968548003898740090507 110027952822005848110135761)
          ·
            refine ⟨82520964616504386082601821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110027952822005848110135761 82520964616504386082601821)
            ·
              refine ⟨30945361731189144780975683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82520964616504386082601821 30945361731189144780975683)
              ·
                refine ⟨46418042596783717171463525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30945361731189144780975683 46418042596783717171463525)
                ·
                  refine ⟨8703382986896946969649411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46418042596783717171463525 8703382986896946969649411)
                  ·
                    refine ⟨13055074480345420454474117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8703382986896946969649411 13055074480345420454474117)
                    ·
                      refine ⟨2447826465064766335213897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13055074480345420454474117 2447826465064766335213897)
                      ·
                        rfl

theorem cell23_4767125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_4767125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767125 prefixEnd_4767125 := by exact prefixLift 4767125
  have htrace : WordTrace (prefixWord ++ tailWord_4767125) baseStart_4767125 baseEnd_4767125 := by
    simpa [prefixWord, tailWord_4767125, baseEnd_4767125] using wordTrace_append hprefix tailTrace_4767125
  have hstable : (prefixWord ++ tailWord_4767125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767125).length < 2 ^ (prefixWord ++ tailWord_4767125).sum := by decide
  have hdescent : baseEnd_4767125 < baseStart_4767125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767213 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_4767213 : Nat := 118140960795 + 4767213 * 2 ^ 59
def prefixEnd_4767213 : Nat := 4983230072969 + 3 ^ 40 * 4767213 * 2
def baseEnd_4767213 : Nat := 2447871651362361990913493

theorem tailTrace_4767213 : CollatzResearch.WordTrace tailWord_4767213 prefixEnd_4767213 2447871651362361990913493 := by
  unfold tailWord_4767213
  simp only [CollatzResearch.WordTrace]
  refine ⟨173874542478208951005714293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115916361652139300670476195 173874542478208951005714293)
  ·
    refine ⟨16300738357332089156785715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173874542478208951005714293 16300738357332089156785715)
    ·
      refine ⟨24451107535998133735178573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16300738357332089156785715 24451107535998133735178573)
      ·
        refine ⟨9169165325999300150691965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24451107535998133735178573 9169165325999300150691965)
        ·
          refine ⟨3438436997249737556509487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9169165325999300150691965 3438436997249737556509487)
          ·
            refine ⟨5157655495874606334764231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3438436997249737556509487 5157655495874606334764231)
            ·
              refine ⟨7736483243811909502146347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5157655495874606334764231 7736483243811909502146347)
              ·
                refine ⟨11604724865717864253219521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7736483243811909502146347 11604724865717864253219521)
                ·
                  refine ⟨8703543649288398189914641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11604724865717864253219521 8703543649288398189914641)
                  ·
                    refine ⟨6527657736966298642435981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8703543649288398189914641 6527657736966298642435981)
                    ·
                      refine ⟨2447871651362361990913493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6527657736966298642435981 2447871651362361990913493)
                      ·
                        rfl

theorem cell23_4767213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_4767213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767213 prefixEnd_4767213 := by exact prefixLift 4767213
  have htrace : WordTrace (prefixWord ++ tailWord_4767213) baseStart_4767213 baseEnd_4767213 := by
    simpa [prefixWord, tailWord_4767213, baseEnd_4767213] using wordTrace_append hprefix tailTrace_4767213
  have hstable : (prefixWord ++ tailWord_4767213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767213).length < 2 ^ (prefixWord ++ tailWord_4767213).sum := by decide
  have hdescent : baseEnd_4767213 < baseStart_4767213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767226 : List Nat := [3, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3]
def baseStart_4767226 : Nat := 118140960795 + 4767226 * 2 ^ 59
def prefixEnd_4767226 : Nat := 4983230072969 + 3 ^ 40 * 4767226 * 2
def baseEnd_4767226 : Nat := 2447878326610870440050933

theorem tailTrace_4767226 : CollatzResearch.WordTrace tailWord_4767226 prefixEnd_4767226 2447878326610870440050933 := by
  unfold tailWord_4767226
  simp only [CollatzResearch.WordTrace]
  refine ⟨43468754156790463556484383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115916677751441236150625021 43468754156790463556484383)
  ·
    refine ⟨65203131235185695334726575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43468754156790463556484383 65203131235185695334726575)
    ·
      refine ⟨97804696852778543002089863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65203131235185695334726575 97804696852778543002089863)
      ·
        refine ⟨146707045279167814503134795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97804696852778543002089863 146707045279167814503134795)
        ·
          refine ⟨220060567918751721754702193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146707045279167814503134795 220060567918751721754702193)
          ·
            refine ⟨165045425939063791316026645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220060567918751721754702193 165045425939063791316026645)
            ·
              refine ⟨7736504340893615217938749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 165045425939063791316026645 7736504340893615217938749)
              ·
                refine ⟨2901189127835105706727031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7736504340893615217938749 2901189127835105706727031)
                ·
                  refine ⟨4351783691752658560090547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2901189127835105706727031 4351783691752658560090547)
                  ·
                    refine ⟨6527675537628987840135821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4351783691752658560090547 6527675537628987840135821)
                    ·
                      refine ⟨2447878326610870440050933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6527675537628987840135821 2447878326610870440050933)
                      ·
                        rfl

theorem cell23_4767226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3].length) (baseStart_4767226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767226 prefixEnd_4767226 := by exact prefixLift 4767226
  have htrace : WordTrace (prefixWord ++ tailWord_4767226) baseStart_4767226 baseEnd_4767226 := by
    simpa [prefixWord, tailWord_4767226, baseEnd_4767226] using wordTrace_append hprefix tailTrace_4767226
  have hstable : (prefixWord ++ tailWord_4767226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767226).length < 2 ^ (prefixWord ++ tailWord_4767226).sum := by decide
  have hdescent : baseEnd_4767226 < baseStart_4767226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767229 : List Nat := [1, 4, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_4767229 : Nat := 118140960795 + 4767229 * 2 ^ 59
def prefixEnd_4767229 : Nat := 4983230072969 + 3 ^ 40 * 4767229 * 2
def baseEnd_4767229 : Nat := 815959955684277976104473

theorem tailTrace_4767229 : CollatzResearch.WordTrace tailWord_4767229 prefixEnd_4767229 815959955684277976104473 := by
  unfold tailWord_4767229
  simp only [CollatzResearch.WordTrace]
  refine ⟨173875126046150985738296741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115916750697433990492197827 173875126046150985738296741)
  ·
    refine ⟨32601586133653309825930639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173875126046150985738296741 32601586133653309825930639)
    ·
      refine ⟨48902379200479964738895959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32601586133653309825930639 48902379200479964738895959)
      ·
        refine ⟨73353568800719947108343939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48902379200479964738895959 73353568800719947108343939)
        ·
          refine ⟨110030353201079920662515909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73353568800719947108343939 110030353201079920662515909)
          ·
            refine ⟨20630691225202485124221733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110030353201079920662515909 20630691225202485124221733)
            ·
              refine ⟨3868254604725465960791575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20630691225202485124221733 3868254604725465960791575)
              ·
                refine ⟨5802381907088198941187363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3868254604725465960791575 5802381907088198941187363)
                ·
                  refine ⟨8703572860632298411781045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5802381907088198941187363 8703572860632298411781045)
                  ·
                    refine ⟨815959955684277976104473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8703572860632298411781045 815959955684277976104473)
                    ·
                      rfl

theorem cell23_4767229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_4767229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767229 prefixEnd_4767229 := by exact prefixLift 4767229
  have htrace : WordTrace (prefixWord ++ tailWord_4767229) baseStart_4767229 baseEnd_4767229 := by
    simpa [prefixWord, tailWord_4767229, baseEnd_4767229] using wordTrace_append hprefix tailTrace_4767229
  have hstable : (prefixWord ++ tailWord_4767229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767229).length < 2 ^ (prefixWord ++ tailWord_4767229).sum := by decide
  have hdescent : baseEnd_4767229 < baseStart_4767229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767266 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_4767266 : Nat := 118140960795 + 4767266 * 2 ^ 59
def prefixEnd_4767266 : Nat := 4983230072969 + 3 ^ 40 * 4767266 * 2
def baseEnd_4767266 : Nat := 2447898865837050283550749

theorem tailTrace_4767266 : CollatzResearch.WordTrace tailWord_4767266 prefixEnd_4767266 2447898865837050283550749 := by
  unfold tailWord_4767266
  simp only [CollatzResearch.WordTrace]
  refine ⟨43469118886754235264348413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115917650364677960704929101 43469118886754235264348413)
  ·
    refine ⟨16300919582532838224130655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43469118886754235264348413 16300919582532838224130655)
    ·
      refine ⟨24451379373799257336195983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16300919582532838224130655 24451379373799257336195983)
      ·
        refine ⟨36677069060698886004293975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24451379373799257336195983 36677069060698886004293975)
        ·
          refine ⟨55015603591048329006440963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36677069060698886004293975 55015603591048329006440963)
          ·
            refine ⟨82523405386572493509661445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55015603591048329006440963 82523405386572493509661445)
            ·
              refine ⟨15473138509982342533061521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82523405386572493509661445 15473138509982342533061521)
              ·
                refine ⟨11604853882486756899796141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15473138509982342533061521 11604853882486756899796141)
                ·
                  refine ⟨4351820205932533837423553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11604853882486756899796141 4351820205932533837423553)
                  ·
                    refine ⟨3263865154449400378067665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4351820205932533837423553 3263865154449400378067665)
                    ·
                      refine ⟨2447898865837050283550749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3263865154449400378067665 2447898865837050283550749)
                      ·
                        rfl

theorem cell23_4767266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_4767266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767266 prefixEnd_4767266 := by exact prefixLift 4767266
  have htrace : WordTrace (prefixWord ++ tailWord_4767266) baseStart_4767266 baseEnd_4767266 := by
    simpa [prefixWord, tailWord_4767266, baseEnd_4767266] using wordTrace_append hprefix tailTrace_4767266
  have hstable : (prefixWord ++ tailWord_4767266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767266).length < 2 ^ (prefixWord ++ tailWord_4767266).sum := by decide
  have hdescent : baseEnd_4767266 < baseStart_4767266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767282 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_4767282 : Nat := 118140960795 + 4767282 * 2 ^ 59
def prefixEnd_4767282 : Nat := 4983230072969 + 3 ^ 40 * 4767282 * 2
def baseEnd_4767282 : Nat := 2447907081527522220950675

theorem tailTrace_4767282 : CollatzResearch.WordTrace tailWord_4767282 prefixEnd_4767282 2447907081527522220950675 := by
  unfold tailWord_4767282
  simp only [CollatzResearch.WordTrace]
  refine ⟨43469264778739743947494025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115918039409972650526650733 43469264778739743947494025)
  ·
    refine ⟨32601948584054807960620519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43469264778739743947494025 32601948584054807960620519)
    ·
      refine ⟨48902922876082211940930779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32601948584054807960620519 48902922876082211940930779)
      ·
        refine ⟨73354384314123317911396169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48902922876082211940930779 73354384314123317911396169)
        ·
          refine ⟨55015788235592488433547127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73354384314123317911396169 55015788235592488433547127)
          ·
            refine ⟨82523682353388732650320691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55015788235592488433547127 82523682353388732650320691)
            ·
              refine ⟨123785523530083098975481037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82523682353388732650320691 123785523530083098975481037)
              ·
                refine ⟨46419571323781162115805389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123785523530083098975481037 46419571323781162115805389)
                ·
                  refine ⟨17407339246417935793427021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46419571323781162115805389 17407339246417935793427021)
                  ·
                    refine ⟨6527752217406725922535133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17407339246417935793427021 6527752217406725922535133)
                    ·
                      refine ⟨2447907081527522220950675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6527752217406725922535133 2447907081527522220950675)
                      ·
                        rfl

theorem cell23_4767282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_4767282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767282 prefixEnd_4767282 := by exact prefixLift 4767282
  have htrace : WordTrace (prefixWord ++ tailWord_4767282) baseStart_4767282 baseEnd_4767282 := by
    simpa [prefixWord, tailWord_4767282, baseEnd_4767282] using wordTrace_append hprefix tailTrace_4767282
  have hstable : (prefixWord ++ tailWord_4767282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767282).length < 2 ^ (prefixWord ++ tailWord_4767282).sum := by decide
  have hdescent : baseEnd_4767282 < baseStart_4767282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767283 : List Nat := [1, 1, 1, 2, 4, 3, 3, 3, 1, 2, 2]
def baseStart_4767283 : Nat := 118140960795 + 4767283 * 2 ^ 59
def prefixEnd_4767283 : Nat := 4983230072969 + 3 ^ 40 * 4767283 * 2
def baseEnd_4767283 : Nat := 2447907595008176717038171

theorem tailTrace_4767283 : CollatzResearch.WordTrace tailWord_4767283 prefixEnd_4767283 2447907595008176717038171 := by
  unfold tailWord_4767283
  simp only [CollatzResearch.WordTrace]
  refine ⟨173877095587955352960762503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115918063725303568640508335 173877095587955352960762503)
  ·
    refine ⟨260815643381933029441143755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173877095587955352960762503 260815643381933029441143755)
    ·
      refine ⟨391223465072899544161715633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260815643381933029441143755 391223465072899544161715633)
      ·
        refine ⟨293417598804674658121286725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391223465072899544161715633 293417598804674658121286725)
        ·
          refine ⟨55015799775876498397741261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 293417598804674658121286725 55015799775876498397741261)
          ·
            refine ⟨20630924915953686899152973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55015799775876498397741261 20630924915953686899152973)
            ·
              refine ⟨7736596843482632587182365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20630924915953686899152973 7736596843482632587182365)
              ·
                refine ⟨2901223816305987220193387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7736596843482632587182365 2901223816305987220193387)
                ·
                  refine ⟨4351835724458980830290081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2901223816305987220193387 4351835724458980830290081)
                  ·
                    refine ⟨3263876793344235622717561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4351835724458980830290081 3263876793344235622717561)
                    ·
                      refine ⟨2447907595008176717038171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3263876793344235622717561 2447907595008176717038171)
                      ·
                        rfl

theorem cell23_4767283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 1, 2, 2].length) (baseStart_4767283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767283 prefixEnd_4767283 := by exact prefixLift 4767283
  have htrace : WordTrace (prefixWord ++ tailWord_4767283) baseStart_4767283 baseEnd_4767283 := by
    simpa [prefixWord, tailWord_4767283, baseEnd_4767283] using wordTrace_append hprefix tailTrace_4767283
  have hstable : (prefixWord ++ tailWord_4767283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767283).length < 2 ^ (prefixWord ++ tailWord_4767283).sum := by decide
  have hdescent : baseEnd_4767283 < baseStart_4767283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767286 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_4767286 : Nat := 118140960795 + 4767286 * 2 ^ 59
def prefixEnd_4767286 : Nat := 4983230072969 + 3 ^ 40 * 4767286 * 2
def baseEnd_4767286 : Nat := 2447909135450140205300657

theorem tailTrace_4767286 : CollatzResearch.WordTrace tailWord_4767286 prefixEnd_4767286 2447909135450140205300657 := by
  unfold tailWord_4767286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10867325312934030279570107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115918136671296322982081141 10867325312934030279570107)
  ·
    refine ⟨16300987969401045419355161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10867325312934030279570107 16300987969401045419355161)
    ·
      refine ⟨12225740977050784064516371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16300987969401045419355161 12225740977050784064516371)
      ·
        refine ⟨18338611465576176096774557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12225740977050784064516371 18338611465576176096774557)
        ·
          refine ⟨6876979299591066036290459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18338611465576176096774557 6876979299591066036290459)
          ·
            refine ⟨10315468949386599054435689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6876979299591066036290459 10315468949386599054435689)
            ·
              refine ⟨7736601712039949290826767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10315468949386599054435689 7736601712039949290826767)
              ·
                refine ⟨11604902568059923936240151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7736601712039949290826767 11604902568059923936240151)
                ·
                  refine ⟨17407353852089885904360227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11604902568059923936240151 17407353852089885904360227)
                  ·
                    refine ⟨26111030778134828856540341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17407353852089885904360227 26111030778134828856540341)
                    ·
                      refine ⟨2447909135450140205300657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26111030778134828856540341 2447909135450140205300657)
                      ·
                        rfl

theorem cell23_4767286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_4767286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767286 prefixEnd_4767286 := by exact prefixLift 4767286
  have htrace : WordTrace (prefixWord ++ tailWord_4767286) baseStart_4767286 baseEnd_4767286 := by
    simpa [prefixWord, tailWord_4767286, baseEnd_4767286] using wordTrace_append hprefix tailTrace_4767286
  have hstable : (prefixWord ++ tailWord_4767286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767286).length < 2 ^ (prefixWord ++ tailWord_4767286).sum := by decide
  have hdescent : baseEnd_4767286 < baseStart_4767286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767316 : List Nat := [2, 4, 1, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_4767316 : Nat := 118140960795 + 4767316 * 2 ^ 59
def prefixEnd_4767316 : Nat := 4983230072969 + 3 ^ 40 * 4767316 * 2
def baseEnd_4767316 : Nat := 2447924539869775087925519

theorem tailTrace_4767316 : CollatzResearch.WordTrace tailWord_4767316 prefixEnd_4767316 2447924539869775087925519 := by
  unfold tailWord_4767316
  simp only [CollatzResearch.WordTrace]
  refine ⟨86939149598417899798356901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115918866131223866397809201 86939149598417899798356901)
  ·
    refine ⟨16301090549703356212191919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86939149598417899798356901 16301090549703356212191919)
    ·
      refine ⟨24451635824555034318287879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16301090549703356212191919 24451635824555034318287879)
      ·
        refine ⟨36677453736832551477431819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24451635824555034318287879 36677453736832551477431819)
        ·
          refine ⟨55016180605248827216147729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36677453736832551477431819 55016180605248827216147729)
          ·
            refine ⟨41262135453936620412110797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55016180605248827216147729 41262135453936620412110797)
            ·
              refine ⟨15473300795226232654541549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41262135453936620412110797 15473300795226232654541549)
              ·
                refine ⟨5802487798209837245453081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15473300795226232654541549 5802487798209837245453081)
                ·
                  refine ⟨4351865848657377934089811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5802487798209837245453081 4351865848657377934089811)
                  ·
                    refine ⟨6527798772986066901134717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4351865848657377934089811 6527798772986066901134717)
                    ·
                      refine ⟨2447924539869775087925519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6527798772986066901134717 2447924539869775087925519)
                      ·
                        rfl

theorem cell23_4767316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_4767316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767316 prefixEnd_4767316 := by exact prefixLift 4767316
  have htrace : WordTrace (prefixWord ++ tailWord_4767316) baseStart_4767316 baseEnd_4767316 := by
    simpa [prefixWord, tailWord_4767316, baseEnd_4767316] using wordTrace_append hprefix tailTrace_4767316
  have hstable : (prefixWord ++ tailWord_4767316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767316).length < 2 ^ (prefixWord ++ tailWord_4767316).sum := by decide
  have hdescent : baseEnd_4767316 < baseStart_4767316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767394 : List Nat := [3, 3, 1, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_4767394 : Nat := 118140960795 + 4767394 * 2 ^ 59
def prefixEnd_4767394 : Nat := 4983230072969 + 3 ^ 40 * 4767394 * 2
def baseEnd_4767394 : Nat := 2447964591360825782750161

theorem tailTrace_4767394 : CollatzResearch.WordTrace tailWord_4767394 prefixEnd_4767394 2447964591360825782750161 := by
  unfold tailWord_4767394
  simp only [CollatzResearch.WordTrace]
  refine ⟨43470286022638304729513309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115920762727035479278702157 43470286022638304729513309)
  ·
    refine ⟨16301357258489364273567491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43470286022638304729513309 16301357258489364273567491)
    ·
      refine ⟨24452035887734046410351237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16301357258489364273567491 24452035887734046410351237)
      ·
        refine ⟨4584756728950133701940857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24452035887734046410351237 4584756728950133701940857)
        ·
          refine ⟨3438567546712600276455643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4584756728950133701940857 3438567546712600276455643)
          ·
            refine ⟨5157851320068900414683465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3438567546712600276455643 5157851320068900414683465)
            ·
              refine ⟨3868388490051675311012599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5157851320068900414683465 3868388490051675311012599)
              ·
                refine ⟨5802582735077512966518899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3868388490051675311012599 5802582735077512966518899)
                ·
                  refine ⟨8703874102616269449778349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5802582735077512966518899 8703874102616269449778349)
                  ·
                    refine ⟨3263952788481101043666881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8703874102616269449778349 3263952788481101043666881)
                    ·
                      refine ⟨2447964591360825782750161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3263952788481101043666881 2447964591360825782750161)
                      ·
                        rfl

theorem cell23_4767394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_4767394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767394 prefixEnd_4767394 := by exact prefixLift 4767394
  have htrace : WordTrace (prefixWord ++ tailWord_4767394) baseStart_4767394 baseEnd_4767394 := by
    simpa [prefixWord, tailWord_4767394, baseEnd_4767394] using wordTrace_append hprefix tailTrace_4767394
  have hstable : (prefixWord ++ tailWord_4767394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767394).length < 2 ^ (prefixWord ++ tailWord_4767394).sum := by decide
  have hdescent : baseEnd_4767394 < baseStart_4767394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767396 : List Nat := [2, 3, 1, 2, 2, 3, 2, 3, 5]
def baseStart_4767396 : Nat := 118140960795 + 4767396 * 2 ^ 59
def prefixEnd_4767396 : Nat := 4983230072969 + 3 ^ 40 * 4767396 * 2
def baseEnd_4767396 : Nat := 271996179813570530547239

theorem tailTrace_4767396 : CollatzResearch.WordTrace tailWord_4767396 prefixEnd_4767396 271996179813570530547239 := by
  unfold tailWord_4767396
  simp only [CollatzResearch.WordTrace]
  refine ⟨86940608518272986629813021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115920811357697315506417361 86940608518272986629813021)
  ·
    refine ⟨32602728194352369986179883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86940608518272986629813021 32602728194352369986179883)
    ·
      refine ⟨48904092291528554979269825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32602728194352369986179883 48904092291528554979269825)
      ·
        refine ⟨36678069218646416234452369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48904092291528554979269825 36678069218646416234452369)
        ·
          refine ⟨27508551913984812175839277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36678069218646416234452369 27508551913984812175839277)
          ·
            refine ⟨10315706967744304565939729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27508551913984812175839277 10315706967744304565939729)
            ·
              refine ⟨7736780225808228424454797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10315706967744304565939729 7736780225808228424454797)
              ·
                refine ⟨2901292584678085659170549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7736780225808228424454797 2901292584678085659170549)
                ·
                  refine ⟨271996179813570530547239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2901292584678085659170549 271996179813570530547239)
                  ·
                    rfl

theorem cell23_4767396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_4767396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767396 prefixEnd_4767396 := by exact prefixLift 4767396
  have htrace : WordTrace (prefixWord ++ tailWord_4767396) baseStart_4767396 baseEnd_4767396 := by
    simpa [prefixWord, tailWord_4767396, baseEnd_4767396] using wordTrace_append hprefix tailTrace_4767396
  have hstable : (prefixWord ++ tailWord_4767396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767396).length < 2 ^ (prefixWord ++ tailWord_4767396).sum := by decide
  have hdescent : baseEnd_4767396 < baseStart_4767396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767449 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 1, 4, 3]
def baseStart_4767449 : Nat := 118140960795 + 4767449 * 2 ^ 59
def prefixEnd_4767449 : Nat := 4983230072969 + 3 ^ 40 * 4767449 * 2
def baseEnd_4767449 : Nat := 2447992832796823067562407

theorem tailTrace_4767449 : CollatzResearch.WordTrace tailWord_4767449 prefixEnd_4767449 2447992832796823067562407 := by
  unfold tailWord_4767449
  simp only [CollatzResearch.WordTrace]
  refine ⟨173883150105353963311305401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115922100070235975540870267 173883150105353963311305401)
  ·
    refine ⟨130412362579015472483479051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173883150105353963311305401 130412362579015472483479051)
    ·
      refine ⟨195618543868523208725218577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130412362579015472483479051 195618543868523208725218577)
      ·
        refine ⟨146713907901392406543913933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195618543868523208725218577 146713907901392406543913933)
        ·
          refine ⟨55017715463022152453967725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146713907901392406543913933 55017715463022152453967725)
          ·
            refine ⟨20631643298633307170237897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55017715463022152453967725 20631643298633307170237897)
            ·
              refine ⟨15473732473974980377678423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20631643298633307170237897 15473732473974980377678423)
              ·
                refine ⟨23210598710962470566517635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15473732473974980377678423 23210598710962470566517635)
                ·
                  refine ⟨34815898066443705849776453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23210598710962470566517635 34815898066443705849776453)
                  ·
                    refine ⟨6527980887458194846833085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34815898066443705849776453 6527980887458194846833085)
                    ·
                      refine ⟨2447992832796823067562407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6527980887458194846833085 2447992832796823067562407)
                      ·
                        rfl

theorem cell23_4767449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_4767449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767449 prefixEnd_4767449 := by exact prefixLift 4767449
  have htrace : WordTrace (prefixWord ++ tailWord_4767449) baseStart_4767449 baseEnd_4767449 := by
    simpa [prefixWord, tailWord_4767449, baseEnd_4767449] using wordTrace_append hprefix tailTrace_4767449
  have hstable : (prefixWord ++ tailWord_4767449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767449).length < 2 ^ (prefixWord ++ tailWord_4767449).sum := by decide
  have hdescent : baseEnd_4767449 < baseStart_4767449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767463 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4767463 : Nat := 118140960795 + 4767463 * 2 ^ 59
def prefixEnd_4767463 : Nat := 4983230072969 + 3 ^ 40 * 4767463 * 2
def baseEnd_4767463 : Nat := 2448000021525986012787343

theorem tailTrace_4767463 : CollatzResearch.WordTrace tailWord_4767463 prefixEnd_4767463 2448000021525986012787343 := by
  unfold tailWord_4767463
  simp only [CollatzResearch.WordTrace]
  refine ⟨173883660727303243702315043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115922440484868829134876695 173883660727303243702315043)
  ·
    refine ⟨260825491090954865553472565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173883660727303243702315043 260825491090954865553472565)
    ·
      refine ⟨24452389789777018645638053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260825491090954865553472565 24452389789777018645638053)
      ·
        refine ⟨4584823085583190996057135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24452389789777018645638053 4584823085583190996057135)
        ·
          refine ⟨6877234628374786494085703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4584823085583190996057135 6877234628374786494085703)
          ·
            refine ⟨10315851942562179741128555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6877234628374786494085703 10315851942562179741128555)
            ·
              refine ⟨15473777913843269611692833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10315851942562179741128555 15473777913843269611692833)
              ·
                refine ⟨11605333435382452208769625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15473777913843269611692833 11605333435382452208769625)
                ·
                  refine ⟨8704000076536839156577219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11605333435382452208769625 8704000076536839156577219)
                  ·
                    refine ⟨13056000114805258734865829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8704000076536839156577219 13056000114805258734865829)
                    ·
                      refine ⟨2448000021525986012787343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13056000114805258734865829 2448000021525986012787343)
                      ·
                        rfl

theorem cell23_4767463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4767463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767463 prefixEnd_4767463 := by exact prefixLift 4767463
  have htrace : WordTrace (prefixWord ++ tailWord_4767463) baseStart_4767463 baseEnd_4767463 := by
    simpa [prefixWord, tailWord_4767463, baseEnd_4767463] using wordTrace_append hprefix tailTrace_4767463
  have hstable : (prefixWord ++ tailWord_4767463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767463).length < 2 ^ (prefixWord ++ tailWord_4767463).sum := by decide
  have hdescent : baseEnd_4767463 < baseStart_4767463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767469 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 8]
def baseStart_4767469 : Nat := 118140960795 + 4767469 * 2 ^ 59
def prefixEnd_4767469 : Nat := 4983230072969 + 3 ^ 40 * 4767469 * 2
def baseEnd_4767469 : Nat := 272000344712212554368035

theorem tailTrace_4767469 : CollatzResearch.WordTrace tailWord_4767469 prefixEnd_4767469 272000344712212554368035 := by
  unfold tailWord_4767469
  simp only [CollatzResearch.WordTrace]
  refine ⟨173883879565281506727033461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115922586376854337818022307 173883879565281506727033461)
  ·
    refine ⟨16301613709245141255659387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173883879565281506727033461 16301613709245141255659387)
    ·
      refine ⟨24452420563867711883489081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16301613709245141255659387 24452420563867711883489081)
      ·
        refine ⟨18339315422900783912616811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24452420563867711883489081 18339315422900783912616811)
        ·
          refine ⟨27508973134351175868925217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18339315422900783912616811 27508973134351175868925217)
          ·
            refine ⟨20631729850763381901693913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27508973134351175868925217 20631729850763381901693913)
            ·
              refine ⟨15473797388072536426270435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20631729850763381901693913 15473797388072536426270435)
              ·
                refine ⟨23210696082108804639405653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15473797388072536426270435 23210696082108804639405653)
                ·
                  refine ⟨272000344712212554368035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23210696082108804639405653 272000344712212554368035)
                  ·
                    rfl

theorem cell23_4767469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_4767469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767469 prefixEnd_4767469 := by exact prefixLift 4767469
  have htrace : WordTrace (prefixWord ++ tailWord_4767469) baseStart_4767469 baseEnd_4767469 := by
    simpa [prefixWord, tailWord_4767469, baseEnd_4767469] using wordTrace_append hprefix tailTrace_4767469
  have hstable : (prefixWord ++ tailWord_4767469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767469).length < 2 ^ (prefixWord ++ tailWord_4767469).sum := by decide
  have hdescent : baseEnd_4767469 < baseStart_4767469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767472 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 6]
def baseStart_4767472 : Nat := 118140960795 + 4767472 * 2 ^ 59
def prefixEnd_4767472 : Nat := 4983230072969 + 3 ^ 40 * 4767472 * 2
def baseEnd_4767472 : Nat := 2448004642851876477574801

theorem tailTrace_4767472 : CollatzResearch.WordTrace tailWord_4767472 prefixEnd_4767472 2448004642851876477574801 := by
  unfold tailWord_4767472
  simp only [CollatzResearch.WordTrace]
  refine ⟨86941994492135319119696335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115922659322847092159595113 86941994492135319119696335)
  ·
    refine ⟨130412991738202978679544503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86941994492135319119696335 130412991738202978679544503)
    ·
      refine ⟨195619487607304468019316755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130412991738202978679544503 195619487607304468019316755)
      ·
        refine ⟨293429231410956702028975133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195619487607304468019316755 293429231410956702028975133)
        ·
          refine ⟨110035961779108763260865675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293429231410956702028975133 110035961779108763260865675)
          ·
            refine ⟨165053942668663144891298513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110035961779108763260865675 165053942668663144891298513)
            ·
              refine ⟨123790457001497358668473885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165053942668663144891298513 123790457001497358668473885)
              ·
                refine ⟨46421421375561509500677707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123790457001497358668473885 46421421375561509500677707)
                ·
                  refine ⟨69632132063342264251016561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46421421375561509500677707 69632132063342264251016561)
                  ·
                    refine ⟨52224099047506698188262421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69632132063342264251016561 52224099047506698188262421)
                    ·
                      refine ⟨2448004642851876477574801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52224099047506698188262421 2448004642851876477574801)
                      ·
                        rfl

theorem cell23_4767472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_4767472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767472 prefixEnd_4767472 := by exact prefixLift 4767472
  have htrace : WordTrace (prefixWord ++ tailWord_4767472) baseStart_4767472 baseEnd_4767472 := by
    simpa [prefixWord, tailWord_4767472, baseEnd_4767472] using wordTrace_append hprefix tailTrace_4767472
  have hstable : (prefixWord ++ tailWord_4767472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767472).length < 2 ^ (prefixWord ++ tailWord_4767472).sum := by decide
  have hdescent : baseEnd_4767472 < baseStart_4767472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767482 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 2, 9]
def baseStart_4767482 : Nat := 118140960795 + 4767482 * 2 ^ 59
def prefixEnd_4767482 : Nat := 4983230072969 + 3 ^ 40 * 4767482 * 2
def baseEnd_4767482 : Nat := 816003259219473812816585

theorem tailTrace_4767482 : CollatzResearch.WordTrace tailWord_4767482 prefixEnd_4767482 816003259219473812816585 := by
  unfold tailWord_4767482
  simp only [CollatzResearch.WordTrace]
  refine ⟨43471088428558602486814175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115922902476156273298171133 43471088428558602486814175)
  ·
    refine ⟨65206632642837903730221263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43471088428558602486814175 65206632642837903730221263)
    ·
      refine ⟨97809948964256855595331895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65206632642837903730221263 97809948964256855595331895)
      ·
        refine ⟨146714923446385283392997843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97809948964256855595331895 146714923446385283392997843)
        ·
          refine ⟨220072385169577925089496765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146714923446385283392997843 220072385169577925089496765)
          ·
            refine ⟨82527144438591721908561287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220072385169577925089496765 82527144438591721908561287)
            ·
              refine ⟨123790716657887582862841931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82527144438591721908561287 123790716657887582862841931)
              ·
                refine ⟨185686074986831374294262897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123790716657887582862841931 185686074986831374294262897)
                ·
                  refine ⟨139264556240123530720697173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185686074986831374294262897 139264556240123530720697173)
                  ·
                    refine ⟨816003259219473812816585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 139264556240123530720697173 816003259219473812816585)
                    ·
                      rfl

theorem cell23_4767482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_4767482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767482 prefixEnd_4767482 := by exact prefixLift 4767482
  have htrace : WordTrace (prefixWord ++ tailWord_4767482) baseStart_4767482 baseEnd_4767482 := by
    simpa [prefixWord, tailWord_4767482, baseEnd_4767482] using wordTrace_append hprefix tailTrace_4767482
  have hstable : (prefixWord ++ tailWord_4767482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767482).length < 2 ^ (prefixWord ++ tailWord_4767482).sum := by decide
  have hdescent : baseEnd_4767482 < baseStart_4767482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767494 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4767494 : Nat := 118140960795 + 4767494 * 2 ^ 59
def prefixEnd_4767494 : Nat := 4983230072969 + 3 ^ 40 * 4767494 * 2
def baseEnd_4767494 : Nat := 816005313142091797166567

theorem tailTrace_4767494 : CollatzResearch.WordTrace tailWord_4767494 prefixEnd_4767494 816005313142091797166567 := by
  unfold tailWord_4767494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5433899730943466749896673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 115923194260127290664462357 5433899730943466749896673)
  ·
    refine ⟨4075424798207600062422505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5433899730943466749896673 4075424798207600062422505)
    ·
      refine ⟨3056568598655700046816879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4075424798207600062422505 3056568598655700046816879)
      ·
        refine ⟨4584852897983550070225319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056568598655700046816879 4584852897983550070225319)
        ·
          refine ⟨6877279346975325105337979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4584852897983550070225319 6877279346975325105337979)
          ·
            refine ⟨10315919020462987658006969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6877279346975325105337979 10315919020462987658006969)
            ·
              refine ⟨7736939265347240743505227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10315919020462987658006969 7736939265347240743505227)
              ·
                refine ⟨11605408898020861115257841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7736939265347240743505227 11605408898020861115257841)
                ·
                  refine ⟨8704056673515645836443381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11605408898020861115257841 8704056673515645836443381)
                  ·
                    refine ⟨816005313142091797166567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8704056673515645836443381 816005313142091797166567)
                    ·
                      rfl

theorem cell23_4767494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4767494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767494 prefixEnd_4767494 := by exact prefixLift 4767494
  have htrace : WordTrace (prefixWord ++ tailWord_4767494) baseStart_4767494 baseEnd_4767494 := by
    simpa [prefixWord, tailWord_4767494, baseEnd_4767494] using wordTrace_append hprefix tailTrace_4767494
  have hstable : (prefixWord ++ tailWord_4767494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767494).length < 2 ^ (prefixWord ++ tailWord_4767494).sum := by decide
  have hdescent : baseEnd_4767494 < baseStart_4767494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767496 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_4767496 : Nat := 118140960795 + 4767496 * 2 ^ 59
def prefixEnd_4767496 : Nat := 4983230072969 + 3 ^ 40 * 4767496 * 2
def baseEnd_4767496 : Nat := 2448016966387584383674691

theorem tailTrace_4767496 : CollatzResearch.WordTrace tailWord_4767496 prefixEnd_4767496 2448016966387584383674691 := by
  unfold tailWord_4767496
  simp only [CollatzResearch.WordTrace]
  refine ⟨86942432168091845169133171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115923242890789126892177561 86942432168091845169133171)
  ·
    refine ⟨130413648252137767753699757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86942432168091845169133171 130413648252137767753699757)
    ·
      refine ⟨48905118094551662907637409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130413648252137767753699757 48905118094551662907637409)
      ·
        refine ⟨36678838570913747180728057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48905118094551662907637409 36678838570913747180728057)
        ·
          refine ⟨27509128928185310385546043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36678838570913747180728057 27509128928185310385546043)
          ·
            refine ⟨41263693392277965578319065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27509128928185310385546043 41263693392277965578319065)
            ·
              refine ⟨30947770044208474183739299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41263693392277965578319065 30947770044208474183739299)
              ·
                refine ⟨46421655066312711275608949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30947770044208474183739299 46421655066312711275608949)
                ·
                  refine ⟨4352030162466816682088339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46421655066312711275608949 4352030162466816682088339)
                  ·
                    refine ⟨6528045243700225023132509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4352030162466816682088339 6528045243700225023132509)
                    ·
                      refine ⟨2448016966387584383674691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6528045243700225023132509 2448016966387584383674691)
                      ·
                        rfl

theorem cell23_4767496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_4767496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767496 prefixEnd_4767496 := by exact prefixLift 4767496
  have htrace : WordTrace (prefixWord ++ tailWord_4767496) baseStart_4767496 baseEnd_4767496 := by
    simpa [prefixWord, tailWord_4767496, baseEnd_4767496] using wordTrace_append hprefix tailTrace_4767496
  have hstable : (prefixWord ++ tailWord_4767496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767496).length < 2 ^ (prefixWord ++ tailWord_4767496).sum := by decide
  have hdescent : baseEnd_4767496 < baseStart_4767496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767546 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 1, 6]
def baseStart_4767546 : Nat := 118140960795 + 4767546 * 2 ^ 59
def prefixEnd_4767546 : Nat := 4983230072969 + 3 ^ 40 * 4767546 * 2
def baseEnd_4767546 : Nat := 816014213473436396016487

theorem tailTrace_4767546 : CollatzResearch.WordTrace tailWord_4767546 prefixEnd_4767546 816014213473436396016487 := by
  unfold tailWord_4767546
  simp only [CollatzResearch.WordTrace]
  refine ⟨43471671996500637219396623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115924458657335032585057661 43471671996500637219396623)
  ·
    refine ⟨65207507994750955829094935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43471671996500637219396623 65207507994750955829094935)
    ·
      refine ⟨97811261992126433743642403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65207507994750955829094935 97811261992126433743642403)
      ·
        refine ⟨146716892988189650615463605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97811261992126433743642403 146716892988189650615463605)
        ·
          refine ⟨13754708717642779745199713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146716892988189650615463605 13754708717642779745199713)
          ·
            refine ⟨10316031538232084808899785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13754708717642779745199713 10316031538232084808899785)
            ·
              refine ⟨7737023653674063606674839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10316031538232084808899785 7737023653674063606674839)
              ·
                refine ⟨11605535480511095410012259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7737023653674063606674839 11605535480511095410012259)
                ·
                  refine ⟨17408303220766643115018389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11605535480511095410012259 17408303220766643115018389)
                  ·
                    refine ⟨816014213473436396016487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17408303220766643115018389 816014213473436396016487)
                    ·
                      rfl

theorem cell23_4767546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_4767546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767546 prefixEnd_4767546 := by exact prefixLift 4767546
  have htrace : WordTrace (prefixWord ++ tailWord_4767546) baseStart_4767546 baseEnd_4767546 := by
    simpa [prefixWord, tailWord_4767546, baseEnd_4767546] using wordTrace_append hprefix tailTrace_4767546
  have hstable : (prefixWord ++ tailWord_4767546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767546).length < 2 ^ (prefixWord ++ tailWord_4767546).sum := by decide
  have hdescent : baseEnd_4767546 < baseStart_4767546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767570 : List Nat := [3, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_4767570 : Nat := 118140960795 + 4767570 * 2 ^ 59
def prefixEnd_4767570 : Nat := 4983230072969 + 3 ^ 40 * 4767570 * 2
def baseEnd_4767570 : Nat := 2448054963956017094149351

theorem tailTrace_4767570 : CollatzResearch.WordTrace tailWord_4767570 prefixEnd_4767570 2448054963956017094149351 := by
  unfold tailWord_4767570
  simp only [CollatzResearch.WordTrace]
  refine ⟨43471890834478900244115041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115925042225277067317640109 43471890834478900244115041)
  ·
    refine ⟨32603918125859175183086281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43471890834478900244115041 32603918125859175183086281)
    ·
      refine ⟨24452938594394381387314711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32603918125859175183086281 24452938594394381387314711)
      ·
        refine ⟨36679407891591572080972067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24452938594394381387314711 36679407891591572080972067)
        ·
          refine ⟨55019111837387358121458101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36679407891591572080972067 55019111837387358121458101)
          ·
            refine ⟨5158041734755064823886697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55019111837387358121458101 5158041734755064823886697)
            ·
              refine ⟨3868531301066298617915023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5158041734755064823886697 3868531301066298617915023)
              ·
                refine ⟨5802796951599447926872535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3868531301066298617915023 5802796951599447926872535)
                ·
                  refine ⟨8704195427399171890308803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5802796951599447926872535 8704195427399171890308803)
                  ·
                    refine ⟨13056293141098757835463205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8704195427399171890308803 13056293141098757835463205)
                    ·
                      refine ⟨2448054963956017094149351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13056293141098757835463205 2448054963956017094149351)
                      ·
                        rfl

theorem cell23_4767570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_4767570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767570 prefixEnd_4767570 := by exact prefixLift 4767570
  have htrace : WordTrace (prefixWord ++ tailWord_4767570) baseStart_4767570 baseEnd_4767570 := by
    simpa [prefixWord, tailWord_4767570, baseEnd_4767570] using wordTrace_append hprefix tailTrace_4767570
  have hstable : (prefixWord ++ tailWord_4767570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767570).length < 2 ^ (prefixWord ++ tailWord_4767570).sum := by decide
  have hdescent : baseEnd_4767570 < baseStart_4767570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767573 : List Nat := [1, 3, 2, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_4767573 : Nat := 118140960795 + 4767573 * 2 ^ 59
def prefixEnd_4767573 : Nat := 4983230072969 + 3 ^ 40 * 4767573 * 2
def baseEnd_4767573 : Nat := 2448056504397980582411837

theorem tailTrace_4767573 : CollatzResearch.WordTrace tailWord_4767573 prefixEnd_4767573 2448056504397980582411837 := by
  unfold tailWord_4767573
  simp only [CollatzResearch.WordTrace]
  refine ⟨173887672756904732488819373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115925115171269821659212915 173887672756904732488819373)
  ·
    refine ⟨65207877283839274683307265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173887672756904732488819373 65207877283839274683307265)
    ·
      refine ⟨48905907962879456012480449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65207877283839274683307265 48905907962879456012480449)
      ·
        refine ⟨36679430972159592009360337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48905907962879456012480449 36679430972159592009360337)
        ·
          refine ⟨27509573229119694007020253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36679430972159592009360337 27509573229119694007020253)
          ·
            refine ⟨10316089960919885252632595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27509573229119694007020253 10316089960919885252632595)
            ·
              refine ⟨15474134941379827878948893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10316089960919885252632595 15474134941379827878948893)
              ·
                refine ⟨5802800603017435454605835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15474134941379827878948893 5802800603017435454605835)
                ·
                  refine ⟨8704200904526153181908753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5802800603017435454605835 8704200904526153181908753)
                  ·
                    refine ⟨6528150678394614886431565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8704200904526153181908753 6528150678394614886431565)
                    ·
                      refine ⟨2448056504397980582411837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6528150678394614886431565 2448056504397980582411837)
                      ·
                        rfl

theorem cell23_4767573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_4767573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767573 prefixEnd_4767573 := by exact prefixLift 4767573
  have htrace : WordTrace (prefixWord ++ tailWord_4767573) baseStart_4767573 baseEnd_4767573 := by
    simpa [prefixWord, tailWord_4767573, baseEnd_4767573] using wordTrace_append hprefix tailTrace_4767573
  have hstable : (prefixWord ++ tailWord_4767573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767573).length < 2 ^ (prefixWord ++ tailWord_4767573).sum := by decide
  have hdescent : baseEnd_4767573 < baseStart_4767573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767638 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_4767638 : Nat := 118140960795 + 4767638 * 2 ^ 59
def prefixEnd_4767638 : Nat := 4983230072969 + 3 ^ 40 * 4767638 * 2
def baseEnd_4767638 : Nat := 2448089880640522828099039

theorem tailTrace_4767638 : CollatzResearch.WordTrace tailWord_4767638 prefixEnd_4767638 2448089880640522828099039 := by
  unfold tailWord_4767638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10868127718854328036870973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115926695667779499059957045 10868127718854328036870973)
  ·
    refine ⟨4075547894570373013826615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10868127718854328036870973 4075547894570373013826615)
    ·
      refine ⟨6113321841855559520739923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4075547894570373013826615 6113321841855559520739923)
      ·
        refine ⟨9169982762783339281109885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6113321841855559520739923 9169982762783339281109885)
        ·
          refine ⟨3438743536043752230416207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9169982762783339281109885 3438743536043752230416207)
          ·
            refine ⟨5158115304065628345624311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3438743536043752230416207 5158115304065628345624311)
            ·
              refine ⟨7737172956098442518436467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5158115304065628345624311 7737172956098442518436467)
              ·
                refine ⟨11605759434147663777654701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7737172956098442518436467 11605759434147663777654701)
                ·
                  refine ⟨4352159787805373916620513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11605759434147663777654701 4352159787805373916620513)
                  ·
                    refine ⟨3264119840854030437465385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4352159787805373916620513 3264119840854030437465385)
                    ·
                      refine ⟨2448089880640522828099039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3264119840854030437465385 2448089880640522828099039)
                      ·
                        rfl

theorem cell23_4767638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_4767638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767638 prefixEnd_4767638 := by exact prefixLift 4767638
  have htrace : WordTrace (prefixWord ++ tailWord_4767638) baseStart_4767638 baseEnd_4767638 := by
    simpa [prefixWord, tailWord_4767638, baseEnd_4767638] using wordTrace_append hprefix tailTrace_4767638
  have hstable : (prefixWord ++ tailWord_4767638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767638).length < 2 ^ (prefixWord ++ tailWord_4767638).sum := by decide
  have hdescent : baseEnd_4767638 < baseStart_4767638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767689 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 7]
def baseStart_4767689 : Nat := 118140960795 + 4767689 * 2 ^ 59
def prefixEnd_4767689 : Nat := 4983230072969 + 3 ^ 40 * 4767689 * 2
def baseEnd_4767689 : Nat := 2448116068153902128561303

theorem tailTrace_4767689 : CollatzResearch.WordTrace tailWord_4767689 prefixEnd_4767689 2448116068153902128561303 := by
  unfold tailWord_4767689
  simp only [CollatzResearch.WordTrace]
  refine ⟨173891903624484484300042121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115927935749656322866694747 173891903624484484300042121)
  ·
    refine ⟨130418927718363363225031591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173891903624484484300042121 130418927718363363225031591)
    ·
      refine ⟨195628391577545044837547387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130418927718363363225031591 195628391577545044837547387)
      ·
        refine ⟨293442587366317567256321081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195628391577545044837547387 293442587366317567256321081)
        ·
          refine ⟨220081940524738175442240811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293442587366317567256321081 220081940524738175442240811)
          ·
            refine ⟨330122910787107263163361217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220081940524738175442240811 330122910787107263163361217)
            ·
              refine ⟨247592183090330447372520913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330122910787107263163361217 247592183090330447372520913)
              ·
                refine ⟨185694137317747835529390685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247592183090330447372520913 185694137317747835529390685)
                ·
                  refine ⟨69635301494155438323521507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185694137317747835529390685 69635301494155438323521507)
                  ·
                    refine ⟨104452952241233157485282261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69635301494155438323521507 104452952241233157485282261)
                    ·
                      refine ⟨2448116068153902128561303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104452952241233157485282261 2448116068153902128561303)
                      ·
                        rfl

theorem cell23_4767689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_4767689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767689 prefixEnd_4767689 := by exact prefixLift 4767689
  have htrace : WordTrace (prefixWord ++ tailWord_4767689) baseStart_4767689 baseEnd_4767689 := by
    simpa [prefixWord, tailWord_4767689, baseEnd_4767689] using wordTrace_append hprefix tailTrace_4767689
  have hstable : (prefixWord ++ tailWord_4767689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767689).length < 2 ^ (prefixWord ++ tailWord_4767689).sum := by decide
  have hdescent : baseEnd_4767689 < baseStart_4767689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767696 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 2, 5]
def baseStart_4767696 : Nat := 118140960795 + 4767696 * 2 ^ 59
def prefixEnd_4767696 : Nat := 4983230072969 + 3 ^ 40 * 4767696 * 2
def baseEnd_4767696 : Nat := 816039887506161200391257

theorem tailTrace_4767696 : CollatzResearch.WordTrace tailWord_4767696 prefixEnd_4767696 816039887506161200391257 := by
  unfold tailWord_4767696
  simp only [CollatzResearch.WordTrace]
  refine ⟨86946079467729562247773471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115928105956972749663697961 86946079467729562247773471)
  ·
    refine ⟨130419119201594343371660207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86946079467729562247773471 130419119201594343371660207)
    ·
      refine ⟨195628678802391515057490311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130419119201594343371660207 195628678802391515057490311)
      ·
        refine ⟨293443018203587272586235467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195628678802391515057490311 293443018203587272586235467)
        ·
          refine ⟨440164527305380908879353201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293443018203587272586235467 440164527305380908879353201)
          ·
            refine ⟨330123395479035681659514901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440164527305380908879353201 330123395479035681659514901)
            ·
              refine ⟨15474534163079797577789761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 330123395479035681659514901 15474534163079797577789761)
              ·
                refine ⟨11605900622309848183342321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15474534163079797577789761 11605900622309848183342321)
                ·
                  refine ⟨8704425466732386137506741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11605900622309848183342321 8704425466732386137506741)
                  ·
                    refine ⟨816039887506161200391257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8704425466732386137506741 816039887506161200391257)
                    ·
                      rfl

theorem cell23_4767696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_4767696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767696 prefixEnd_4767696 := by exact prefixLift 4767696
  have htrace : WordTrace (prefixWord ++ tailWord_4767696) baseStart_4767696 baseEnd_4767696 := by
    simpa [prefixWord, tailWord_4767696, baseEnd_4767696] using wordTrace_append hprefix tailTrace_4767696
  have hstable : (prefixWord ++ tailWord_4767696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767696).length < 2 ^ (prefixWord ++ tailWord_4767696).sum := by decide
  have hdescent : baseEnd_4767696 < baseStart_4767696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767716 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_4767716 : Nat := 118140960795 + 4767716 * 2 ^ 59
def prefixEnd_4767716 : Nat := 4983230072969 + 3 ^ 40 * 4767716 * 2
def baseEnd_4767716 : Nat := 2448129932131573522923679

theorem tailTrace_4767716 : CollatzResearch.WordTrace tailWord_4767716 prefixEnd_4767716 2448129932131573522923679 := by
  unfold tailWord_4767716
  simp only [CollatzResearch.WordTrace]
  refine ⟨86946444197693333955637501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115928592263591111940850001 86946444197693333955637501)
  ·
    refine ⟨32604916574135000233364063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86946444197693333955637501 32604916574135000233364063)
    ·
      refine ⟨48907374861202500350046095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32604916574135000233364063 48907374861202500350046095)
      ·
        refine ⟨73361062291803750525069143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48907374861202500350046095 73361062291803750525069143)
        ·
          refine ⟨110041593437705625787603715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73361062291803750525069143 110041593437705625787603715)
          ·
            refine ⟨165062390156558438681405573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110041593437705625787603715 165062390156558438681405573)
            ·
              refine ⟨30949198154354707252763545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165062390156558438681405573 30949198154354707252763545)
              ·
                refine ⟨23211898615766030439572659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30949198154354707252763545 23211898615766030439572659)
                ·
                  refine ⟨34817847923649045659358989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23211898615766030439572659 34817847923649045659358989)
                  ·
                    refine ⟨13056692971368392122259621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34817847923649045659358989 13056692971368392122259621)
                    ·
                      refine ⟨2448129932131573522923679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13056692971368392122259621 2448129932131573522923679)
                      ·
                        rfl

theorem cell23_4767716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_4767716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767716 prefixEnd_4767716 := by exact prefixLift 4767716
  have htrace : WordTrace (prefixWord ++ tailWord_4767716) baseStart_4767716 baseEnd_4767716 := by
    simpa [prefixWord, tailWord_4767716, baseEnd_4767716] using wordTrace_append hprefix tailTrace_4767716
  have hstable : (prefixWord ++ tailWord_4767716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767716).length < 2 ^ (prefixWord ++ tailWord_4767716).sum := by decide
  have hdescent : baseEnd_4767716 < baseStart_4767716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767756 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 8]
def baseStart_4767756 : Nat := 118140960795 + 4767756 * 2 ^ 59
def prefixEnd_4767756 : Nat := 4983230072969 + 3 ^ 40 * 4767756 * 2
def baseEnd_4767756 : Nat := 272016719039750374047055

theorem tailTrace_4767756 : CollatzResearch.WordTrace tailWord_4767756 prefixEnd_4767756 272016719039750374047055 := by
  unfold tailWord_4767756
  simp only [CollatzResearch.WordTrace]
  refine ⟨86947173657620877371365561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115929564876827836495154081 86947173657620877371365561)
  ·
    refine ⟨65210380243215658028524171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86947173657620877371365561 65210380243215658028524171)
    ·
      refine ⟨97815570364823487042786257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65210380243215658028524171 97815570364823487042786257)
      ·
        refine ⟨73361677773617615282089693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97815570364823487042786257 73361677773617615282089693)
        ·
          refine ⟨27510629165106605730783635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73361677773617615282089693 27510629165106605730783635)
          ·
            refine ⟨41265943747659908596175453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27510629165106605730783635 41265943747659908596175453)
            ·
              refine ⟨15474728905372465723565795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41265943747659908596175453 15474728905372465723565795)
              ·
                refine ⟨23212093358058698585348693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15474728905372465723565795 23212093358058698585348693)
                ·
                  refine ⟨272016719039750374047055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23212093358058698585348693 272016719039750374047055)
                  ·
                    rfl

theorem cell23_4767756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_4767756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767756 prefixEnd_4767756 := by exact prefixLift 4767756
  have htrace : WordTrace (prefixWord ++ tailWord_4767756) baseStart_4767756 baseEnd_4767756 := by
    simpa [prefixWord, tailWord_4767756, baseEnd_4767756] using wordTrace_append hprefix tailTrace_4767756
  have hstable : (prefixWord ++ tailWord_4767756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767756).length < 2 ^ (prefixWord ++ tailWord_4767756).sum := by decide
  have hdescent : baseEnd_4767756 < baseStart_4767756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767816 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 5, 6]
def baseStart_4767816 : Nat := 118140960795 + 4767816 * 2 ^ 59
def prefixEnd_4767816 : Nat := 4983230072969 + 3 ^ 40 * 4767816 * 2
def baseEnd_4767816 : Nat := 816060426732341043891073

theorem tailTrace_4767816 : CollatzResearch.WordTrace tailWord_4767816 prefixEnd_4767816 816060426732341043891073 := by
  unfold tailWord_4767816
  simp only [CollatzResearch.WordTrace]
  refine ⟨86948267847512192494957651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115931023796682923326610201 86948267847512192494957651)
  ·
    refine ⟨130422401771268288742436477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86948267847512192494957651 130422401771268288742436477)
    ·
      refine ⟨48908400664225608278413679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130422401771268288742436477 48908400664225608278413679)
      ·
        refine ⟨73362600996338412417620519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48908400664225608278413679 73362600996338412417620519)
        ·
          refine ⟨110043901494507618626430779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73362600996338412417620519 110043901494507618626430779)
          ·
            refine ⟨165065852241761427939646169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110043901494507618626430779 165065852241761427939646169)
            ·
              refine ⟨123799389181321070954734627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165065852241761427939646169 123799389181321070954734627)
              ·
                refine ⟨185699083771981606432101941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123799389181321070954734627 185699083771981606432101941)
                ·
                  refine ⟨17409289103623275603009557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 185699083771981606432101941 17409289103623275603009557)
                  ·
                    refine ⟨816060426732341043891073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17409289103623275603009557 816060426732341043891073)
                    ·
                      rfl

theorem cell23_4767816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_4767816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767816 prefixEnd_4767816 := by exact prefixLift 4767816
  have htrace : WordTrace (prefixWord ++ tailWord_4767816) baseStart_4767816 baseEnd_4767816 := by
    simpa [prefixWord, tailWord_4767816, baseEnd_4767816] using wordTrace_append hprefix tailTrace_4767816
  have hstable : (prefixWord ++ tailWord_4767816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767816).length < 2 ^ (prefixWord ++ tailWord_4767816).sum := by decide
  have hdescent : baseEnd_4767816 < baseStart_4767816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767837 : List Nat := [1, 4, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_4767837 : Nat := 118140960795 + 4767837 * 2 ^ 59
def prefixEnd_4767837 : Nat := 4983230072969 + 3 ^ 40 * 4767837 * 2
def baseEnd_4767837 : Nat := 816064021096922516503541

theorem tailTrace_4767837 : CollatzResearch.WordTrace tailWord_4767837 prefixEnd_4767837 816064021096922516503541 := by
  unfold tailWord_4767837
  simp only [CollatzResearch.WordTrace]
  refine ⟨173897301627948305576429765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115931534418632203717619843 173897301627948305576429765)
  ·
    refine ⟨32605744055240307295580581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173897301627948305576429765 32605744055240307295580581)
    ·
      refine ⟨6113577010357557617921359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32605744055240307295580581 6113577010357557617921359)
      ·
        refine ⟨9170365515536336426882039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6113577010357557617921359 9170365515536336426882039)
        ·
          refine ⟨13755548273304504640323059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9170365515536336426882039 13755548273304504640323059)
          ·
            refine ⟨20633322409956756960484589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13755548273304504640323059 20633322409956756960484589)
            ·
              refine ⟨7737495903733783860181721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20633322409956756960484589 7737495903733783860181721)
              ·
                refine ⟨5803121927800337895136291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7737495903733783860181721 5803121927800337895136291)
                ·
                  refine ⟨8704682891700506842704437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5803121927800337895136291 8704682891700506842704437)
                  ·
                    refine ⟨816064021096922516503541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8704682891700506842704437 816064021096922516503541)
                    ·
                      rfl

theorem cell23_4767837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_4767837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767837 prefixEnd_4767837 := by exact prefixLift 4767837
  have htrace : WordTrace (prefixWord ++ tailWord_4767837) baseStart_4767837 baseEnd_4767837 := by
    simpa [prefixWord, tailWord_4767837, baseEnd_4767837] using wordTrace_append hprefix tailTrace_4767837
  have hstable : (prefixWord ++ tailWord_4767837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767837).length < 2 ^ (prefixWord ++ tailWord_4767837).sum := by decide
  have hdescent : baseEnd_4767837 < baseStart_4767837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767840 : List Nat := [2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 4]
def baseStart_4767840 : Nat := 118140960795 + 4767840 * 2 ^ 59
def prefixEnd_4767840 : Nat := 4983230072969 + 3 ^ 40 * 4767840 * 2
def baseEnd_4767840 : Nat := 2448193603732731037773109

theorem tailTrace_4767840 : CollatzResearch.WordTrace tailWord_4767840 prefixEnd_4767840 2448193603732731037773109 := by
  unfold tailWord_4767840
  simp only [CollatzResearch.WordTrace]
  refine ⟨86948705523468718544394487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115931607364624958059192649 86948705523468718544394487)
  ·
    refine ⟨130423058285203077816591731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86948705523468718544394487 130423058285203077816591731)
    ·
      refine ⟨195634587427804616724887597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130423058285203077816591731 195634587427804616724887597)
      ·
        refine ⟨73362970285426731271832849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195634587427804616724887597 73362970285426731271832849)
        ·
          refine ⟨55022227714070048453874637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73362970285426731271832849 55022227714070048453874637)
          ·
            refine ⟨20633335392776268170202989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55022227714070048453874637 20633335392776268170202989)
            ·
              refine ⟨7737500772291100563826121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20633335392776268170202989 7737500772291100563826121)
              ·
                refine ⟨5803125579218325422869591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7737500772291100563826121 5803125579218325422869591)
                ·
                  refine ⟨8704688368827488134304387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5803125579218325422869591 8704688368827488134304387)
                  ·
                    refine ⟨13057032553241232201456581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8704688368827488134304387 13057032553241232201456581)
                    ·
                      refine ⟨2448193603732731037773109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13057032553241232201456581 2448193603732731037773109)
                      ·
                        rfl

theorem cell23_4767840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_4767840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767840 prefixEnd_4767840 := by exact prefixLift 4767840
  have htrace : WordTrace (prefixWord ++ tailWord_4767840) baseStart_4767840 baseEnd_4767840 := by
    simpa [prefixWord, tailWord_4767840, baseEnd_4767840] using wordTrace_append hprefix tailTrace_4767840
  have hstable : (prefixWord ++ tailWord_4767840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767840).length < 2 ^ (prefixWord ++ tailWord_4767840).sum := by decide
  have hdescent : baseEnd_4767840 < baseStart_4767840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767850 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 1, 6]
def baseStart_4767850 : Nat := 118140960795 + 4767850 * 2 ^ 59
def prefixEnd_4767850 : Nat := 4983230072969 + 3 ^ 40 * 4767850 * 2
def baseEnd_4767850 : Nat := 816066246179758666216021

theorem tailTrace_4767850 : CollatzResearch.WordTrace tailWord_4767850 prefixEnd_4767850 816066246179758666216021 := by
  unfold tailWord_4767850
  simp only [CollatzResearch.WordTrace]
  refine ⟨43474443944225302199163251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115931850517934139197768669 43474443944225302199163251)
  ·
    refine ⟨65211665916337953298744877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43474443944225302199163251 65211665916337953298744877)
    ·
      refine ⟨24454374718626732487029329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65211665916337953298744877 24454374718626732487029329)
      ·
        refine ⟨18340781038970049365271997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24454374718626732487029329 18340781038970049365271997)
        ·
          refine ⟨6877792889613768511976999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18340781038970049365271997 6877792889613768511976999)
          ·
            refine ⟨10316689334420652767965499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6877792889613768511976999 10316689334420652767965499)
            ·
              refine ⟨15475034001630979151948249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10316689334420652767965499 15475034001630979151948249)
              ·
                refine ⟨11606275501223234363961187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15475034001630979151948249 11606275501223234363961187)
                ·
                  refine ⟨17409413251834851545941781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11606275501223234363961187 17409413251834851545941781)
                  ·
                    refine ⟨816066246179758666216021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17409413251834851545941781 816066246179758666216021)
                    ·
                      rfl

theorem cell23_4767850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_4767850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767850 prefixEnd_4767850 := by exact prefixLift 4767850
  have htrace : WordTrace (prefixWord ++ tailWord_4767850) baseStart_4767850 baseEnd_4767850 := by
    simpa [prefixWord, tailWord_4767850, baseEnd_4767850] using wordTrace_append hprefix tailTrace_4767850
  have hstable : (prefixWord ++ tailWord_4767850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767850).length < 2 ^ (prefixWord ++ tailWord_4767850).sum := by decide
  have hdescent : baseEnd_4767850 < baseStart_4767850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767866 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_4767866 : Nat := 118140960795 + 4767866 * 2 ^ 59
def prefixEnd_4767866 : Nat := 4983230072969 + 3 ^ 40 * 4767866 * 2
def baseEnd_4767866 : Nat := 2448206954229747936047989

theorem tailTrace_4767866 : CollatzResearch.WordTrace tailWord_4767866 prefixEnd_4767866 2448206954229747936047989 := by
  unfold tailWord_4767866
  simp only [CollatzResearch.WordTrace]
  refine ⟨43474589836210810882308863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115932239563228829019490301 43474589836210810882308863)
  ·
    refine ⟨65211884754316216323463295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43474589836210810882308863 65211884754316216323463295)
    ·
      refine ⟨97817827131474324485194943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65211884754316216323463295 97817827131474324485194943)
      ·
        refine ⟨146726740697211486727792415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97817827131474324485194943 146726740697211486727792415)
        ·
          refine ⟨220090111045817230091688623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146726740697211486727792415 220090111045817230091688623)
          ·
            refine ⟨330135166568725845137532935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220090111045817230091688623 330135166568725845137532935)
            ·
              refine ⟨495202749853088767706299403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330135166568725845137532935 495202749853088767706299403)
              ·
                refine ⟨742804124779633151559449105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495202749853088767706299403 742804124779633151559449105)
                ·
                  refine ⟨557103093584724863669586829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 742804124779633151559449105 557103093584724863669586829)
                  ·
                    refine ⟨208913660094271823876095061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 557103093584724863669586829 208913660094271823876095061)
                    ·
                      refine ⟨2448206954229747936047989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 208913660094271823876095061 2448206954229747936047989)
                      ·
                        rfl

theorem cell23_4767866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_4767866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767866 prefixEnd_4767866 := by exact prefixLift 4767866
  have htrace : WordTrace (prefixWord ++ tailWord_4767866) baseStart_4767866 baseEnd_4767866 := by
    simpa [prefixWord, tailWord_4767866, baseEnd_4767866] using wordTrace_append hprefix tailTrace_4767866
  have hstable : (prefixWord ++ tailWord_4767866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767866).length < 2 ^ (prefixWord ++ tailWord_4767866).sum := by decide
  have hdescent : baseEnd_4767866 < baseStart_4767866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767880 : List Nat := [2, 1, 3, 4, 1, 3, 1, 8]
def baseStart_4767880 : Nat := 118140960795 + 4767880 * 2 ^ 59
def prefixEnd_4767880 : Nat := 4983230072969 + 3 ^ 40 * 4767880 * 2
def baseEnd_4767880 : Nat := 90674597887367069676775

theorem tailTrace_4767880 : CollatzResearch.WordTrace tailWord_4767880 prefixEnd_4767880 90674597887367069676775 := by
  unfold tailWord_4767880
  simp only [CollatzResearch.WordTrace]
  refine ⟨86949434983396261960122547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115932579977861682613496729 86949434983396261960122547)
  ·
    refine ⟨130424152475094392940183821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86949434983396261960122547 130424152475094392940183821)
    ·
      refine ⟨48909057178160397352568933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130424152475094392940183821 48909057178160397352568933)
      ·
        refine ⟨9170448220905074503606675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48909057178160397352568933 9170448220905074503606675)
        ·
          refine ⟨13755672331357611755410013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9170448220905074503606675 13755672331357611755410013)
          ·
            refine ⟨5158377124259104408278755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13755672331357611755410013 5158377124259104408278755)
            ·
              refine ⟨7737565686388656612418133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5158377124259104408278755 7737565686388656612418133)
              ·
                refine ⟨90674597887367069676775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7737565686388656612418133 90674597887367069676775)
                ·
                  rfl

theorem cell23_4767880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 8].length) (baseStart_4767880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767880 prefixEnd_4767880 := by exact prefixLift 4767880
  have htrace : WordTrace (prefixWord ++ tailWord_4767880) baseStart_4767880 baseEnd_4767880 := by
    simpa [prefixWord, tailWord_4767880, baseEnd_4767880] using wordTrace_append hprefix tailTrace_4767880
  have hstable : (prefixWord ++ tailWord_4767880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767880).length < 2 ^ (prefixWord ++ tailWord_4767880).sum := by decide
  have hdescent : baseEnd_4767880 < baseStart_4767880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767911 : List Nat := [1, 1, 6, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_4767911 : Nat := 118140960795 + 4767911 * 2 ^ 59
def prefixEnd_4767911 : Nat := 4983230072969 + 3 ^ 40 * 4767911 * 2
def baseEnd_4767911 : Nat := 2448230060859200259985283

theorem tailTrace_4767911 : CollatzResearch.WordTrace tailWord_4767911 prefixEnd_4767911 2448230060859200259985283 := by
  unfold tailWord_4767911
  simp only [CollatzResearch.WordTrace]
  refine ⟨173900000629680216214623587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115933333753120144143082391 173900000629680216214623587)
  ·
    refine ⟨260850000944520324321935381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173900000629680216214623587 260850000944520324321935381)
    ·
      refine ⟨12227343794274390202590721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 260850000944520324321935381 12227343794274390202590721)
      ·
        refine ⟨9170507845705792651943041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12227343794274390202590721 9170507845705792651943041)
        ·
          refine ⟨6877880884279344488957281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9170507845705792651943041 6877880884279344488957281)
          ·
            refine ⟨5158410663209508366717961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6877880884279344488957281 5158410663209508366717961)
            ·
              refine ⟨3868807997407131275038471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5158410663209508366717961 3868807997407131275038471)
              ·
                refine ⟨5803211996110696912557707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3868807997407131275038471 5803211996110696912557707)
                ·
                  refine ⟨8704817994166045368836561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5803211996110696912557707 8704817994166045368836561)
                  ·
                    refine ⟨6528613495624534026627421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8704817994166045368836561 6528613495624534026627421)
                    ·
                      refine ⟨2448230060859200259985283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6528613495624534026627421 2448230060859200259985283)
                      ·
                        rfl

theorem cell23_4767911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_4767911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767911 prefixEnd_4767911 := by exact prefixLift 4767911
  have htrace : WordTrace (prefixWord ++ tailWord_4767911) baseStart_4767911 baseEnd_4767911 := by
    simpa [prefixWord, tailWord_4767911, baseEnd_4767911] using wordTrace_append hprefix tailTrace_4767911
  have hstable : (prefixWord ++ tailWord_4767911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767911).length < 2 ^ (prefixWord ++ tailWord_4767911).sum := by decide
  have hdescent : baseEnd_4767911 < baseStart_4767911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767918 : List Nat := [4, 1, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_4767918 : Nat := 118140960795 + 4767918 * 2 ^ 59
def prefixEnd_4767918 : Nat := 4983230072969 + 3 ^ 40 * 4767918 * 2
def baseEnd_4767918 : Nat := 816077885074593910865917

theorem tailTrace_4767918 : CollatzResearch.WordTrace tailWord_4767918 prefixEnd_4767918 816077885074593910865917 := by
  unfold tailWord_4767918
  simp only [CollatzResearch.WordTrace]
  refine ⟨21737531992581857051266051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115933503960436570940085605 21737531992581857051266051)
  ·
    refine ⟨32606297988872785576899077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21737531992581857051266051 32606297988872785576899077)
    ·
      refine ⟨6113680872913647295668577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32606297988872785576899077 6113680872913647295668577)
      ·
        refine ⟨4585260654685235471751433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6113680872913647295668577 4585260654685235471751433)
        ·
          refine ⟨3438945491013926603813575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4585260654685235471751433 3438945491013926603813575)
          ·
            refine ⟨5158418236520889905720363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3438945491013926603813575 5158418236520889905720363)
            ·
              refine ⟨7737627354781334858580545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5158418236520889905720363 7737627354781334858580545)
              ·
                refine ⟨5803220516086001143935409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7737627354781334858580545 5803220516086001143935409)
                ·
                  refine ⟨4352415387064500857951557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5803220516086001143935409 4352415387064500857951557)
                  ·
                    refine ⟨816077885074593910865917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4352415387064500857951557 816077885074593910865917)
                    ·
                      rfl

theorem cell23_4767918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_4767918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767918 prefixEnd_4767918 := by exact prefixLift 4767918
  have htrace : WordTrace (prefixWord ++ tailWord_4767918) baseStart_4767918 baseEnd_4767918 := by
    simpa [prefixWord, tailWord_4767918, baseEnd_4767918] using wordTrace_append hprefix tailTrace_4767918
  have hstable : (prefixWord ++ tailWord_4767918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767918).length < 2 ^ (prefixWord ++ tailWord_4767918).sum := by decide
  have hdescent : baseEnd_4767918 < baseStart_4767918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767930 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2]
def baseStart_4767930 : Nat := 118140960795 + 4767930 * 2 ^ 59
def prefixEnd_4767930 : Nat := 4983230072969 + 3 ^ 40 * 4767930 * 2
def baseEnd_4767930 : Nat := 2448239816991635685647695

theorem tailTrace_4767930 : CollatzResearch.WordTrace tailWord_4767930 prefixEnd_4767930 2448239816991635685647695 := by
  unfold tailWord_4767930
  simp only [CollatzResearch.WordTrace]
  refine ⟨43475173404152845614891311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115933795744407588306376829 43475173404152845614891311)
  ·
    refine ⟨65212760106229268422336967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43475173404152845614891311 65212760106229268422336967)
    ·
      refine ⟨97819140159343902633505451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65212760106229268422336967 97819140159343902633505451)
      ·
        refine ⟨146728710239015853950258177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97819140159343902633505451 146728710239015853950258177)
        ·
          refine ⟨110046532679261890462693633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146728710239015853950258177 110046532679261890462693633)
          ·
            refine ⟨82534899509446417847020225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110046532679261890462693633 82534899509446417847020225)
            ·
              refine ⟨61901174632084813385265169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82534899509446417847020225 61901174632084813385265169)
              ·
                refine ⟨46425880974063610038948877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61901174632084813385265169 46425880974063610038948877)
                ·
                  refine ⟨17409705365273853764605829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46425880974063610038948877 17409705365273853764605829)
                  ·
                    refine ⟨3264319755988847580863593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17409705365273853764605829 3264319755988847580863593)
                    ·
                      refine ⟨2448239816991635685647695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3264319755988847580863593 2448239816991635685647695)
                      ·
                        rfl

theorem cell23_4767930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2].length) (baseStart_4767930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767930 prefixEnd_4767930 := by exact prefixLift 4767930
  have htrace : WordTrace (prefixWord ++ tailWord_4767930) baseStart_4767930 baseEnd_4767930 := by
    simpa [prefixWord, tailWord_4767930, baseEnd_4767930] using wordTrace_append hprefix tailTrace_4767930
  have hstable : (prefixWord ++ tailWord_4767930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767930).length < 2 ^ (prefixWord ++ tailWord_4767930).sum := by decide
  have hdescent : baseEnd_4767930 < baseStart_4767930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767933 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_4767933 : Nat := 118140960795 + 4767933 * 2 ^ 59
def prefixEnd_4767933 : Nat := 4983230072969 + 3 ^ 40 * 4767933 * 2
def baseEnd_4767933 : Nat := 2448241357433599173910181

theorem tailTrace_4767933 : CollatzResearch.WordTrace tailWord_4767933 prefixEnd_4767933 2448241357433599173910181 := by
  unfold tailWord_4767933
  simp only [CollatzResearch.WordTrace]
  refine ⟨173900803035600513971924453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115933868690400342647949635 173900803035600513971924453)
  ·
    refine ⟨32606400569175096369735835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173900803035600513971924453 32606400569175096369735835)
    ·
      refine ⟨48909600853762644554603753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32606400569175096369735835 48909600853762644554603753)
      ·
        refine ⟨36682200640321983415952815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48909600853762644554603753 36682200640321983415952815)
        ·
          refine ⟨55023300960482975123929223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36682200640321983415952815 55023300960482975123929223)
          ·
            refine ⟨82534951440724462685893835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55023300960482975123929223 82534951440724462685893835)
            ·
              refine ⟨123802427161086694028840753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82534951440724462685893835 123802427161086694028840753)
              ·
                refine ⟨92851820370815020521630565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123802427161086694028840753 92851820370815020521630565)
                ·
                  refine ⟨17409716319527816347805731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92851820370815020521630565 17409716319527816347805731)
                  ·
                    refine ⟨26114574479291724521708597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17409716319527816347805731 26114574479291724521708597)
                    ·
                      refine ⟨2448241357433599173910181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26114574479291724521708597 2448241357433599173910181)
                      ·
                        rfl

theorem cell23_4767933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_4767933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767933 prefixEnd_4767933 := by exact prefixLift 4767933
  have htrace : WordTrace (prefixWord ++ tailWord_4767933) baseStart_4767933 baseEnd_4767933 := by
    simpa [prefixWord, tailWord_4767933, baseEnd_4767933] using wordTrace_append hprefix tailTrace_4767933
  have hstable : (prefixWord ++ tailWord_4767933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767933).length < 2 ^ (prefixWord ++ tailWord_4767933).sum := by decide
  have hdescent : baseEnd_4767933 < baseStart_4767933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767940 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_4767940 : Nat := 118140960795 + 4767940 * 2 ^ 59
def prefixEnd_4767940 : Nat := 4983230072969 + 3 ^ 40 * 4767940 * 2
def baseEnd_4767940 : Nat := 816081650599393548840883

theorem tailTrace_4767940 : CollatzResearch.WordTrace tailWord_4767940 prefixEnd_4767940 816081650599393548840883 := by
  unfold tailWord_4767940
  simp only [CollatzResearch.WordTrace]
  refine ⟨86950529173287577083714637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115934038897716769444952849 86950529173287577083714637)
  ·
    refine ⟨32606448439982841406392989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86950529173287577083714637 32606448439982841406392989)
    ·
      refine ⟨12227418164993565527397371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32606448439982841406392989 12227418164993565527397371)
      ·
        refine ⟨18341127247490348291096057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12227418164993565527397371 18341127247490348291096057)
        ·
          refine ⟨13755845435617761218322043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18341127247490348291096057 13755845435617761218322043)
          ·
            refine ⟨20633768153426641827483065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13755845435617761218322043 20633768153426641827483065)
            ·
              refine ⟨15475326115069981370612299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20633768153426641827483065 15475326115069981370612299)
              ·
                refine ⟨23212989172604972055918449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15475326115069981370612299 23212989172604972055918449)
                ·
                  refine ⟨17409741879453729041938837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23212989172604972055918449 17409741879453729041938837)
                  ·
                    refine ⟨816081650599393548840883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17409741879453729041938837 816081650599393548840883)
                    ·
                      rfl

theorem cell23_4767940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_4767940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767940 prefixEnd_4767940 := by exact prefixLift 4767940
  have htrace : WordTrace (prefixWord ++ tailWord_4767940) baseStart_4767940 baseEnd_4767940 := by
    simpa [prefixWord, tailWord_4767940, baseEnd_4767940] using wordTrace_append hprefix tailTrace_4767940
  have hstable : (prefixWord ++ tailWord_4767940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767940).length < 2 ^ (prefixWord ++ tailWord_4767940).sum := by decide
  have hdescent : baseEnd_4767940 < baseStart_4767940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767953 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 7]
def baseStart_4767953 : Nat := 118140960795 + 4767953 * 2 ^ 59
def prefixEnd_4767953 : Nat := 4983230072969 + 3 ^ 40 * 4767953 * 2
def baseEnd_4767953 : Nat := 272027958560743232851121

theorem tailTrace_4767953 : CollatzResearch.WordTrace tailWord_4767953 prefixEnd_4767953 272027958560743232851121 := by
  unfold tailWord_4767953
  simp only [CollatzResearch.WordTrace]
  refine ⟨173901532495528057387652513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115934354997018704925101675 173901532495528057387652513)
  ·
    refine ⟨130426149371646043040739385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173901532495528057387652513 130426149371646043040739385)
    ·
      refine ⟨97819612028734532280554539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130426149371646043040739385 97819612028734532280554539)
      ·
        refine ⟨146729418043101798420831809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97819612028734532280554539 146729418043101798420831809)
        ·
          refine ⟨110047063532326348815623857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146729418043101798420831809 110047063532326348815623857)
          ·
            refine ⟨82535297649244761611717893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110047063532326348815623857 82535297649244761611717893)
            ·
              refine ⟨15475368309233392802197105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82535297649244761611717893 15475368309233392802197105)
              ·
                refine ⟨11606526231925044601647829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15475368309233392802197105 11606526231925044601647829)
                ·
                  refine ⟨272027958560743232851121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11606526231925044601647829 272027958560743232851121)
                  ·
                    rfl

theorem cell23_4767953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 7].length) (baseStart_4767953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767953 prefixEnd_4767953 := by exact prefixLift 4767953
  have htrace : WordTrace (prefixWord ++ tailWord_4767953) baseStart_4767953 baseEnd_4767953 := by
    simpa [prefixWord, tailWord_4767953, baseEnd_4767953] using wordTrace_append hprefix tailTrace_4767953
  have hstable : (prefixWord ++ tailWord_4767953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767953).length < 2 ^ (prefixWord ++ tailWord_4767953).sum := by decide
  have hdescent : baseEnd_4767953 < baseStart_4767953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767963 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 3]
def baseStart_4767963 : Nat := 118140960795 + 4767963 * 2 ^ 59
def prefixEnd_4767963 : Nat := 4983230072969 + 3 ^ 40 * 4767963 * 2
def baseEnd_4767963 : Nat := 2448256761853234056535043

theorem tailTrace_4767963 : CollatzResearch.WordTrace tailWord_4767963 prefixEnd_4767963 2448256761853234056535043 := by
  unfold tailWord_4767963
  simp only [CollatzResearch.WordTrace]
  refine ⟨173901897225491829095516543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115934598150327886063677695 173901897225491829095516543)
  ·
    refine ⟨260852845838237743643274815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173901897225491829095516543 260852845838237743643274815)
    ·
      refine ⟨391279268757356615464912223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260852845838237743643274815 391279268757356615464912223)
      ·
        refine ⟨586918903136034923197368335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391279268757356615464912223 586918903136034923197368335)
        ·
          refine ⟨880378354704052384796052503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586918903136034923197368335 880378354704052384796052503)
          ·
            refine ⟨1320567532056078577194078755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880378354704052384796052503 1320567532056078577194078755)
            ·
              refine ⟨1980851298084117865791118133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320567532056078577194078755 1980851298084117865791118133)
              ·
                refine ⟨185704809195386049917917325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1980851298084117865791118133 185704809195386049917917325)
                ·
                  refine ⟨69639303448269768719218997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185704809195386049917917325 69639303448269768719218997)
                  ·
                    refine ⟨6528684698275290817426781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69639303448269768719218997 6528684698275290817426781)
                    ·
                      refine ⟨2448256761853234056535043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6528684698275290817426781 2448256761853234056535043)
                      ·
                        rfl

theorem cell23_4767963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 3].length) (baseStart_4767963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767963 prefixEnd_4767963 := by exact prefixLift 4767963
  have htrace : WordTrace (prefixWord ++ tailWord_4767963) baseStart_4767963 baseEnd_4767963 := by
    simpa [prefixWord, tailWord_4767963, baseEnd_4767963] using wordTrace_append hprefix tailTrace_4767963
  have hstable : (prefixWord ++ tailWord_4767963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767963).length < 2 ^ (prefixWord ++ tailWord_4767963).sum := by decide
  have hdescent : baseEnd_4767963 < baseStart_4767963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4767987 : List Nat := [1, 1, 1, 2, 2, 4, 5, 2, 5]
def baseStart_4767987 : Nat := 118140960795 + 4767987 * 2 ^ 59
def prefixEnd_4767987 : Nat := 4983230072969 + 3 ^ 40 * 4767987 * 2
def baseEnd_4767987 : Nat := 272029898376549106959437

theorem tailTrace_4767987 : CollatzResearch.WordTrace tailWord_4767987 prefixEnd_4767987 272029898376549106959437 := by
  unfold tailWord_4767987
  simp only [CollatzResearch.WordTrace]
  refine ⟨173902772577404881194390215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115935181718269920796260143 173902772577404881194390215)
  ·
    refine ⟨260854158866107321791585323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173902772577404881194390215 260854158866107321791585323)
    ·
      refine ⟨391281238299160982687377985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260854158866107321791585323 391281238299160982687377985)
      ·
        refine ⟨293460928724370737015533489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391281238299160982687377985 293460928724370737015533489)
        ·
          refine ⟨220095696543278052761650117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293460928724370737015533489 220095696543278052761650117)
          ·
            refine ⟨41267943101864634892809397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220095696543278052761650117 41267943101864634892809397)
            ·
              refine ⟨3868869665799809521200881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41267943101864634892809397 3868869665799809521200881)
              ·
                refine ⟨2901652249349857140900661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3868869665799809521200881 2901652249349857140900661)
                ·
                  refine ⟨272029898376549106959437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2901652249349857140900661 272029898376549106959437)
                  ·
                    rfl

theorem cell23_4767987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 5].length) (baseStart_4767987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4767987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4767987 prefixEnd_4767987 := by exact prefixLift 4767987
  have htrace : WordTrace (prefixWord ++ tailWord_4767987) baseStart_4767987 baseEnd_4767987 := by
    simpa [prefixWord, tailWord_4767987, baseEnd_4767987] using wordTrace_append hprefix tailTrace_4767987
  have hstable : (prefixWord ++ tailWord_4767987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4767987).length < 2 ^ (prefixWord ++ tailWord_4767987).sum := by decide
  have hdescent : baseEnd_4767987 < baseStart_4767987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4767987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768060 : List Nat := [2, 2, 2, 2, 1, 2, 1, 5, 6]
def baseStart_4768060 : Nat := 118140960795 + 4768060 * 2 ^ 59
def prefixEnd_4768060 : Nat := 4983230072969 + 3 ^ 40 * 4768060 * 2
def baseEnd_4768060 : Nat := 272034063275191130780233

theorem tailTrace_4768060 : CollatzResearch.WordTrace tailWord_4768060 prefixEnd_4768060 272034063275191130780233 := by
  unfold tailWord_4768060
  simp only [CollatzResearch.WordTrace]
  refine ⟨86952717553070207330898817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115936956737426943107865089 86952717553070207330898817)
  ·
    refine ⟨65214538164802655498174113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86952717553070207330898817 65214538164802655498174113)
    ·
      refine ⟨48910903623601991623630585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65214538164802655498174113 48910903623601991623630585)
      ·
        refine ⟨36683177717701493717722939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48910903623601991623630585 36683177717701493717722939)
        ·
          refine ⟨55024766576552240576584409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36683177717701493717722939 55024766576552240576584409)
          ·
            refine ⟨41268574932414180432438307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55024766576552240576584409 41268574932414180432438307)
            ·
              refine ⟨61902862398621270648657461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41268574932414180432438307 61902862398621270648657461)
              ·
                refine ⟨5803393349870744123311637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61902862398621270648657461 5803393349870744123311637)
                ·
                  refine ⟨272034063275191130780233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5803393349870744123311637 272034063275191130780233)
                  ·
                    rfl

theorem cell23_4768060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_4768060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768060 prefixEnd_4768060 := by exact prefixLift 4768060
  have htrace : WordTrace (prefixWord ++ tailWord_4768060) baseStart_4768060 baseEnd_4768060 := by
    simpa [prefixWord, tailWord_4768060, baseEnd_4768060] using wordTrace_append hprefix tailTrace_4768060
  have hstable : (prefixWord ++ tailWord_4768060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768060).length < 2 ^ (prefixWord ++ tailWord_4768060).sum := by decide
  have hdescent : baseEnd_4768060 < baseStart_4768060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768087 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 5, 1, 3]
def baseStart_4768087 : Nat := 118140960795 + 4768087 * 2 ^ 59
def prefixEnd_4768087 : Nat := 4983230072969 + 3 ^ 40 * 4768087 * 2
def baseEnd_4768087 : Nat := 2448320433454391571384473

theorem tailTrace_4768087 : CollatzResearch.WordTrace tailWord_4768087 prefixEnd_4768087 2448320433454391571384473 := by
  unfold tailWord_4768087
  simp only [CollatzResearch.WordTrace]
  refine ⟨173906419877042598273030515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115937613251361732182020343 173906419877042598273030515)
  ·
    refine ⟨260859629815563897409545773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173906419877042598273030515 260859629815563897409545773)
    ·
      refine ⟨97822361180836461528579665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260859629815563897409545773 97822361180836461528579665)
      ·
        refine ⟨73366770885627346146434749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97822361180836461528579665 73366770885627346146434749)
        ·
          refine ⟨27512539082110254804913031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73366770885627346146434749 27512539082110254804913031)
          ·
            refine ⟨41268808623165382207369547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27512539082110254804913031 41268808623165382207369547)
            ·
              refine ⟨61903212934748073311054321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41268808623165382207369547 61903212934748073311054321)
              ·
                refine ⟨46427409701061054983290741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61903212934748073311054321 46427409701061054983290741)
                ·
                  refine ⟨4352569659474473904683507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46427409701061054983290741 4352569659474473904683507)
                  ·
                    refine ⟨6528854489211710857025261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4352569659474473904683507 6528854489211710857025261)
                    ·
                      refine ⟨2448320433454391571384473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6528854489211710857025261 2448320433454391571384473)
                      ·
                        rfl

theorem cell23_4768087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_4768087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768087 prefixEnd_4768087 := by exact prefixLift 4768087
  have htrace : WordTrace (prefixWord ++ tailWord_4768087) baseStart_4768087 baseEnd_4768087 := by
    simpa [prefixWord, tailWord_4768087, baseEnd_4768087] using wordTrace_append hprefix tailTrace_4768087
  have hstable : (prefixWord ++ tailWord_4768087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768087).length < 2 ^ (prefixWord ++ tailWord_4768087).sum := by decide
  have hdescent : baseEnd_4768087 < baseStart_4768087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768104 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_4768104 : Nat := 118140960795 + 4768104 * 2 ^ 59
def prefixEnd_4768104 : Nat := 4983230072969 + 3 ^ 40 * 4768104 * 2
def baseEnd_4768104 : Nat := 2448329162625518004871895

theorem tailTrace_4768104 : CollatzResearch.WordTrace tailWord_4768104 prefixEnd_4768104 2448329162625518004871895 := by
  unfold tailWord_4768104
  simp only [CollatzResearch.WordTrace]
  refine ⟨86953519958990505088199683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115938026611987340117599577 86953519958990505088199683)
  ·
    refine ⟨130430279938485757632299525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86953519958990505088199683 130430279938485757632299525)
    ·
      refine ⟨24455677488466079556056161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130430279938485757632299525 24455677488466079556056161)
      ·
        refine ⟨18341758116349559667042121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24455677488466079556056161 18341758116349559667042121)
        ·
          refine ⟨13756318587262169750281591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18341758116349559667042121 13756318587262169750281591)
          ·
            refine ⟨20634477880893254625422387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13756318587262169750281591 20634477880893254625422387)
            ·
              refine ⟨30951716821339881938133581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20634477880893254625422387 30951716821339881938133581)
              ·
                refine ⟨11606893808002455726800093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30951716821339881938133581 11606893808002455726800093)
                ·
                  refine ⟨4352585178000920897550035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11606893808002455726800093 4352585178000920897550035)
                  ·
                    refine ⟨6528877767001381346325053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4352585178000920897550035 6528877767001381346325053)
                    ·
                      refine ⟨2448329162625518004871895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6528877767001381346325053 2448329162625518004871895)
                      ·
                        rfl

theorem cell23_4768104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_4768104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768104 prefixEnd_4768104 := by exact prefixLift 4768104
  have htrace : WordTrace (prefixWord ++ tailWord_4768104) baseStart_4768104 baseEnd_4768104 := by
    simpa [prefixWord, tailWord_4768104, baseEnd_4768104] using wordTrace_append hprefix tailTrace_4768104
  have hstable : (prefixWord ++ tailWord_4768104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768104).length < 2 ^ (prefixWord ++ tailWord_4768104).sum := by decide
  have hdescent : baseEnd_4768104 < baseStart_4768104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768137 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 4, 4]
def baseStart_4768137 : Nat := 118140960795 + 4768137 * 2 ^ 59
def prefixEnd_4768137 : Nat := 4983230072969 + 3 ^ 40 * 4768137 * 2
def baseEnd_4768137 : Nat := 816115369162372125253081

theorem tailTrace_4768137 : CollatzResearch.WordTrace tailWord_4768137 prefixEnd_4768137 816115369162372125253081 := by
  unfold tailWord_4768137
  simp only [CollatzResearch.WordTrace]
  refine ⟨173908243526861456812350665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115938829017907637874900443 173908243526861456812350665)
  ·
    refine ⟨130431182645146092609262999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173908243526861456812350665 130431182645146092609262999)
    ·
      refine ⟨195646773967719138913894499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130431182645146092609262999 195646773967719138913894499)
      ·
        refine ⟨293470160951578708370841749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195646773967719138913894499 293470160951578708370841749)
        ·
          refine ⟨13756413794605251954883207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 293470160951578708370841749 13756413794605251954883207)
          ·
            refine ⟨20634620691907877932324811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13756413794605251954883207 20634620691907877932324811)
            ·
              refine ⟨30951931037861816898487217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20634620691907877932324811 30951931037861816898487217)
              ·
                refine ⟨23213948278396362673865413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30951931037861816898487217 23213948278396362673865413)
                ·
                  refine ⟨4352615302199318001349765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23213948278396362673865413 4352615302199318001349765)
                  ·
                    refine ⟨816115369162372125253081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4352615302199318001349765 816115369162372125253081)
                    ·
                      rfl

theorem cell23_4768137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 4].length) (baseStart_4768137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768137 prefixEnd_4768137 := by exact prefixLift 4768137
  have htrace : WordTrace (prefixWord ++ tailWord_4768137) baseStart_4768137 baseEnd_4768137 := by
    simpa [prefixWord, tailWord_4768137, baseEnd_4768137] using wordTrace_append hprefix tailTrace_4768137
  have hstable : (prefixWord ++ tailWord_4768137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768137).length < 2 ^ (prefixWord ++ tailWord_4768137).sum := by decide
  have hdescent : baseEnd_4768137 < baseStart_4768137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768167 : List Nat := [1, 1, 6, 1, 1, 3, 2, 8]
def baseStart_4768167 : Nat := 118140960795 + 4768167 * 2 ^ 59
def prefixEnd_4768167 : Nat := 4983230072969 + 3 ^ 40 * 4768167 * 2
def baseEnd_4768167 : Nat := 90680055996546342903115

theorem tailTrace_4768167 : CollatzResearch.WordTrace tailWord_4768167 prefixEnd_4768167 90680055996546342903115 := by
  unfold tailWord_4768167
  simp only [CollatzResearch.WordTrace]
  refine ⟨173909337716752771935942755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115939558477835181290628503 173909337716752771935942755)
  ·
    refine ⟨260864006575129157903914133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173909337716752771935942755 260864006575129157903914133)
    ·
      refine ⟨12228000308209179276745975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 260864006575129157903914133 12228000308209179276745975)
      ·
        refine ⟨18342000462313768915118963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12228000308209179276745975 18342000462313768915118963)
        ·
          refine ⟨27513000693470653372678445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18342000462313768915118963 27513000693470653372678445)
          ·
            refine ⟨10317375260051495014754417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27513000693470653372678445 10317375260051495014754417)
            ·
              refine ⟨7738031445038621261065813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10317375260051495014754417 7738031445038621261065813)
              ·
                refine ⟨90680055996546342903115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7738031445038621261065813 90680055996546342903115)
                ·
                  rfl

theorem cell23_4768167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 8].length) (baseStart_4768167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768167 prefixEnd_4768167 := by exact prefixLift 4768167
  have htrace : WordTrace (prefixWord ++ tailWord_4768167) baseStart_4768167 baseEnd_4768167 := by
    simpa [prefixWord, tailWord_4768167, baseEnd_4768167] using wordTrace_append hprefix tailTrace_4768167
  have hstable : (prefixWord ++ tailWord_4768167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768167).length < 2 ^ (prefixWord ++ tailWord_4768167).sum := by decide
  have hdescent : baseEnd_4768167 < baseStart_4768167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768212 : List Nat := [2, 4, 1, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_4768212 : Nat := 118140960795 + 4768212 * 2 ^ 59
def prefixEnd_4768212 : Nat := 4983230072969 + 3 ^ 40 * 4768212 * 2
def baseEnd_4768212 : Nat := 2448384618536203582321399

theorem tailTrace_4768212 : CollatzResearch.WordTrace tailWord_4768212 prefixEnd_4768212 2448384618536203582321399 := by
  unfold tailWord_4768212
  simp only [CollatzResearch.WordTrace]
  refine ⟨86955489500794872310665445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115940652667726496414220593 86955489500794872310665445)
  ·
    refine ⟨16304154281399038558249771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86955489500794872310665445 16304154281399038558249771)
    ·
      refine ⟨24456231422098557837374657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16304154281399038558249771 24456231422098557837374657)
      ·
        refine ⟨18342173566573918378030993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24456231422098557837374657 18342173566573918378030993)
        ·
          refine ⟨13756630174930438783523245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18342173566573918378030993 13756630174930438783523245)
          ·
            refine ⟨5158736315598914543821217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13756630174930438783523245 5158736315598914543821217)
            ·
              refine ⟨3869052236699185907865913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5158736315598914543821217 3869052236699185907865913)
              ·
                refine ⟨2901789177524389430899435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3869052236699185907865913 2901789177524389430899435)
                ·
                  refine ⟨4352683766286584146349153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2901789177524389430899435 4352683766286584146349153)
                  ·
                    refine ⟨3264512824714938109761865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4352683766286584146349153 3264512824714938109761865)
                    ·
                      refine ⟨2448384618536203582321399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3264512824714938109761865 2448384618536203582321399)
                      ·
                        rfl

theorem cell23_4768212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_4768212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768212 prefixEnd_4768212 := by exact prefixLift 4768212
  have htrace : WordTrace (prefixWord ++ tailWord_4768212) baseStart_4768212 baseEnd_4768212 := by
    simpa [prefixWord, tailWord_4768212, baseEnd_4768212] using wordTrace_append hprefix tailTrace_4768212
  have hstable : (prefixWord ++ tailWord_4768212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768212).length < 2 ^ (prefixWord ++ tailWord_4768212).sum := by decide
  have hdescent : baseEnd_4768212 < baseStart_4768212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768262 : List Nat := [6, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_4768262 : Nat := 118140960795 + 4768262 * 2 ^ 59
def prefixEnd_4768262 : Nat := 4983230072969 + 3 ^ 40 * 4768262 * 2
def baseEnd_4768262 : Nat := 2448410292568928386696169

theorem tailTrace_4768262 : CollatzResearch.WordTrace tailWord_4768262 prefixEnd_4768262 2448410292568928386696169 := by
  unfold tailWord_4768262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5434775082856518848770345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 115941868434272402107100693 5434775082856518848770345)
  ·
    refine ⟨4076081312142389136577759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5434775082856518848770345 4076081312142389136577759)
    ·
      refine ⟨6114121968213583704866639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4076081312142389136577759 6114121968213583704866639)
      ·
        refine ⟨9171182952320375557299959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6114121968213583704866639 9171182952320375557299959)
        ·
          refine ⟨13756774428480563335949939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9171182952320375557299959 13756774428480563335949939)
          ·
            refine ⟨20635161642720845003924909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13756774428480563335949939 20635161642720845003924909)
            ·
              refine ⟨7738185616020316876471841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20635161642720845003924909 7738185616020316876471841)
              ·
                refine ⟨5803639212015237657353881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7738185616020316876471841 5803639212015237657353881)
                ·
                  refine ⟨4352729409011428243015411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5803639212015237657353881 4352729409011428243015411)
                  ·
                    refine ⟨6529094113517142364523117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4352729409011428243015411 6529094113517142364523117)
                    ·
                      refine ⟨2448410292568928386696169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6529094113517142364523117 2448410292568928386696169)
                      ·
                        rfl

theorem cell23_4768262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_4768262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768262 prefixEnd_4768262 := by exact prefixLift 4768262
  have htrace : WordTrace (prefixWord ++ tailWord_4768262) baseStart_4768262 baseEnd_4768262 := by
    simpa [prefixWord, tailWord_4768262, baseEnd_4768262] using wordTrace_append hprefix tailTrace_4768262
  have hstable : (prefixWord ++ tailWord_4768262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768262).length < 2 ^ (prefixWord ++ tailWord_4768262).sum := by decide
  have hdescent : baseEnd_4768262 < baseStart_4768262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768268 : List Nat := [2, 2, 1, 2, 4, 1, 3, 2, 2, 2, 2]
def baseStart_4768268 : Nat := 118140960795 + 4768268 * 2 ^ 59
def prefixEnd_4768268 : Nat := 4983230072969 + 3 ^ 40 * 4768268 * 2
def baseEnd_4768268 : Nat := 2448413373452855363221141

theorem tailTrace_4768268 : CollatzResearch.WordTrace tailWord_4768268 prefixEnd_4768268 2448413373452855363221141 := by
  unfold tailWord_4768268
  simp only [CollatzResearch.WordTrace]
  refine ⟨86956510744693433092684729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115942014326257910790246305 86956510744693433092684729)
  ·
    refine ⟨65217383058520074819513547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86956510744693433092684729 65217383058520074819513547)
    ·
      refine ⟨97826074587780112229270321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65217383058520074819513547 97826074587780112229270321)
      ·
        refine ⟨73369555940835084171952741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97826074587780112229270321 73369555940835084171952741)
        ·
          refine ⟨13756791738906578282241139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73369555940835084171952741 13756791738906578282241139)
          ·
            refine ⟨20635187608359867423361709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13756791738906578282241139 20635187608359867423361709)
            ·
              refine ⟨7738195353134950283760641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20635187608359867423361709 7738195353134950283760641)
              ·
                refine ⟨5803646514851212712820481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7738195353134950283760641 5803646514851212712820481)
                ·
                  refine ⟨4352734886138409534615361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5803646514851212712820481 4352734886138409534615361)
                  ·
                    refine ⟨3264551164603807150961521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4352734886138409534615361 3264551164603807150961521)
                    ·
                      refine ⟨2448413373452855363221141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3264551164603807150961521 2448413373452855363221141)
                      ·
                        rfl

theorem cell23_4768268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_4768268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768268 prefixEnd_4768268 := by exact prefixLift 4768268
  have htrace : WordTrace (prefixWord ++ tailWord_4768268) baseStart_4768268 baseEnd_4768268 := by
    simpa [prefixWord, tailWord_4768268, baseEnd_4768268] using wordTrace_append hprefix tailTrace_4768268
  have hstable : (prefixWord ++ tailWord_4768268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768268).length < 2 ^ (prefixWord ++ tailWord_4768268).sum := by decide
  have hdescent : baseEnd_4768268 < baseStart_4768268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768284 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_4768284 : Nat := 118140960795 + 4768284 * 2 ^ 59
def prefixEnd_4768284 : Nat := 4983230072969 + 3 ^ 40 * 4768284 * 2
def baseEnd_4768284 : Nat := 2448421589143327300621067

theorem tailTrace_4768284 : CollatzResearch.WordTrace tailWord_4768284 prefixEnd_4768284 2448421589143327300621067 := by
  unfold tailWord_4768284
  simp only [CollatzResearch.WordTrace]
  refine ⟨86956802528664450458975953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115942403371552600611967937 86956802528664450458975953)
  ·
    refine ⟨65217601896498337844231965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86956802528664450458975953 65217601896498337844231965)
    ·
      refine ⟨24456600711186876691586987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65217601896498337844231965 24456600711186876691586987)
      ·
        refine ⟨36684901066780315037380481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24456600711186876691586987 36684901066780315037380481)
        ·
          refine ⟨27513675800085236278035361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36684901066780315037380481 27513675800085236278035361)
          ·
            refine ⟨20635256850063927208526521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27513675800085236278035361 20635256850063927208526521)
            ·
              refine ⟨15476442637547945406394891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20635256850063927208526521 15476442637547945406394891)
              ·
                refine ⟨23214663956321918109592337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15476442637547945406394891 23214663956321918109592337)
                ·
                  refine ⟨17410997967241438582194253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23214663956321918109592337 17410997967241438582194253)
                  ·
                    refine ⟨6529124237715539468322845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17410997967241438582194253 6529124237715539468322845)
                    ·
                      refine ⟨2448421589143327300621067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6529124237715539468322845 2448421589143327300621067)
                      ·
                        rfl

theorem cell23_4768284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_4768284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768284 prefixEnd_4768284 := by exact prefixLift 4768284
  have htrace : WordTrace (prefixWord ++ tailWord_4768284) baseStart_4768284 baseEnd_4768284 := by
    simpa [prefixWord, tailWord_4768284, baseEnd_4768284] using wordTrace_append hprefix tailTrace_4768284
  have hstable : (prefixWord ++ tailWord_4768284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768284).length < 2 ^ (prefixWord ++ tailWord_4768284).sum := by decide
  have hdescent : baseEnd_4768284 < baseStart_4768284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768285 : List Nat := [1, 4, 2, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_4768285 : Nat := 118140960795 + 4768285 * 2 ^ 59
def prefixEnd_4768285 : Nat := 4983230072969 + 3 ^ 40 * 4768285 * 2
def baseEnd_4768285 : Nat := 2448422102623981796708563

theorem tailTrace_4768285 : CollatzResearch.WordTrace tailWord_4768285 prefixEnd_4768285 2448422102623981796708563 := by
  unfold tailWord_4768285
  simp only [CollatzResearch.WordTrace]
  refine ⟨173913641530325278088738309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115942427686883518725825539 173913641530325278088738309)
  ·
    refine ⟨32608807786935989641638433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173913641530325278088738309 32608807786935989641638433)
    ·
      refine ⟨24456605840201992231228825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32608807786935989641638433 24456605840201992231228825)
      ·
        refine ⟨18342454380151494173421619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24456605840201992231228825 18342454380151494173421619)
        ·
          refine ⟨27513681570227241260132429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18342454380151494173421619 27513681570227241260132429)
          ·
            refine ⟨10317630588835215472549661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27513681570227241260132429 10317630588835215472549661)
            ·
              refine ⟨3869111470813205802206123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10317630588835215472549661 3869111470813205802206123)
              ·
                refine ⟨5803667206219808703309185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3869111470813205802206123 5803667206219808703309185)
                ·
                  refine ⟨4352750404664856527481889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5803667206219808703309185 4352750404664856527481889)
                  ·
                    refine ⟨3264562803498642395611417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4352750404664856527481889 3264562803498642395611417)
                    ·
                      refine ⟨2448422102623981796708563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3264562803498642395611417 2448422102623981796708563)
                      ·
                        rfl

theorem cell23_4768285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_4768285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768285 prefixEnd_4768285 := by exact prefixLift 4768285
  have htrace : WordTrace (prefixWord ++ tailWord_4768285) baseStart_4768285 baseEnd_4768285 := by
    simpa [prefixWord, tailWord_4768285, baseEnd_4768285] using wordTrace_append hprefix tailTrace_4768285
  have hstable : (prefixWord ++ tailWord_4768285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768285).length < 2 ^ (prefixWord ++ tailWord_4768285).sum := by decide
  have hdescent : baseEnd_4768285 < baseStart_4768285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768307 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 4]
def baseStart_4768307 : Nat := 118140960795 + 4768307 * 2 ^ 59
def prefixEnd_4768307 : Nat := 4983230072969 + 3 ^ 40 * 4768307 * 2
def baseEnd_4768307 : Nat := 2448433399198380710633461

theorem tailTrace_4768307 : CollatzResearch.WordTrace tailWord_4768307 prefixEnd_4768307 2448433399198380710633461 := by
  unfold tailWord_4768307
  simp only [CollatzResearch.WordTrace]
  refine ⟨173914443936245575846039175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115942962624163717230692783 173914443936245575846039175)
  ·
    refine ⟨260871665904368363769058763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173914443936245575846039175 260871665904368363769058763)
    ·
      refine ⟨391307498856552545653588145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260871665904368363769058763 391307498856552545653588145)
      ·
        refine ⟨293480624142414409240191109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391307498856552545653588145 293480624142414409240191109)
        ·
          refine ⟨55027617026702701732535833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 293480624142414409240191109 55027617026702701732535833)
          ·
            refine ⟨41270712770027026299401875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55027617026702701732535833 41270712770027026299401875)
            ·
              refine ⟨61906069155040539449102813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41270712770027026299401875 61906069155040539449102813)
              ·
                refine ⟨23214775933140202293413555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61906069155040539449102813 23214775933140202293413555)
                ·
                  refine ⟨34822163899710303440120333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23214775933140202293413555 34822163899710303440120333)
                  ·
                    refine ⟨13058311462391363790045125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34822163899710303440120333 13058311462391363790045125)
                    ·
                      refine ⟨2448433399198380710633461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13058311462391363790045125 2448433399198380710633461)
                      ·
                        rfl

theorem cell23_4768307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_4768307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768307 prefixEnd_4768307 := by exact prefixLift 4768307
  have htrace : WordTrace (prefixWord ++ tailWord_4768307) baseStart_4768307 baseEnd_4768307 := by
    simpa [prefixWord, tailWord_4768307, baseEnd_4768307] using wordTrace_append hprefix tailTrace_4768307
  have hstable : (prefixWord ++ tailWord_4768307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768307).length < 2 ^ (prefixWord ++ tailWord_4768307).sum := by decide
  have hdescent : baseEnd_4768307 < baseStart_4768307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768381 : List Nat := [1, 4, 1, 1, 5, 1, 2, 2, 6]
def baseStart_4768381 : Nat := 118140960795 + 4768381 * 2 ^ 59
def prefixEnd_4768381 : Nat := 4983230072969 + 3 ^ 40 * 4768381 * 2
def baseEnd_4768381 : Nat := 272052377418534824567569

theorem tailTrace_4768381 : CollatzResearch.WordTrace tailWord_4768381 prefixEnd_4768381 272052377418534824567569 := by
  unfold tailWord_4768381
  simp only [CollatzResearch.WordTrace]
  refine ⟨173917142937977486484232997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115944761958651657656155331 173917142937977486484232997)
  ·
    refine ⟨32609464300870778715793687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173917142937977486484232997 32609464300870778715793687)
    ·
      refine ⟨48914196451306168073690531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32609464300870778715793687 48914196451306168073690531)
      ·
        refine ⟨73371294676959252110535797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48914196451306168073690531 73371294676959252110535797)
        ·
          refine ⟨6878558875964929885362731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73371294676959252110535797 6878558875964929885362731)
          ·
            refine ⟨10317838313947394828044097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6878558875964929885362731 10317838313947394828044097)
            ·
              refine ⟨7738378735460546121033073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10317838313947394828044097 7738378735460546121033073)
              ·
                refine ⟨5803784051595409590774805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7738378735460546121033073 5803784051595409590774805)
                ·
                  refine ⟨272052377418534824567569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5803784051595409590774805 272052377418534824567569)
                  ·
                    rfl

theorem cell23_4768381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_4768381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768381 prefixEnd_4768381 := by exact prefixLift 4768381
  have htrace : WordTrace (prefixWord ++ tailWord_4768381) baseStart_4768381 baseEnd_4768381 := by
    simpa [prefixWord, tailWord_4768381, baseEnd_4768381] using wordTrace_append hprefix tailTrace_4768381
  have hstable : (prefixWord ++ tailWord_4768381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768381).length < 2 ^ (prefixWord ++ tailWord_4768381).sum := by decide
  have hdescent : baseEnd_4768381 < baseStart_4768381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768391 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_4768391 : Nat := 118140960795 + 4768391 * 2 ^ 59
def prefixEnd_4768391 : Nat := 4983230072969 + 3 ^ 40 * 4768391 * 2
def baseEnd_4768391 : Nat := 2448476531573358381983075

theorem tailTrace_4768391 : CollatzResearch.WordTrace tailWord_4768391 prefixEnd_4768391 2448476531573358381983075 := by
  unfold tailWord_4768391
  simp only [CollatzResearch.WordTrace]
  refine ⟨173917507667941258192097027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115945005111960838794731351 173917507667941258192097027)
  ·
    refine ⟨260876261501911887288145541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173917507667941258192097027 260876261501911887288145541)
    ·
      refine ⟨48914299031608478866527289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260876261501911887288145541 48914299031608478866527289)
      ·
        refine ⟨36685724273706359149895467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48914299031608478866527289 36685724273706359149895467)
        ·
          refine ⟨55028586410559538724843201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36685724273706359149895467 55028586410559538724843201)
          ·
            refine ⟨41271439807919654043632401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55028586410559538724843201 41271439807919654043632401)
            ·
              refine ⟨30953579855939740532724301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41271439807919654043632401 30953579855939740532724301)
              ·
                refine ⟨11607592445977402699771613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30953579855939740532724301 11607592445977402699771613)
                ·
                  refine ⟨4352847167241526012414355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11607592445977402699771613 4352847167241526012414355)
                  ·
                    refine ⟨6529270750862289018621533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4352847167241526012414355 6529270750862289018621533)
                    ·
                      refine ⟨2448476531573358381983075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6529270750862289018621533 2448476531573358381983075)
                      ·
                        rfl

theorem cell23_4768391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_4768391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768391 prefixEnd_4768391 := by exact prefixLift 4768391
  have htrace : WordTrace (prefixWord ++ tailWord_4768391) baseStart_4768391 baseEnd_4768391 := by
    simpa [prefixWord, tailWord_4768391, baseEnd_4768391] using wordTrace_append hprefix tailTrace_4768391
  have hstable : (prefixWord ++ tailWord_4768391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768391).length < 2 ^ (prefixWord ++ tailWord_4768391).sum := by decide
  have hdescent : baseEnd_4768391 < baseStart_4768391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768431 : List Nat := [1, 1, 2, 1, 2, 6, 1, 3, 1, 1, 4]
def baseStart_4768431 : Nat := 118140960795 + 4768431 * 2 ^ 59
def prefixEnd_4768431 : Nat := 4983230072969 + 3 ^ 40 * 4768431 * 2
def baseEnd_4768431 : Nat := 2448497070799538225482891

theorem tailTrace_4768431 : CollatzResearch.WordTrace tailWord_4768431 prefixEnd_4768431 2448497070799538225482891 := by
  unfold tailWord_4768431
  simp only [CollatzResearch.WordTrace]
  refine ⟨173918966587796345023553147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115945977725197563349035431 173918966587796345023553147)
  ·
    refine ⟨260878449881694517535329721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173918966587796345023553147 260878449881694517535329721)
    ·
      refine ⟨195658837411270888151497291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260878449881694517535329721 195658837411270888151497291)
      ·
        refine ⟨293488256116906332227245937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195658837411270888151497291 293488256116906332227245937)
        ·
          refine ⟨220116192087679749170434453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293488256116906332227245937 220116192087679749170434453)
          ·
            refine ⟨10317946504109988242364115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 220116192087679749170434453 10317946504109988242364115)
            ·
              refine ⟨15476919756164982363546173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10317946504109988242364115 15476919756164982363546173)
              ·
                refine ⟨5803844908561868386329815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15476919756164982363546173 5803844908561868386329815)
                ·
                  refine ⟨8705767362842802579494723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5803844908561868386329815 8705767362842802579494723)
                  ·
                    refine ⟨13058651044264203869242085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8705767362842802579494723 13058651044264203869242085)
                    ·
                      refine ⟨2448497070799538225482891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13058651044264203869242085 2448497070799538225482891)
                      ·
                        rfl

theorem cell23_4768431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 1, 4].length) (baseStart_4768431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768431 prefixEnd_4768431 := by exact prefixLift 4768431
  have htrace : WordTrace (prefixWord ++ tailWord_4768431) baseStart_4768431 baseEnd_4768431 := by
    simpa [prefixWord, tailWord_4768431, baseEnd_4768431] using wordTrace_append hprefix tailTrace_4768431
  have hstable : (prefixWord ++ tailWord_4768431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768431).length < 2 ^ (prefixWord ++ tailWord_4768431).sum := by decide
  have hdescent : baseEnd_4768431 < baseStart_4768431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768434 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_4768434 : Nat := 118140960795 + 4768434 * 2 ^ 59
def prefixEnd_4768434 : Nat := 4983230072969 + 3 ^ 40 * 4768434 * 2
def baseEnd_4768434 : Nat := 2448498611241501713745377

theorem tailTrace_4768434 : CollatzResearch.WordTrace tailWord_4768434 prefixEnd_4768434 2448498611241501713745377 := by
  unfold tailWord_4768434
  simp only [CollatzResearch.WordTrace]
  refine ⟨43479769001696369133978089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115946050671190317690608237 43479769001696369133978089)
  ·
    refine ⟨32609826751272276850483567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43479769001696369133978089 32609826751272276850483567)
    ·
      refine ⟨48914740126908415275725351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32609826751272276850483567 48914740126908415275725351)
      ·
        refine ⟨73372110190362622913588027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48914740126908415275725351 73372110190362622913588027)
        ·
          refine ⟨110058165285543934370382041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73372110190362622913588027 110058165285543934370382041)
          ·
            refine ⟨82543623964157950777786531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110058165285543934370382041 82543623964157950777786531)
            ·
              refine ⟨123815435946236926166679797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82543623964157950777786531 123815435946236926166679797)
              ·
                refine ⟨11607697119959711828126231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123815435946236926166679797 11607697119959711828126231)
                ·
                  refine ⟨17411545679939567742189347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11607697119959711828126231 17411545679939567742189347)
                  ·
                    refine ⟨26117318519909351613284021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17411545679939567742189347 26117318519909351613284021)
                    ·
                      refine ⟨2448498611241501713745377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26117318519909351613284021 2448498611241501713745377)
                      ·
                        rfl

theorem cell23_4768434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_4768434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768434 prefixEnd_4768434 := by exact prefixLift 4768434
  have htrace : WordTrace (prefixWord ++ tailWord_4768434) baseStart_4768434 baseEnd_4768434 := by
    simpa [prefixWord, tailWord_4768434, baseEnd_4768434] using wordTrace_append hprefix tailTrace_4768434
  have hstable : (prefixWord ++ tailWord_4768434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768434).length < 2 ^ (prefixWord ++ tailWord_4768434).sum := by decide
  have hdescent : baseEnd_4768434 < baseStart_4768434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768444 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_4768444 : Nat := 118140960795 + 4768444 * 2 ^ 59
def prefixEnd_4768444 : Nat := 4983230072969 + 3 ^ 40 * 4768444 * 2
def baseEnd_4768444 : Nat := 2448503746048046674620331

theorem tailTrace_4768444 : CollatzResearch.WordTrace tailWord_4768444 prefixEnd_4768444 2448503746048046674620331 := by
  unfold tailWord_4768444
  simp only [CollatzResearch.WordTrace]
  refine ⟨86959720368374624121888193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115946293824499498829184257 86959720368374624121888193)
  ·
    refine ⟨65219790276280968091416145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86959720368374624121888193 65219790276280968091416145)
    ·
      refine ⟨48914842707210726068562109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65219790276280968091416145 48914842707210726068562109)
      ·
        refine ⟨18343066015204022275710791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48914842707210726068562109 18343066015204022275710791)
        ·
          refine ⟨27514599022806033413566187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18343066015204022275710791 27514599022806033413566187)
          ·
            refine ⟨41271898534209050120349281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27514599022806033413566187 41271898534209050120349281)
            ·
              refine ⟨30953923900656787590261961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41271898534209050120349281 30953923900656787590261961)
              ·
                refine ⟨23215442925492590692696471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30953923900656787590261961 23215442925492590692696471)
                ·
                  refine ⟨34823164388238886039044707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23215442925492590692696471 34823164388238886039044707)
                  ·
                    refine ⟨52234746582358329058567061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34823164388238886039044707 52234746582358329058567061)
                    ·
                      refine ⟨2448503746048046674620331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52234746582358329058567061 2448503746048046674620331)
                      ·
                        rfl

theorem cell23_4768444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_4768444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768444 prefixEnd_4768444 := by exact prefixLift 4768444
  have htrace : WordTrace (prefixWord ++ tailWord_4768444) baseStart_4768444 baseEnd_4768444 := by
    simpa [prefixWord, tailWord_4768444, baseEnd_4768444] using wordTrace_append hprefix tailTrace_4768444
  have hstable : (prefixWord ++ tailWord_4768444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768444).length < 2 ^ (prefixWord ++ tailWord_4768444).sum := by decide
  have hdescent : baseEnd_4768444 < baseStart_4768444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768448 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 3, 2, 2]
def baseStart_4768448 : Nat := 118140960795 + 4768448 * 2 ^ 59
def prefixEnd_4768448 : Nat := 4983230072969 + 3 ^ 40 * 4768448 * 2
def baseEnd_4768448 : Nat := 2448505799970664658970313

theorem tailTrace_4768448 : CollatzResearch.WordTrace tailWord_4768448 prefixEnd_4768448 2448505799970664658970313 := by
  unfold tailWord_4768448
  simp only [CollatzResearch.WordTrace]
  refine ⟨86959793314367378463460999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115946391085823171284614665 86959793314367378463460999)
  ·
    refine ⟨130439689971551067695191499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86959793314367378463460999 130439689971551067695191499)
    ·
      refine ⟨195659534957326601542787249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130439689971551067695191499 195659534957326601542787249)
      ·
        refine ⟨146744651217994951157090437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195659534957326601542787249 146744651217994951157090437)
        ·
          refine ⟨27514622103374053341954457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146744651217994951157090437 27514622103374053341954457)
          ·
            refine ⟨20635966577530540006465843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27514622103374053341954457 20635966577530540006465843)
            ·
              refine ⟨30953949866295810009698765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20635966577530540006465843 30953949866295810009698765)
              ·
                refine ⟨11607731199860928753637037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30953949866295810009698765 11607731199860928753637037)
                ·
                  refine ⟨4352899199947848282613889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11607731199860928753637037 4352899199947848282613889)
                  ·
                    refine ⟨3264674399960886211960417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4352899199947848282613889 3264674399960886211960417)
                    ·
                      refine ⟨2448505799970664658970313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3264674399960886211960417 2448505799970664658970313)
                      ·
                        rfl

theorem cell23_4768448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 3, 2, 2].length) (baseStart_4768448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768448 prefixEnd_4768448 := by exact prefixLift 4768448
  have htrace : WordTrace (prefixWord ++ tailWord_4768448) baseStart_4768448 baseEnd_4768448 := by
    simpa [prefixWord, tailWord_4768448, baseEnd_4768448] using wordTrace_append hprefix tailTrace_4768448
  have hstable : (prefixWord ++ tailWord_4768448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768448).length < 2 ^ (prefixWord ++ tailWord_4768448).sum := by decide
  have hdescent : baseEnd_4768448 < baseStart_4768448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768471 : List Nat := [1, 1, 3, 2, 1, 6, 2, 7]
def baseStart_4768471 : Nat := 118140960795 + 4768471 * 2 ^ 59
def prefixEnd_4768471 : Nat := 4983230072969 + 3 ^ 40 * 4768471 * 2
def baseEnd_4768471 : Nat := 90685837408359928480841

theorem tailTrace_4768471 : CollatzResearch.WordTrace tailWord_4768471 prefixEnd_4768471 90685837408359928480841 := by
  unfold tailWord_4768471
  simp only [CollatzResearch.WordTrace]
  refine ⟨173920425507651431855009267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115946950338434287903339511 173920425507651431855009267)
  ·
    refine ⟨260880638261477147782513901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173920425507651431855009267 260880638261477147782513901)
    ·
      refine ⟨97830239348053930418442713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260880638261477147782513901 97830239348053930418442713)
      ·
        refine ⟨73372679511040447813832035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97830239348053930418442713 73372679511040447813832035)
        ·
          refine ⟨110059019266560671720748053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73372679511040447813832035 110059019266560671720748053)
          ·
            refine ⟨5159016528120031486910065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110059019266560671720748053 5159016528120031486910065)
            ·
              refine ⟨3869262396090023615182549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5159016528120031486910065 3869262396090023615182549)
              ·
                refine ⟨90685837408359928480841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3869262396090023615182549 90685837408359928480841)
                ·
                  rfl

theorem cell23_4768471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 7].length) (baseStart_4768471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768471 prefixEnd_4768471 := by exact prefixLift 4768471
  have htrace : WordTrace (prefixWord ++ tailWord_4768471) baseStart_4768471 baseEnd_4768471 := by
    simpa [prefixWord, tailWord_4768471, baseEnd_4768471] using wordTrace_append hprefix tailTrace_4768471
  have hstable : (prefixWord ++ tailWord_4768471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768471).length < 2 ^ (prefixWord ++ tailWord_4768471).sum := by decide
  have hdescent : baseEnd_4768471 < baseStart_4768471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768491 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 5, 3, 2]
def baseStart_4768491 : Nat := 118140960795 + 4768491 * 2 ^ 59
def prefixEnd_4768491 : Nat := 4983230072969 + 3 ^ 40 * 4768491 * 2
def baseEnd_4768491 : Nat := 2448527879638807990732615

theorem tailTrace_4768491 : CollatzResearch.WordTrace tailWord_4768491 prefixEnd_4768491 2448527879638807990732615 := by
  unfold tailWord_4768491
  simp only [CollatzResearch.WordTrace]
  refine ⟨173921154967578975270737327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115947436645052650180491551 173921154967578975270737327)
  ·
    refine ⟨260881732451368462906105991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173921154967578975270737327 260881732451368462906105991)
    ·
      refine ⟨391322598677052694359158987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260881732451368462906105991 391322598677052694359158987)
      ·
        refine ⟨586983898015579041538738481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391322598677052694359158987 586983898015579041538738481)
        ·
          refine ⟨440237923511684281154053861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586983898015579041538738481 440237923511684281154053861)
          ·
            refine ⟨82544610658440802716385099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 440237923511684281154053861 82544610658440802716385099)
            ·
              refine ⟨123816915987661204074577649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82544610658440802716385099 123816915987661204074577649)
              ·
                refine ⟨92862686990745903055933237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123816915987661204074577649 92862686990745903055933237)
                ·
                  refine ⟨8705876905382428411493741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92862686990745903055933237 8705876905382428411493741)
                  ·
                    refine ⟨3264703839518410654310153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8705876905382428411493741 3264703839518410654310153)
                    ·
                      refine ⟨2448527879638807990732615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3264703839518410654310153 2448527879638807990732615)
                      ·
                        rfl

theorem cell23_4768491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 3, 2].length) (baseStart_4768491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768491 prefixEnd_4768491 := by exact prefixLift 4768491
  have htrace : WordTrace (prefixWord ++ tailWord_4768491) baseStart_4768491 baseEnd_4768491 := by
    simpa [prefixWord, tailWord_4768491, baseEnd_4768491] using wordTrace_append hprefix tailTrace_4768491
  have hstable : (prefixWord ++ tailWord_4768491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768491).length < 2 ^ (prefixWord ++ tailWord_4768491).sum := by decide
  have hdescent : baseEnd_4768491 < baseStart_4768491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768498 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_4768498 : Nat := 118140960795 + 4768498 * 2 ^ 59
def prefixEnd_4768498 : Nat := 4983230072969 + 3 ^ 40 * 4768498 * 2
def baseEnd_4768498 : Nat := 2448531474003389463345083

theorem tailTrace_4768498 : CollatzResearch.WordTrace tailWord_4768498 prefixEnd_4768498 2448531474003389463345083 := by
  unfold tailWord_4768498
  simp only [CollatzResearch.WordTrace]
  refine ⟨43480352569638403866560537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115947606852369076977494765 43480352569638403866560537)
  ·
    refine ⟨32610264427228802899920403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43480352569638403866560537 32610264427228802899920403)
    ·
      refine ⟨48915396640843204349880605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32610264427228802899920403 48915396640843204349880605)
      ·
        refine ⟨18343273740316201631205227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48915396640843204349880605 18343273740316201631205227)
        ·
          refine ⟨27514910610474302446807841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18343273740316201631205227 27514910610474302446807841)
          ·
            refine ⟨20636182957855726835105881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27514910610474302446807841 20636182957855726835105881)
            ·
              refine ⟨15477137218391795126329411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20636182957855726835105881 15477137218391795126329411)
              ·
                refine ⟨23215705827587692689494117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15477137218391795126329411 23215705827587692689494117)
                ·
                  refine ⟨4352944842672692379280147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23215705827587692689494117 4352944842672692379280147)
                  ·
                    refine ⟨6529417264009038568920221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4352944842672692379280147 6529417264009038568920221)
                    ·
                      refine ⟨2448531474003389463345083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6529417264009038568920221 2448531474003389463345083)
                      ·
                        rfl

theorem cell23_4768498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_4768498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768498 prefixEnd_4768498 := by exact prefixLift 4768498
  have htrace : WordTrace (prefixWord ++ tailWord_4768498) baseStart_4768498 baseEnd_4768498 := by
    simpa [prefixWord, tailWord_4768498, baseEnd_4768498] using wordTrace_append hprefix tailTrace_4768498
  have hstable : (prefixWord ++ tailWord_4768498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768498).length < 2 ^ (prefixWord ++ tailWord_4768498).sum := by decide
  have hdescent : baseEnd_4768498 < baseStart_4768498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768504 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_4768504 : Nat := 118140960795 + 4768504 * 2 ^ 59
def prefixEnd_4768504 : Nat := 4983230072969 + 3 ^ 40 * 4768504 * 2
def baseEnd_4768504 : Nat := 2448534554887316439870055

theorem tailTrace_4768504 : CollatzResearch.WordTrace tailWord_4768504 prefixEnd_4768504 2448534554887316439870055 := by
  unfold tailWord_4768504
  simp only [CollatzResearch.WordTrace]
  refine ⟨86960814558265939245480283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115947752744354585660640377 86960814558265939245480283)
  ·
    refine ⟨130441221837398908868220425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86960814558265939245480283 130441221837398908868220425)
    ·
      refine ⟨97830916378049181651165319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130441221837398908868220425 97830916378049181651165319)
      ·
        refine ⟨146746374567073772476747979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97830916378049181651165319 146746374567073772476747979)
        ·
          refine ⟨220119561850610658715121969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146746374567073772476747979 220119561850610658715121969)
          ·
            refine ⟨165089671387957994036341477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220119561850610658715121969 165089671387957994036341477)
            ·
              refine ⟨30954313385242123881814027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165089671387957994036341477 30954313385242123881814027)
              ·
                refine ⟨46431470077863185822721041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30954313385242123881814027 46431470077863185822721041)
                ·
                  refine ⟨34823602558397389367040781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46431470077863185822721041 34823602558397389367040781)
                  ·
                    refine ⟨13058850959399021012640293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34823602558397389367040781 13058850959399021012640293)
                    ·
                      refine ⟨2448534554887316439870055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13058850959399021012640293 2448534554887316439870055)
                      ·
                        rfl

theorem cell23_4768504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_4768504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768504 prefixEnd_4768504 := by exact prefixLift 4768504
  have htrace : WordTrace (prefixWord ++ tailWord_4768504) baseStart_4768504 baseEnd_4768504 := by
    simpa [prefixWord, tailWord_4768504, baseEnd_4768504] using wordTrace_append hprefix tailTrace_4768504
  have hstable : (prefixWord ++ tailWord_4768504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768504).length < 2 ^ (prefixWord ++ tailWord_4768504).sum := by decide
  have hdescent : baseEnd_4768504 < baseStart_4768504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768538 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2]
def baseStart_4768538 : Nat := 118140960795 + 4768538 * 2 ^ 59
def prefixEnd_4768538 : Nat := 4983230072969 + 3 ^ 40 * 4768538 * 2
def baseEnd_4768538 : Nat := 2448552013229569306844899

theorem tailTrace_4768538 : CollatzResearch.WordTrace tailWord_4768538 prefixEnd_4768538 2448552013229569306844899 := by
  unfold tailWord_4768538
  simp only [CollatzResearch.WordTrace]
  refine ⟨43480717299602175574424567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115948579465605801531798845 43480717299602175574424567)
  ·
    refine ⟨65221075949403263361636851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43480717299602175574424567 65221075949403263361636851)
    ·
      refine ⟨97831613924104895042455277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65221075949403263361636851 97831613924104895042455277)
      ·
        refine ⟨36686855221539335640920729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97831613924104895042455277 36686855221539335640920729)
        ·
          refine ⟨27515141416154501730690547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36686855221539335640920729 27515141416154501730690547)
          ·
            refine ⟨41272712124231752596035821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27515141416154501730690547 41272712124231752596035821)
            ·
              refine ⟨15477267046586907223513433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41272712124231752596035821 15477267046586907223513433)
              ·
                refine ⟨11607950284940180417635075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15477267046586907223513433 11607950284940180417635075)
                ·
                  refine ⟨17411925427410270626452613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11607950284940180417635075 17411925427410270626452613)
                  ·
                    refine ⟨3264736017639425742459865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17411925427410270626452613 3264736017639425742459865)
                    ·
                      refine ⟨2448552013229569306844899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3264736017639425742459865 2448552013229569306844899)
                      ·
                        rfl

theorem cell23_4768538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_4768538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768538 prefixEnd_4768538 := by exact prefixLift 4768538
  have htrace : WordTrace (prefixWord ++ tailWord_4768538) baseStart_4768538 baseEnd_4768538 := by
    simpa [prefixWord, tailWord_4768538, baseEnd_4768538] using wordTrace_append hprefix tailTrace_4768538
  have hstable : (prefixWord ++ tailWord_4768538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768538).length < 2 ^ (prefixWord ++ tailWord_4768538).sum := by decide
  have hdescent : baseEnd_4768538 < baseStart_4768538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768558 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_4768558 : Nat := 118140960795 + 4768558 * 2 ^ 59
def prefixEnd_4768558 : Nat := 4983230072969 + 3 ^ 40 * 4768558 * 2
def baseEnd_4768558 : Nat := 2448562282842659228594807

theorem tailTrace_4768558 : CollatzResearch.WordTrace tailWord_4768558 prefixEnd_4768558 2448562282842659228594807 := by
  unfold tailWord_4768558
  simp only [CollatzResearch.WordTrace]
  refine ⟨21740449832292030714178291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115949065772224163808950885 21740449832292030714178291)
  ·
    refine ⟨32610674748438046071267437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21740449832292030714178291 32610674748438046071267437)
    ·
      refine ⟨12229003030664267276725289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32610674748438046071267437 12229003030664267276725289)
      ·
        refine ⟨9171752272998200457543967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12229003030664267276725289 9171752272998200457543967)
        ·
          refine ⟨13757628409497300686315951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9171752272998200457543967 13757628409497300686315951)
          ·
            refine ⟨20636442614245951029473927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13757628409497300686315951 20636442614245951029473927)
            ·
              refine ⟨30954663921368926544210891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20636442614245951029473927 30954663921368926544210891)
              ·
                refine ⟨46431995882053389816316337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30954663921368926544210891 46431995882053389816316337)
                ·
                  refine ⟨34823996911540042362237253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46431995882053389816316337 34823996911540042362237253)
                  ·
                    refine ⟨6529499420913757942919485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34823996911540042362237253 6529499420913757942919485)
                    ·
                      refine ⟨2448562282842659228594807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6529499420913757942919485 2448562282842659228594807)
                      ·
                        rfl

theorem cell23_4768558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_4768558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768558 prefixEnd_4768558 := by exact prefixLift 4768558
  have htrace : WordTrace (prefixWord ++ tailWord_4768558) baseStart_4768558 baseEnd_4768558 := by
    simpa [prefixWord, tailWord_4768558, baseEnd_4768558] using wordTrace_append hprefix tailTrace_4768558
  have hstable : (prefixWord ++ tailWord_4768558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768558).length < 2 ^ (prefixWord ++ tailWord_4768558).sum := by decide
  have hdescent : baseEnd_4768558 < baseStart_4768558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768648 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_4768648 : Nat := 118140960795 + 4768648 * 2 ^ 59
def prefixEnd_4768648 : Nat := 4983230072969 + 3 ^ 40 * 4768648 * 2
def baseEnd_4768648 : Nat := 2448608496101563876469393

theorem tailTrace_4768648 : CollatzResearch.WordTrace tailWord_4768648 prefixEnd_4768648 2448608496101563876469393 := by
  unfold tailWord_4768648
  simp only [CollatzResearch.WordTrace]
  refine ⟨86963440614005095542101299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115951254152006794056135065 86963440614005095542101299)
  ·
    refine ⟨130445160921007643313151949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86963440614005095542101299 130445160921007643313151949)
    ·
      refine ⟨48916935345377866242431981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130445160921007643313151949 48916935345377866242431981)
      ·
        refine ⟨18343850754516699840911993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48916935345377866242431981 18343850754516699840911993)
        ·
          refine ⟨13757888065887524880683995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18343850754516699840911993 13757888065887524880683995)
          ·
            refine ⟨20636832098831287321025993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13757888065887524880683995 20636832098831287321025993)
            ·
              refine ⟨15477624074123465490769495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20636832098831287321025993 15477624074123465490769495)
              ·
                refine ⟨23216436111185198236154243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15477624074123465490769495 23216436111185198236154243)
                ·
                  refine ⟨34824654166777797354231365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23216436111185198236154243 34824654166777797354231365)
                  ·
                    refine ⟨6529622656270837003918381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34824654166777797354231365 6529622656270837003918381)
                    ·
                      refine ⟨2448608496101563876469393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6529622656270837003918381 2448608496101563876469393)
                      ·
                        rfl

theorem cell23_4768648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_4768648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768648 prefixEnd_4768648 := by exact prefixLift 4768648
  have htrace : WordTrace (prefixWord ++ tailWord_4768648) baseStart_4768648 baseEnd_4768648 := by
    simpa [prefixWord, tailWord_4768648, baseEnd_4768648] using wordTrace_append hprefix tailTrace_4768648
  have hstable : (prefixWord ++ tailWord_4768648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768648).length < 2 ^ (prefixWord ++ tailWord_4768648).sum := by decide
  have hdescent : baseEnd_4768648 < baseStart_4768648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768662 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4768662 : Nat := 118140960795 + 4768662 * 2 ^ 59
def prefixEnd_4768662 : Nat := 4983230072969 + 3 ^ 40 * 4768662 * 2
def baseEnd_4768662 : Nat := 2448615684830726821694329

theorem tailTrace_4768662 : CollatzResearch.WordTrace tailWord_4768662 prefixEnd_4768662 2448615684830726821694329 := by
  unfold tailWord_4768662
  simp only [CollatzResearch.WordTrace]
  refine ⟨10870461990622466967200765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115951594566639647650141493 10870461990622466967200765)
  ·
    refine ⟨4076423246483425112700287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10870461990622466967200765 4076423246483425112700287)
    ·
      refine ⟨6114634869725137669050431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4076423246483425112700287 6114634869725137669050431)
      ·
        refine ⟨9171952304587706503575647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6114634869725137669050431 9171952304587706503575647)
        ·
          refine ⟨13757928456881559755363471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9171952304587706503575647 13757928456881559755363471)
          ·
            refine ⟨20636892685322339633045207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13757928456881559755363471 20636892685322339633045207)
            ·
              refine ⟨30955339027983509449567811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20636892685322339633045207 30955339027983509449567811)
              ·
                refine ⟨46433008541975264174351717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30955339027983509449567811 46433008541975264174351717)
                ·
                  refine ⟨8706189101620362032690947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46433008541975264174351717 8706189101620362032690947)
                  ·
                    refine ⟨13059283652430543049036421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8706189101620362032690947 13059283652430543049036421)
                    ·
                      refine ⟨2448615684830726821694329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13059283652430543049036421 2448615684830726821694329)
                      ·
                        rfl

theorem cell23_4768662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4768662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768662 prefixEnd_4768662 := by exact prefixLift 4768662
  have htrace : WordTrace (prefixWord ++ tailWord_4768662) baseStart_4768662 baseEnd_4768662 := by
    simpa [prefixWord, tailWord_4768662, baseEnd_4768662] using wordTrace_append hprefix tailTrace_4768662
  have hstable : (prefixWord ++ tailWord_4768662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768662).length < 2 ^ (prefixWord ++ tailWord_4768662).sum := by decide
  have hdescent : baseEnd_4768662 < baseStart_4768662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768681 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 3, 5]
def baseStart_4768681 : Nat := 118140960795 + 4768681 * 2 ^ 59
def prefixEnd_4768681 : Nat := 4983230072969 + 3 ^ 40 * 4768681 * 2
def baseEnd_4768681 : Nat := 816208480321054082452247

theorem tailTrace_4768681 : CollatzResearch.WordTrace tailWord_4768681 prefixEnd_4768681 816208480321054082452247 := by
  unfold tailWord_4768681
  simp only [CollatzResearch.WordTrace]
  refine ⟨173928084836890637720153897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115952056557927091813435931 173928084836890637720153897)
  ·
    refine ⟨130446063627667978290115423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173928084836890637720153897 130446063627667978290115423)
    ·
      refine ⟨195669095441501967435173135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130446063627667978290115423 195669095441501967435173135)
      ·
        refine ⟨293503643162252951152759703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195669095441501967435173135 293503643162252951152759703)
        ·
          refine ⟨440255464743379426729139555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293503643162252951152759703 440255464743379426729139555)
          ·
            refine ⟨660383197115069140093709333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440255464743379426729139555 660383197115069140093709333)
            ·
              refine ⟨30955462364768865941892625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 660383197115069140093709333 30955462364768865941892625)
              ·
                refine ⟨23216596773576649456419469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30955462364768865941892625 23216596773576649456419469)
                ·
                  refine ⟨8706223790091243546157301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23216596773576649456419469 8706223790091243546157301)
                  ·
                    refine ⟨816208480321054082452247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8706223790091243546157301 816208480321054082452247)
                    ·
                      rfl

theorem cell23_4768681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_4768681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768681 prefixEnd_4768681 := by exact prefixLift 4768681
  have htrace : WordTrace (prefixWord ++ tailWord_4768681) baseStart_4768681 baseEnd_4768681 := by
    simpa [prefixWord, tailWord_4768681, baseEnd_4768681] using wordTrace_append hprefix tailTrace_4768681
  have hstable : (prefixWord ++ tailWord_4768681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768681).length < 2 ^ (prefixWord ++ tailWord_4768681).sum := by decide
  have hdescent : baseEnd_4768681 < baseStart_4768681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768711 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 3, 6]
def baseStart_4768711 : Nat := 118140960795 + 4768711 * 2 ^ 59
def prefixEnd_4768711 : Nat := 4983230072969 + 3 ^ 40 * 4768711 * 2
def baseEnd_4768711 : Nat := 816213615127599043327201

theorem tailTrace_4768711 : CollatzResearch.WordTrace tailWord_4768711 prefixEnd_4768711 816213615127599043327201 := by
  unfold tailWord_4768711
  simp only [CollatzResearch.WordTrace]
  refine ⟨173929179026781952843745987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115952786017854635229163991 173929179026781952843745987)
  ·
    refine ⟨260893768540172929265618981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173929179026781952843745987 260893768540172929265618981)
    ·
      refine ⟨48917581601282424237303559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260893768540172929265618981 48917581601282424237303559)
      ·
        refine ⟨73376372401923636355955339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48917581601282424237303559 73376372401923636355955339)
        ·
          refine ⟨110064558602885454533933009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73376372401923636355955339 110064558602885454533933009)
          ·
            refine ⟨82548418952164090900449757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110064558602885454533933009 82548418952164090900449757)
            ·
              refine ⟨30955657107061534087668659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82548418952164090900449757 30955657107061534087668659)
              ·
                refine ⟨46433485660592301131502989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30955657107061534087668659 46433485660592301131502989)
                ·
                  refine ⟨17412557122722112924313621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46433485660592301131502989 17412557122722112924313621)
                  ·
                    refine ⟨816213615127599043327201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17412557122722112924313621 816213615127599043327201)
                    ·
                      rfl

theorem cell23_4768711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_4768711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768711 prefixEnd_4768711 := by exact prefixLift 4768711
  have htrace : WordTrace (prefixWord ++ tailWord_4768711) baseStart_4768711 baseEnd_4768711 := by
    simpa [prefixWord, tailWord_4768711, baseEnd_4768711] using wordTrace_append hprefix tailTrace_4768711
  have hstable : (prefixWord ++ tailWord_4768711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768711).length < 2 ^ (prefixWord ++ tailWord_4768711).sum := by decide
  have hdescent : baseEnd_4768711 < baseStart_4768711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768715 : List Nat := [1, 1, 1, 1, 3, 6, 3, 1, 1, 5]
def baseStart_4768715 : Nat := 118140960795 + 4768715 * 2 ^ 59
def prefixEnd_4768715 : Nat := 4983230072969 + 3 ^ 40 * 4768715 * 2
def baseEnd_4768715 : Nat := 816214299768471704777195

theorem tailTrace_4768715 : CollatzResearch.WordTrace tailWord_4768715 prefixEnd_4768715 816214299768471704777195 := by
  unfold tailWord_4768715
  simp only [CollatzResearch.WordTrace]
  refine ⟨173929324918767461526891599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115952883279178307684594399 173929324918767461526891599)
  ·
    refine ⟨260893987378151192290337399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173929324918767461526891599 260893987378151192290337399)
    ·
      refine ⟨391340981067226788435506099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260893987378151192290337399 391340981067226788435506099)
      ·
        refine ⟨587011471600840182653259149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391340981067226788435506099 587011471600840182653259149)
        ·
          refine ⟨220129301850315068494972181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 587011471600840182653259149 220129301850315068494972181)
          ·
            refine ⟨10318561024233518835701821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 220129301850315068494972181 10318561024233518835701821)
            ·
              refine ⟨3869460384087569563388183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10318561024233518835701821 3869460384087569563388183)
              ·
                refine ⟨5804190576131354345082275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3869460384087569563388183 5804190576131354345082275)
                ·
                  refine ⟨8706285864197031517623413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5804190576131354345082275 8706285864197031517623413)
                  ·
                    refine ⟨816214299768471704777195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8706285864197031517623413 816214299768471704777195)
                    ·
                      rfl

theorem cell23_4768715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 1, 5].length) (baseStart_4768715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768715 prefixEnd_4768715 := by exact prefixLift 4768715
  have htrace : WordTrace (prefixWord ++ tailWord_4768715) baseStart_4768715 baseEnd_4768715 := by
    simpa [prefixWord, tailWord_4768715, baseEnd_4768715] using wordTrace_append hprefix tailTrace_4768715
  have hstable : (prefixWord ++ tailWord_4768715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768715).length < 2 ^ (prefixWord ++ tailWord_4768715).sum := by decide
  have hdescent : baseEnd_4768715 < baseStart_4768715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768722 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_4768722 : Nat := 118140960795 + 4768722 * 2 ^ 59
def prefixEnd_4768722 : Nat := 4983230072969 + 3 ^ 40 * 4768722 * 2
def baseEnd_4768722 : Nat := 2448646493669996586944053

theorem tailTrace_4768722 : CollatzResearch.WordTrace tailWord_4768722 prefixEnd_4768722 2448646493669996586944053 := by
  unfold tailWord_4768722
  simp only [CollatzResearch.WordTrace]
  refine ⟨43482395057435525430599105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115953053486494734481597613 43482395057435525430599105)
  ·
    refine ⟨32611796293076644072949329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43482395057435525430599105 32611796293076644072949329)
    ·
      refine ⟨24458847219807483054711997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32611796293076644072949329 24458847219807483054711997)
      ·
        refine ⟨9172067707427806145516999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24458847219807483054711997 9172067707427806145516999)
        ·
          refine ⟨13758101561141709218275499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9172067707427806145516999 13758101561141709218275499)
          ·
            refine ⟨20637152341712563827413249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13758101561141709218275499 20637152341712563827413249)
            ·
              refine ⟨15477864256284422870559937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20637152341712563827413249 15477864256284422870559937)
              ·
                refine ⟨11608398192213317152919953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15477864256284422870559937 11608398192213317152919953)
                ·
                  refine ⟨8706298644159987864689965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11608398192213317152919953 8706298644159987864689965)
                  ·
                    refine ⟨3264861991559995449258737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8706298644159987864689965 3264861991559995449258737)
                    ·
                      refine ⟨2448646493669996586944053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3264861991559995449258737 2448646493669996586944053)
                      ·
                        rfl

theorem cell23_4768722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_4768722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768722 prefixEnd_4768722 := by exact prefixLift 4768722
  have htrace : WordTrace (prefixWord ++ tailWord_4768722) baseStart_4768722 baseEnd_4768722 := by
    simpa [prefixWord, tailWord_4768722, baseEnd_4768722] using wordTrace_append hprefix tailTrace_4768722
  have hstable : (prefixWord ++ tailWord_4768722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768722).length < 2 ^ (prefixWord ++ tailWord_4768722).sum := by decide
  have hdescent : baseEnd_4768722 < baseStart_4768722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768729 : List Nat := [1, 2, 1, 2, 5, 1, 4, 2, 1, 1, 3]
def baseStart_4768729 : Nat := 118140960795 + 4768729 * 2 ^ 59
def prefixEnd_4768729 : Nat := 4983230072969 + 3 ^ 40 * 4768729 * 2
def baseEnd_4768729 : Nat := 2448650088034578059556521

theorem tailTrace_4768729 : CollatzResearch.WordTrace tailWord_4768729 prefixEnd_4768729 2448650088034578059556521 := by
  unfold tailWord_4768729
  simp only [CollatzResearch.WordTrace]
  refine ⟨173929835540716741917901241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115953223693811161278600827 173929835540716741917901241)
  ·
    refine ⟨130447376655537556438425931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173929835540716741917901241 130447376655537556438425931)
    ·
      refine ⟨195671064983306334657638897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130447376655537556438425931 195671064983306334657638897)
      ·
        refine ⟨146753298737479750993229173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195671064983306334657638897 146753298737479750993229173)
        ·
          refine ⟨13758121756638726655615235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146753298737479750993229173 13758121756638726655615235)
          ·
            refine ⟨20637182634958089983422853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13758121756638726655615235 20637182634958089983422853)
            ·
              refine ⟨3869471744054641871891785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20637182634958089983422853 3869471744054641871891785)
              ·
                refine ⟨2902103808040981403918839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3869471744054641871891785 2902103808040981403918839)
                ·
                  refine ⟨4353155712061472105878259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902103808040981403918839 4353155712061472105878259)
                  ·
                    refine ⟨6529733568092208158817389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4353155712061472105878259 6529733568092208158817389)
                    ·
                      refine ⟨2448650088034578059556521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6529733568092208158817389 2448650088034578059556521)
                      ·
                        rfl

theorem cell23_4768729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 1, 1, 3].length) (baseStart_4768729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768729 prefixEnd_4768729 := by exact prefixLift 4768729
  have htrace : WordTrace (prefixWord ++ tailWord_4768729) baseStart_4768729 baseEnd_4768729 := by
    simpa [prefixWord, tailWord_4768729, baseEnd_4768729] using wordTrace_append hprefix tailTrace_4768729
  have hstable : (prefixWord ++ tailWord_4768729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768729).length < 2 ^ (prefixWord ++ tailWord_4768729).sum := by decide
  have hdescent : baseEnd_4768729 < baseStart_4768729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768766 : List Nat := [4, 2, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_4768766 : Nat := 118140960795 + 4768766 * 2 ^ 59
def prefixEnd_4768766 : Nat := 4983230072969 + 3 ^ 40 * 4768766 * 2
def baseEnd_4768766 : Nat := 816223028939598138264617

theorem tailTrace_4768766 : CollatzResearch.WordTrace tailWord_4768766 prefixEnd_4768766 816223028939598138264617 := by
  unfold tailWord_4768766
  simp only [CollatzResearch.WordTrace]
  refine ⟨21741398130197837154624769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115954123361055131491332101 21741398130197837154624769)
  ·
    refine ⟨16306048597648377865968577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21741398130197837154624769 16306048597648377865968577)
    ·
      refine ⟨12229536448236283399476433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16306048597648377865968577 12229536448236283399476433)
      ·
        refine ⟨9172152336177212549607325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12229536448236283399476433 9172152336177212549607325)
        ·
          refine ⟨3439557126066454706102747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9172152336177212549607325 3439557126066454706102747)
          ·
            refine ⟨5159335689099682059154121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439557126066454706102747 5159335689099682059154121)
            ·
              refine ⟨3869501766824761544365591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5159335689099682059154121 3869501766824761544365591)
              ·
                refine ⟨5804252650237142316548387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3869501766824761544365591 5804252650237142316548387)
                ·
                  refine ⟨8706378975355713474822581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5804252650237142316548387 8706378975355713474822581)
                  ·
                    refine ⟨816223028939598138264617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8706378975355713474822581 816223028939598138264617)
                    ·
                      rfl

theorem cell23_4768766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_4768766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768766 prefixEnd_4768766 := by exact prefixLift 4768766
  have htrace : WordTrace (prefixWord ++ tailWord_4768766) baseStart_4768766 baseEnd_4768766 := by
    simpa [prefixWord, tailWord_4768766, baseEnd_4768766] using wordTrace_append hprefix tailTrace_4768766
  have hstable : (prefixWord ++ tailWord_4768766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768766).length < 2 ^ (prefixWord ++ tailWord_4768766).sum := by decide
  have hdescent : baseEnd_4768766 < baseStart_4768766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768769 : List Nat := [1, 2, 4, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_4768769 : Nat := 118140960795 + 4768769 * 2 ^ 59
def prefixEnd_4768769 : Nat := 4983230072969 + 3 ^ 40 * 4768769 * 2
def baseEnd_4768769 : Nat := 2448670627260757903056337

theorem tailTrace_4768769 : CollatzResearch.WordTrace tailWord_4768769 prefixEnd_4768769 2448670627260757903056337 := by
  unfold tailWord_4768769
  simp only [CollatzResearch.WordTrace]
  refine ⟨173931294460571828749357361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115954196307047885832904907 173931294460571828749357361)
  ·
    refine ⟨130448470845428871562018021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173931294460571828749357361 130448470845428871562018021)
    ·
      refine ⟨24459088283517913417878379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130448470845428871562018021 24459088283517913417878379)
      ·
        refine ⟨36688632425276870126817569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24459088283517913417878379 36688632425276870126817569)
        ·
          refine ⟨27516474318957652595113177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36688632425276870126817569 27516474318957652595113177)
          ·
            refine ⟨20637355739218239446334883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27516474318957652595113177 20637355739218239446334883)
            ·
              refine ⟨30956033608827359169502325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20637355739218239446334883 30956033608827359169502325)
              ·
                refine ⟨2902128150827564922140843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30956033608827359169502325 2902128150827564922140843)
                ·
                  refine ⟨4353192226241347383211265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902128150827564922140843 4353192226241347383211265)
                  ·
                    refine ⟨3264894169681010537408449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4353192226241347383211265 3264894169681010537408449)
                    ·
                      refine ⟨2448670627260757903056337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3264894169681010537408449 2448670627260757903056337)
                      ·
                        rfl

theorem cell23_4768769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_4768769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768769 prefixEnd_4768769 := by exact prefixLift 4768769
  have htrace : WordTrace (prefixWord ++ tailWord_4768769) baseStart_4768769 baseEnd_4768769 := by
    simpa [prefixWord, tailWord_4768769, baseEnd_4768769] using wordTrace_append hprefix tailTrace_4768769
  have hstable : (prefixWord ++ tailWord_4768769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768769).length < 2 ^ (prefixWord ++ tailWord_4768769).sum := by decide
  have hdescent : baseEnd_4768769 < baseStart_4768769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768802 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_4768802 : Nat := 118140960795 + 4768802 * 2 ^ 59
def prefixEnd_4768802 : Nat := 4983230072969 + 3 ^ 40 * 4768802 * 2
def baseEnd_4768802 : Nat := 2448687572122356273943685

theorem tailTrace_4768802 : CollatzResearch.WordTrace tailWord_4768802 prefixEnd_4768802 2448687572122356273943685 := by
  unfold tailWord_4768802
  simp only [CollatzResearch.WordTrace]
  refine ⟨43483124517363068846327165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115954998712968183590205773 43483124517363068846327165)
  ·
    refine ⟨16306171694011150817372687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43483124517363068846327165 16306171694011150817372687)
    ·
      refine ⟨24459257541016726226059031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16306171694011150817372687 24459257541016726226059031)
      ·
        refine ⟨36688886311525089339088547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24459257541016726226059031 36688886311525089339088547)
        ·
          refine ⟨55033329467287634008632821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36688886311525089339088547 55033329467287634008632821)
          ·
            refine ⟨5159374637558215688309327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55033329467287634008632821 5159374637558215688309327)
            ·
              refine ⟨7739061956337323532463991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159374637558215688309327 7739061956337323532463991)
              ·
                refine ⟨11608592934505985298695987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7739061956337323532463991 11608592934505985298695987)
                ·
                  refine ⟨17412889401758977948043981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11608592934505985298695987 17412889401758977948043981)
                  ·
                    refine ⟨6529833525659616730516493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17412889401758977948043981 6529833525659616730516493)
                    ·
                      refine ⟨2448687572122356273943685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6529833525659616730516493 2448687572122356273943685)
                      ·
                        rfl

theorem cell23_4768802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_4768802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768802 prefixEnd_4768802 := by exact prefixLift 4768802
  have htrace : WordTrace (prefixWord ++ tailWord_4768802) baseStart_4768802 baseEnd_4768802 := by
    simpa [prefixWord, tailWord_4768802, baseEnd_4768802] using wordTrace_append hprefix tailTrace_4768802
  have hstable : (prefixWord ++ tailWord_4768802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768802).length < 2 ^ (prefixWord ++ tailWord_4768802).sum := by decide
  have hdescent : baseEnd_4768802 < baseStart_4768802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768812 : List Nat := [2, 2, 1, 1, 1, 2, 6, 2, 1, 3, 2]
def baseStart_4768812 : Nat := 118140960795 + 4768812 * 2 ^ 59
def prefixEnd_4768812 : Nat := 4983230072969 + 3 ^ 40 * 4768812 * 2
def baseEnd_4768812 : Nat := 2448692706928901234818639

theorem tailTrace_4768812 : CollatzResearch.WordTrace tailWord_4768812 prefixEnd_4768812 2448692706928901234818639 := by
  unfold tailWord_4768812
  simp only [CollatzResearch.WordTrace]
  refine ⟨86966431399708023546586345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115955241866277364728781793 86966431399708023546586345)
  ·
    refine ⟨65224823549781017659939759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86966431399708023546586345 65224823549781017659939759)
    ·
      refine ⟨97837235324671526489909639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65224823549781017659939759 97837235324671526489909639)
      ·
        refine ⟨146755852987007289734864459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97837235324671526489909639 146755852987007289734864459)
        ·
          refine ⟨220133779480510934602296689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146755852987007289734864459 220133779480510934602296689)
          ·
            refine ⟨165100334610383200951722517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220133779480510934602296689 165100334610383200951722517)
            ·
              refine ⟨7739078184861712544611993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 165100334610383200951722517 7739078184861712544611993)
              ·
                refine ⟨5804308638646284408458995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7739078184861712544611993 5804308638646284408458995)
                ·
                  refine ⟨8706462957969426612688493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5804308638646284408458995 8706462957969426612688493)
                  ·
                    refine ⟨3264923609238534979758185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8706462957969426612688493 3264923609238534979758185)
                    ·
                      refine ⟨2448692706928901234818639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3264923609238534979758185 2448692706928901234818639)
                      ·
                        rfl

theorem cell23_4768812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 3, 2].length) (baseStart_4768812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768812 prefixEnd_4768812 := by exact prefixLift 4768812
  have htrace : WordTrace (prefixWord ++ tailWord_4768812) baseStart_4768812 baseEnd_4768812 := by
    simpa [prefixWord, tailWord_4768812, baseEnd_4768812] using wordTrace_append hprefix tailTrace_4768812
  have hstable : (prefixWord ++ tailWord_4768812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768812).length < 2 ^ (prefixWord ++ tailWord_4768812).sum := by decide
  have hdescent : baseEnd_4768812 < baseStart_4768812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768828 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_4768828 : Nat := 118140960795 + 4768828 * 2 ^ 59
def prefixEnd_4768828 : Nat := 4983230072969 + 3 ^ 40 * 4768828 * 2
def baseEnd_4768828 : Nat := 2448700922619373172218565

theorem tailTrace_4768828 : CollatzResearch.WordTrace tailWord_4768828 prefixEnd_4768828 2448700922619373172218565 := by
  unfold tailWord_4768828
  simp only [CollatzResearch.WordTrace]
  refine ⟨86966723183679040912877569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115955630911572054550503425 86966723183679040912877569)
  ·
    refine ⟨65225042387759280684658177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86966723183679040912877569 65225042387759280684658177)
    ·
      refine ⟨48918781790819460513493633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65225042387759280684658177 48918781790819460513493633)
      ·
        refine ⟨36689086343114595385120225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48918781790819460513493633 36689086343114595385120225)
        ·
          refine ⟨27516814757335946538840169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36689086343114595385120225 27516814757335946538840169)
          ·
            refine ⟨20637611068001959904130127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27516814757335946538840169 20637611068001959904130127)
            ·
              refine ⟨30956416602002939856195191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20637611068001959904130127 30956416602002939856195191)
              ·
                refine ⟨46434624903004409784292787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30956416602002939856195191 46434624903004409784292787)
                ·
                  refine ⟨69651937354506614676439181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46434624903004409784292787 69651937354506614676439181)
                  ·
                    refine ⟨26119476507939980503664693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69651937354506614676439181 26119476507939980503664693)
                    ·
                      refine ⟨2448700922619373172218565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26119476507939980503664693 2448700922619373172218565)
                      ·
                        rfl

theorem cell23_4768828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_4768828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768828 prefixEnd_4768828 := by exact prefixLift 4768828
  have htrace : WordTrace (prefixWord ++ tailWord_4768828) baseStart_4768828 baseEnd_4768828 := by
    simpa [prefixWord, tailWord_4768828, baseEnd_4768828] using wordTrace_append hprefix tailTrace_4768828
  have hstable : (prefixWord ++ tailWord_4768828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768828).length < 2 ^ (prefixWord ++ tailWord_4768828).sum := by decide
  have hdescent : baseEnd_4768828 < baseStart_4768828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768842 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 4, 2, 2]
def baseStart_4768842 : Nat := 118140960795 + 4768842 * 2 ^ 59
def prefixEnd_4768842 : Nat := 4983230072969 + 3 ^ 40 * 4768842 * 2
def baseEnd_4768842 : Nat := 2448708111348536117443501

theorem tailTrace_4768842 : CollatzResearch.WordTrace tailWord_4768842 prefixEnd_4768842 2448708111348536117443501 := by
  unfold tailWord_4768842
  simp only [CollatzResearch.WordTrace]
  refine ⟨43483489247326840554191195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115955971326204908144509853 43483489247326840554191195)
  ·
    refine ⟨65225233870990260831286793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43483489247326840554191195 65225233870990260831286793)
    ·
      refine ⟨48918925403242695623465095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65225233870990260831286793 48918925403242695623465095)
      ·
        refine ⟨73378388104864043435197643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48918925403242695623465095 73378388104864043435197643)
        ·
          refine ⟨110067582157296065152796465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73378388104864043435197643 110067582157296065152796465)
          ·
            refine ⟨82550686617972048864597349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110067582157296065152796465 82550686617972048864597349)
            ·
              refine ⟨15478253740869759162112003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82550686617972048864597349 15478253740869759162112003)
              ·
                refine ⟨23217380611304638743168005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15478253740869759162112003 23217380611304638743168005)
                ·
                  refine ⟨4353258864619619764344001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23217380611304638743168005 4353258864619619764344001)
                  ·
                    refine ⟨3264944148464714823258001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4353258864619619764344001 3264944148464714823258001)
                    ·
                      refine ⟨2448708111348536117443501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3264944148464714823258001 2448708111348536117443501)
                      ·
                        rfl

theorem cell23_4768842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_4768842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768842 prefixEnd_4768842 := by exact prefixLift 4768842
  have htrace : WordTrace (prefixWord ++ tailWord_4768842) baseStart_4768842 baseEnd_4768842 := by
    simpa [prefixWord, tailWord_4768842, baseEnd_4768842] using wordTrace_append hprefix tailTrace_4768842
  have hstable : (prefixWord ++ tailWord_4768842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768842).length < 2 ^ (prefixWord ++ tailWord_4768842).sum := by decide
  have hdescent : baseEnd_4768842 < baseStart_4768842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768888 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_4768888 : Nat := 118140960795 + 4768888 * 2 ^ 59
def prefixEnd_4768888 : Nat := 4983230072969 + 3 ^ 40 * 4768888 * 2
def baseEnd_4768888 : Nat := 2448731731458642937468289

theorem tailTrace_4768888 : CollatzResearch.WordTrace tailWord_4768888 prefixEnd_4768888 2448731731458642937468289 := by
  unfold tailWord_4768888
  simp only [CollatzResearch.WordTrace]
  refine ⟨86967817373570356036469659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115957089831427141381959545 86967817373570356036469659)
  ·
    refine ⟨130451726060355534054704489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86967817373570356036469659 130451726060355534054704489)
    ·
      refine ⟨97838794545266650541028367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130451726060355534054704489 97838794545266650541028367)
      ·
        refine ⟨146758191817899975811542551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97838794545266650541028367 146758191817899975811542551)
        ·
          refine ⟨220137287726849963717313827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146758191817899975811542551 220137287726849963717313827)
          ·
            refine ⟨330205931590274945575970741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220137287726849963717313827 330205931590274945575970741)
            ·
              refine ⟨30956806086588276147747257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 330205931590274945575970741 30956806086588276147747257)
              ·
                refine ⟨23217604564941207110810443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30956806086588276147747257 23217604564941207110810443)
                ·
                  refine ⟨34826406847411810666215665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23217604564941207110810443 34826406847411810666215665)
                  ·
                    refine ⟨26119805135558857999661749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34826406847411810666215665 26119805135558857999661749)
                    ·
                      refine ⟨2448731731458642937468289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26119805135558857999661749 2448731731458642937468289)
                      ·
                        rfl

theorem cell23_4768888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_4768888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768888 prefixEnd_4768888 := by exact prefixLift 4768888
  have htrace : WordTrace (prefixWord ++ tailWord_4768888) baseStart_4768888 baseEnd_4768888 := by
    simpa [prefixWord, tailWord_4768888, baseEnd_4768888] using wordTrace_append hprefix tailTrace_4768888
  have hstable : (prefixWord ++ tailWord_4768888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768888).length < 2 ^ (prefixWord ++ tailWord_4768888).sum := by decide
  have hdescent : baseEnd_4768888 < baseStart_4768888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768915 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 1, 6, 2]
def baseStart_4768915 : Nat := 118140960795 + 4768915 * 2 ^ 59
def prefixEnd_4768915 : Nat := 4983230072969 + 3 ^ 40 * 4768915 * 2
def baseEnd_4768915 : Nat := 2448745595436314331830665

theorem tailTrace_4768915 : CollatzResearch.WordTrace tailWord_4768915 prefixEnd_4768915 2448745595436314331830665 := by
  unfold tailWord_4768915
  simp only [CollatzResearch.WordTrace]
  refine ⟨173936619518042895684172199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115957746345361930456114799 173936619518042895684172199)
  ·
    refine ⟨260904929277064343526258299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173936619518042895684172199 260904929277064343526258299)
    ·
      refine ⟨391357393915596515289387449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260904929277064343526258299 391357393915596515289387449)
      ·
        refine ⟨293518045436697386467040587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391357393915596515289387449 293518045436697386467040587)
        ·
          refine ⟨440277068155046079700560881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293518045436697386467040587 440277068155046079700560881)
          ·
            refine ⟨330207801116284559775420661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440277068155046079700560881 330207801116284559775420661)
            ·
              refine ⟨30956981354651677478945687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 330207801116284559775420661 30956981354651677478945687)
              ·
                refine ⟨46435472031977516218418531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30956981354651677478945687 46435472031977516218418531)
                ·
                  refine ⟨69653208047966274327627797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46435472031977516218418531 69653208047966274327627797)
                  ·
                    refine ⟨3264994127248419109107553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69653208047966274327627797 3264994127248419109107553)
                    ·
                      refine ⟨2448745595436314331830665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3264994127248419109107553 2448745595436314331830665)
                      ·
                        rfl

theorem cell23_4768915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 6, 2].length) (baseStart_4768915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768915 prefixEnd_4768915 := by exact prefixLift 4768915
  have htrace : WordTrace (prefixWord ++ tailWord_4768915) baseStart_4768915 baseEnd_4768915 := by
    simpa [prefixWord, tailWord_4768915, baseEnd_4768915] using wordTrace_append hprefix tailTrace_4768915
  have hstable : (prefixWord ++ tailWord_4768915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768915).length < 2 ^ (prefixWord ++ tailWord_4768915).sum := by decide
  have hdescent : baseEnd_4768915 < baseStart_4768915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768932 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_4768932 : Nat := 118140960795 + 4768932 * 2 ^ 59
def prefixEnd_4768932 : Nat := 4983230072969 + 3 ^ 40 * 4768932 * 2
def baseEnd_4768932 : Nat := 2448754324607440765318087

theorem tailTrace_4768932 : CollatzResearch.WordTrace tailWord_4768932 prefixEnd_4768932 2448754324607440765318087 := by
  unfold tailWord_4768932
  simp only [CollatzResearch.WordTrace]
  refine ⟨86968619779490653793770525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115958159705987538391694033 86968619779490653793770525)
  ·
    refine ⟨32613232417308995172663947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86968619779490653793770525 32613232417308995172663947)
    ·
      refine ⟨48919848625963492758995921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32613232417308995172663947 48919848625963492758995921)
      ·
        refine ⟨36689886469472619569246941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48919848625963492758995921 36689886469472619569246941)
        ·
          refine ⟨13758707426052232338467603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36689886469472619569246941 13758707426052232338467603)
          ·
            refine ⟨20638061139078348507701405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13758707426052232338467603 20638061139078348507701405)
            ·
              refine ⟨7739272927154380690388027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20638061139078348507701405 7739272927154380690388027)
              ·
                refine ⟨11608909390731571035582041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7739272927154380690388027 11608909390731571035582041)
                ·
                  refine ⟨8706682043048678276686531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11608909390731571035582041 8706682043048678276686531)
                  ·
                    refine ⟨13060023064573017415029797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8706682043048678276686531 13060023064573017415029797)
                    ·
                      refine ⟨2448754324607440765318087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13060023064573017415029797 2448754324607440765318087)
                      ·
                        rfl

theorem cell23_4768932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_4768932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768932 prefixEnd_4768932 := by exact prefixLift 4768932
  have htrace : WordTrace (prefixWord ++ tailWord_4768932) baseStart_4768932 baseEnd_4768932 := by
    simpa [prefixWord, tailWord_4768932, baseEnd_4768932] using wordTrace_append hprefix tailTrace_4768932
  have hstable : (prefixWord ++ tailWord_4768932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768932).length < 2 ^ (prefixWord ++ tailWord_4768932).sum := by decide
  have hdescent : baseEnd_4768932 < baseStart_4768932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768945 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4768945 : Nat := 118140960795 + 4768945 * 2 ^ 59
def prefixEnd_4768945 : Nat := 4983230072969 + 3 ^ 40 * 4768945 * 2
def baseEnd_4768945 : Nat := 2448760999855949214455527

theorem tailTrace_4768945 : CollatzResearch.WordTrace tailWord_4768945 prefixEnd_4768945 2448760999855949214455527 := by
  unfold tailWord_4768945
  simp only [CollatzResearch.WordTrace]
  refine ⟨173937713707934210807764289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115958475805289473871842859 173937713707934210807764289)
  ·
    refine ⟨130453285280950658105823217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173937713707934210807764289 130453285280950658105823217)
    ·
      refine ⟨97839963960712993579367413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130453285280950658105823217 97839963960712993579367413)
      ·
        refine ⟨9172496621316843148065695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97839963960712993579367413 9172496621316843148065695)
        ·
          refine ⟨13758744931975264722098543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9172496621316843148065695 13758744931975264722098543)
          ·
            refine ⟨20638117397962897083147815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13758744931975264722098543 20638117397962897083147815)
            ·
              refine ⟨30957176096944345624721723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20638117397962897083147815 30957176096944345624721723)
              ·
                refine ⟨46435764145416518437082585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30957176096944345624721723 46435764145416518437082585)
                ·
                  refine ⟨34826823109062388827811939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46435764145416518437082585 34826823109062388827811939)
                  ·
                    refine ⟨52240234663593583241717909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34826823109062388827811939 52240234663593583241717909)
                    ·
                      refine ⟨2448760999855949214455527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52240234663593583241717909 2448760999855949214455527)
                      ·
                        rfl

theorem cell23_4768945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4768945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768945 prefixEnd_4768945 := by exact prefixLift 4768945
  have htrace : WordTrace (prefixWord ++ tailWord_4768945) baseStart_4768945 baseEnd_4768945 := by
    simpa [prefixWord, tailWord_4768945, baseEnd_4768945] using wordTrace_append hprefix tailTrace_4768945
  have hstable : (prefixWord ++ tailWord_4768945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768945).length < 2 ^ (prefixWord ++ tailWord_4768945).sum := by decide
  have hdescent : baseEnd_4768945 < baseStart_4768945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4768992 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 1, 5, 2]
def baseStart_4768992 : Nat := 118140960795 + 4768992 * 2 ^ 59
def prefixEnd_4768992 : Nat := 4983230072969 + 3 ^ 40 * 4768992 * 2
def baseEnd_4768992 : Nat := 2448785133446710530567811

theorem tailTrace_4768992 : CollatzResearch.WordTrace tailWord_4768992 prefixEnd_4768992 2448785133446710530567811 := by
  unfold tailWord_4768992
  simp only [CollatzResearch.WordTrace]
  refine ⟨86969713969381968917362615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115959618625842625223150153 86969713969381968917362615)
  ·
    refine ⟨130454570954072953376043923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86969713969381968917362615 130454570954072953376043923)
    ·
      refine ⟨195681856431109430064065885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130454570954072953376043923 195681856431109430064065885)
      ·
        refine ⟨73380696161666036274024707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195681856431109430064065885 73380696161666036274024707)
        ·
          refine ⟨110071044242499054411037061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73380696161666036274024707 110071044242499054411037061)
          ·
            refine ⟨20638320795468572702069449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110071044242499054411037061 20638320795468572702069449)
            ·
              refine ⟨15478740596601429526552087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20638320795468572702069449 15478740596601429526552087)
              ·
                refine ⟨23218110894902144289828131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15478740596601429526552087 23218110894902144289828131)
                ·
                  refine ⟨34827166342353216434742197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23218110894902144289828131 34827166342353216434742197)
                  ·
                    refine ⟨3265046844595614040757081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34827166342353216434742197 3265046844595614040757081)
                    ·
                      refine ⟨2448785133446710530567811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3265046844595614040757081 2448785133446710530567811)
                      ·
                        rfl

theorem cell23_4768992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_4768992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4768992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4768992 prefixEnd_4768992 := by exact prefixLift 4768992
  have htrace : WordTrace (prefixWord ++ tailWord_4768992) baseStart_4768992 baseEnd_4768992 := by
    simpa [prefixWord, tailWord_4768992, baseEnd_4768992] using wordTrace_append hprefix tailTrace_4768992
  have hstable : (prefixWord ++ tailWord_4768992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4768992).length < 2 ^ (prefixWord ++ tailWord_4768992).sum := by decide
  have hdescent : baseEnd_4768992 < baseStart_4768992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4768992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769002 : List Nat := [3, 1, 3, 1, 1, 3, 2, 3, 1, 5]
def baseStart_4769002 : Nat := 118140960795 + 4769002 * 2 ^ 59
def prefixEnd_4769002 : Nat := 4983230072969 + 3 ^ 40 * 4769002 * 2
def baseEnd_4769002 : Nat := 816263422751085163814255

theorem tailTrace_4769002 : CollatzResearch.WordTrace tailWord_4769002 prefixEnd_4769002 816263422751085163814255 := by
  unfold tailWord_4769002
  simp only [CollatzResearch.WordTrace]
  refine ⟨43484948167181927385647315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115959861779151806361726173 43484948167181927385647315)
  ·
    refine ⟨65227422250772891078470973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43484948167181927385647315 65227422250772891078470973)
    ·
      refine ⟨24460283344039834154426615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65227422250772891078470973 24460283344039834154426615)
      ·
        refine ⟨36690425016059751231639923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24460283344039834154426615 36690425016059751231639923)
        ·
          refine ⟨55035637524089626847459885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36690425016059751231639923 55035637524089626847459885)
          ·
            refine ⟨20638364071533610067797457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55035637524089626847459885 20638364071533610067797457)
            ·
              refine ⟨15478773053650207550848093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20638364071533610067797457 15478773053650207550848093)
              ·
                refine ⟨5804539895118827831568035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15478773053650207550848093 5804539895118827831568035)
                ·
                  refine ⟨8706809842678241747352053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5804539895118827831568035 8706809842678241747352053)
                  ·
                    refine ⟨816263422751085163814255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8706809842678241747352053 816263422751085163814255)
                    ·
                      rfl

theorem cell23_4769002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_4769002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769002 prefixEnd_4769002 := by exact prefixLift 4769002
  have htrace : WordTrace (prefixWord ++ tailWord_4769002) baseStart_4769002 baseEnd_4769002 := by
    simpa [prefixWord, tailWord_4769002, baseEnd_4769002] using wordTrace_append hprefix tailTrace_4769002
  have hstable : (prefixWord ++ tailWord_4769002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769002).length < 2 ^ (prefixWord ++ tailWord_4769002).sum := by decide
  have hdescent : baseEnd_4769002 < baseStart_4769002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769035 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 6]
def baseStart_4769035 : Nat := 118140960795 + 4769035 * 2 ^ 59
def prefixEnd_4769035 : Nat := 4983230072969 + 3 ^ 40 * 4769035 * 2
def baseEnd_4769035 : Nat := 2448807213114853862330113

theorem tailTrace_4769035 : CollatzResearch.WordTrace tailWord_4769035 prefixEnd_4769035 2448807213114853862330113 := by
  unfold tailWord_4769035
  simp only [CollatzResearch.WordTrace]
  refine ⟨173940996277608156178540559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115960664185072104119027039 173940996277608156178540559)
  ·
    refine ⟨260911494416412234267810839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173940996277608156178540559 260911494416412234267810839)
    ·
      refine ⟨391367241624618351401716259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260911494416412234267810839 391367241624618351401716259)
      ·
        refine ⟨587050862436927527102574389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391367241624618351401716259 587050862436927527102574389)
        ·
          refine ⟨55036018353461955665866349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 587050862436927527102574389 55036018353461955665866349)
          ·
            refine ⟨20638506882548233374699881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55036018353461955665866349 20638506882548233374699881)
            ·
              refine ⟨15478880161911175031024911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20638506882548233374699881 15478880161911175031024911)
              ·
                refine ⟨23218320242866762546537367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15478880161911175031024911 23218320242866762546537367)
                ·
                  refine ⟨34827480364300143819806051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23218320242866762546537367 34827480364300143819806051)
                  ·
                    refine ⟨52241220546450215729709077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34827480364300143819806051 52241220546450215729709077)
                    ·
                      refine ⟨2448807213114853862330113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52241220546450215729709077 2448807213114853862330113)
                      ·
                        rfl

theorem cell23_4769035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 6].length) (baseStart_4769035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769035 prefixEnd_4769035 := by exact prefixLift 4769035
  have htrace : WordTrace (prefixWord ++ tailWord_4769035) baseStart_4769035 baseEnd_4769035 := by
    simpa [prefixWord, tailWord_4769035, baseEnd_4769035] using wordTrace_append hprefix tailTrace_4769035
  have hstable : (prefixWord ++ tailWord_4769035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769035).length < 2 ^ (prefixWord ++ tailWord_4769035).sum := by decide
  have hdescent : baseEnd_4769035 < baseStart_4769035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769056 : List Nat := [2, 1, 1, 5, 3, 1, 3, 1, 1, 1, 4]
def baseStart_4769056 : Nat := 118140960795 + 4769056 * 2 ^ 59
def prefixEnd_4769056 : Nat := 4983230072969 + 3 ^ 40 * 4769056 * 2
def baseEnd_4769056 : Nat := 2448817996208598280167517

theorem tailTrace_4769056 : CollatzResearch.WordTrace tailWord_4769056 prefixEnd_4769056 2448817996208598280167517 := by
  unfold tailWord_4769056
  simp only [CollatzResearch.WordTrace]
  refine ⟨86970881105266038382527511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115961174807021384510036681 86970881105266038382527511)
  ·
    refine ⟨130456321657899057573791267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86970881105266038382527511 130456321657899057573791267)
    ·
      refine ⟨195684482486848586360686901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130456321657899057573791267 195684482486848586360686901)
      ·
        refine ⟨18345420233142054971314397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 195684482486848586360686901 18345420233142054971314397)
        ·
          refine ⟨6879532587428270614242899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18345420233142054971314397 6879532587428270614242899)
          ·
            refine ⟨10319298881142405921364349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6879532587428270614242899 10319298881142405921364349)
            ·
              refine ⟨3869737080428402220511631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10319298881142405921364349 3869737080428402220511631)
              ·
                refine ⟨5804605620642603330767447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3869737080428402220511631 5804605620642603330767447)
                ·
                  refine ⟨8706908430963904996151171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5804605620642603330767447 8706908430963904996151171)
                  ·
                    refine ⟨13060362646445857494226757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8706908430963904996151171 13060362646445857494226757)
                    ·
                      refine ⟨2448817996208598280167517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13060362646445857494226757 2448817996208598280167517)
                      ·
                        rfl

theorem cell23_4769056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_4769056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769056 prefixEnd_4769056 := by exact prefixLift 4769056
  have htrace : WordTrace (prefixWord ++ tailWord_4769056) baseStart_4769056 baseEnd_4769056 := by
    simpa [prefixWord, tailWord_4769056, baseEnd_4769056] using wordTrace_append hprefix tailTrace_4769056
  have hstable : (prefixWord ++ tailWord_4769056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769056).length < 2 ^ (prefixWord ++ tailWord_4769056).sum := by decide
  have hdescent : baseEnd_4769056 < baseStart_4769056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769066 : List Nat := [3, 1, 4, 2, 1, 2, 2, 2, 2, 4]
def baseStart_4769066 : Nat := 118140960795 + 4769066 * 2 ^ 59
def prefixEnd_4769066 : Nat := 4983230072969 + 3 ^ 40 * 4769066 * 2
def baseEnd_4769066 : Nat := 816274377005047747014157

theorem tailTrace_4769066 : CollatzResearch.WordTrace tailWord_4769066 prefixEnd_4769066 816274377005047747014157 := by
  unfold tailWord_4769066
  simp only [CollatzResearch.WordTrace]
  refine ⟨43485531735123962118229763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115961417960330565648612701 43485531735123962118229763)
  ·
    refine ⟨65228297602685943177344645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43485531735123962118229763 65228297602685943177344645)
    ·
      refine ⟨12230305800503614345752121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65228297602685943177344645 12230305800503614345752121)
      ·
        refine ⟨9172729350377710759314091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12230305800503614345752121 9172729350377710759314091)
        ·
          refine ⟨13759094025566566138971137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9172729350377710759314091 13759094025566566138971137)
          ·
            refine ⟨10319320519174924604228353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13759094025566566138971137 10319320519174924604228353)
            ·
              refine ⟨7739490389381193453171265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10319320519174924604228353 7739490389381193453171265)
              ·
                refine ⟨5804617792035895089878449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7739490389381193453171265 5804617792035895089878449)
                ·
                  refine ⟨4353463344026921317408837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5804617792035895089878449 4353463344026921317408837)
                  ·
                    refine ⟨816274377005047747014157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4353463344026921317408837 816274377005047747014157)
                    ·
                      rfl

theorem cell23_4769066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_4769066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769066 prefixEnd_4769066 := by exact prefixLift 4769066
  have htrace : WordTrace (prefixWord ++ tailWord_4769066) baseStart_4769066 baseEnd_4769066 := by
    simpa [prefixWord, tailWord_4769066, baseEnd_4769066] using wordTrace_append hprefix tailTrace_4769066
  have hstable : (prefixWord ++ tailWord_4769066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769066).length < 2 ^ (prefixWord ++ tailWord_4769066).sum := by decide
  have hdescent : baseEnd_4769066 < baseStart_4769066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769073 : List Nat := [1, 2, 2, 3, 3, 2, 1, 4, 1, 2, 2]
def baseStart_4769073 : Nat := 118140960795 + 4769073 * 2 ^ 59
def prefixEnd_4769073 : Nat := 4983230072969 + 3 ^ 40 * 4769073 * 2
def baseEnd_4769073 : Nat := 2448826725379724713654939

theorem tailTrace_4769073 : CollatzResearch.WordTrace tailWord_4769073 prefixEnd_4769073 2448826725379724713654939 := by
  unfold tailWord_4769073
  simp only [CollatzResearch.WordTrace]
  refine ⟨173942382251470488668423873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115961588167646992445615915 173942382251470488668423873)
  ·
    refine ⟨130456786688602866501317905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173942382251470488668423873 130456786688602866501317905)
    ·
      refine ⟨97842590016452149875988429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130456786688602866501317905 97842590016452149875988429)
      ·
        refine ⟨36690971256169556203495661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97842590016452149875988429 36690971256169556203495661)
        ·
          refine ⟨13759114221063583576310873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36690971256169556203495661 13759114221063583576310873)
          ·
            refine ⟨10319335665797687682233155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13759114221063583576310873 10319335665797687682233155)
            ·
              refine ⟨15479003498696531523349733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10319335665797687682233155 15479003498696531523349733)
              ·
                refine ⟨2902313156005599660628075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15479003498696531523349733 2902313156005599660628075)
                ·
                  refine ⟨4353469734008399490942113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902313156005599660628075 4353469734008399490942113)
                  ·
                    refine ⟨3265102300506299618206585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4353469734008399490942113 3265102300506299618206585)
                    ·
                      refine ⟨2448826725379724713654939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3265102300506299618206585 2448826725379724713654939)
                      ·
                        rfl

theorem cell23_4769073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_4769073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769073 prefixEnd_4769073 := by exact prefixLift 4769073
  have htrace : WordTrace (prefixWord ++ tailWord_4769073) baseStart_4769073 baseEnd_4769073 := by
    simpa [prefixWord, tailWord_4769073, baseEnd_4769073] using wordTrace_append hprefix tailTrace_4769073
  have hstable : (prefixWord ++ tailWord_4769073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769073).length < 2 ^ (prefixWord ++ tailWord_4769073).sum := by decide
  have hdescent : baseEnd_4769073 < baseStart_4769073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769075 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 2, 7]
def baseStart_4769075 : Nat := 118140960795 + 4769075 * 2 ^ 59
def prefixEnd_4769075 : Nat := 4983230072969 + 3 ^ 40 * 4769075 * 2
def baseEnd_4769075 : Nat := 816275917447011235276643

theorem tailTrace_4769075 : CollatzResearch.WordTrace tailWord_4769075 prefixEnd_4769075 816275917447011235276643 := by
  unfold tailWord_4769075
  simp only [CollatzResearch.WordTrace]
  refine ⟨173942455197463243009996679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115961636798308828673331119 173942455197463243009996679)
  ·
    refine ⟨260913682796194864514995019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173942455197463243009996679 260913682796194864514995019)
    ·
      refine ⟨391370524194292296772492529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260913682796194864514995019 391370524194292296772492529)
      ·
        refine ⟨293527893145719222579369397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391370524194292296772492529 293527893145719222579369397)
        ·
          refine ⟨27518239982411177116815881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 293527893145719222579369397 27518239982411177116815881)
          ·
            refine ⟨20638679986808382837611911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27518239982411177116815881 20638679986808382837611911)
            ·
              refine ⟨30958019980212574256417867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20638679986808382837611911 30958019980212574256417867)
              ·
                refine ⟨46437029970318861384626801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30958019980212574256417867 46437029970318861384626801)
                ·
                  refine ⟨34827772477739146038470101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46437029970318861384626801 34827772477739146038470101)
                  ·
                    refine ⟨816275917447011235276643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34827772477739146038470101 816275917447011235276643)
                    ·
                      rfl

theorem cell23_4769075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 7].length) (baseStart_4769075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769075 prefixEnd_4769075 := by exact prefixLift 4769075
  have htrace : WordTrace (prefixWord ++ tailWord_4769075) baseStart_4769075 baseEnd_4769075 := by
    simpa [prefixWord, tailWord_4769075, baseEnd_4769075] using wordTrace_append hprefix tailTrace_4769075
  have hstable : (prefixWord ++ tailWord_4769075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769075).length < 2 ^ (prefixWord ++ tailWord_4769075).sum := by decide
  have hdescent : baseEnd_4769075 < baseStart_4769075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769089 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4769089 : Nat := 118140960795 + 4769089 * 2 ^ 59
def prefixEnd_4769089 : Nat := 4983230072969 + 3 ^ 40 * 4769089 * 2
def baseEnd_4769089 : Nat := 2448834941070196651054865

theorem tailTrace_4769089 : CollatzResearch.WordTrace tailWord_4769089 prefixEnd_4769089 2448834941070196651054865 := by
  unfold tailWord_4769089
  simp only [CollatzResearch.WordTrace]
  refine ⟨173942965819412523401006321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115961977212941682267337547 173942965819412523401006321)
  ·
    refine ⟨130457224364559392550754741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173942965819412523401006321 130457224364559392550754741)
    ·
      refine ⟨12230364784177443051633257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130457224364559392550754741 12230364784177443051633257)
      ·
        refine ⟨9172773588133082288724943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12230364784177443051633257 9172773588133082288724943)
        ·
          refine ⟨13759160382199623433087415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9172773588133082288724943 13759160382199623433087415)
          ·
            refine ⟨20638740573299435149631123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13759160382199623433087415 20638740573299435149631123)
            ·
              refine ⟨30958110859949152724446685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20638740573299435149631123 30958110859949152724446685)
              ·
                refine ⟨11609291572480932271667507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30958110859949152724446685 11609291572480932271667507)
                ·
                  refine ⟨17413937358721398407501261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11609291572480932271667507 17413937358721398407501261)
                  ·
                    refine ⟨6530226509520524402812973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17413937358721398407501261 6530226509520524402812973)
                    ·
                      refine ⟨2448834941070196651054865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6530226509520524402812973 2448834941070196651054865)
                      ·
                        rfl

theorem cell23_4769089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4769089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769089 prefixEnd_4769089 := by exact prefixLift 4769089
  have htrace : WordTrace (prefixWord ++ tailWord_4769089) baseStart_4769089 baseEnd_4769089 := by
    simpa [prefixWord, tailWord_4769089, baseEnd_4769089] using wordTrace_append hprefix tailTrace_4769089
  have hstable : (prefixWord ++ tailWord_4769089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769089).length < 2 ^ (prefixWord ++ tailWord_4769089).sum := by decide
  have hdescent : baseEnd_4769089 < baseStart_4769089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769105 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 1, 8]
def baseStart_4769105 : Nat := 118140960795 + 4769105 * 2 ^ 59
def prefixEnd_4769105 : Nat := 4983230072969 + 3 ^ 40 * 4769105 * 2
def baseEnd_4769105 : Nat := 816281052253556196151597

theorem tailTrace_4769105 : CollatzResearch.WordTrace tailWord_4769105 prefixEnd_4769105 816281052253556196151597 := by
  unfold tailWord_4769105
  simp only [CollatzResearch.WordTrace]
  refine ⟨173943549387354558133588769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115962366258236372089059179 173943549387354558133588769)
  ·
    refine ⟨130457662040515918600191577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173943549387354558133588769 130457662040515918600191577)
    ·
      refine ⟨97843246530386938950143683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130457662040515918600191577 97843246530386938950143683)
      ·
        refine ⟨146764869795580408425215525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97843246530386938950143683 146764869795580408425215525)
        ·
          refine ⟨27518413086671326579727911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146764869795580408425215525 27518413086671326579727911)
          ·
            refine ⟨41277619630006989869591867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27518413086671326579727911 41277619630006989869591867)
            ·
              refine ⟨61916429445010484804387801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41277619630006989869591867 61916429445010484804387801)
              ·
                refine ⟨46437322083757863603290851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61916429445010484804387801 46437322083757863603290851)
                ·
                  refine ⟨69655983125636795404936277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46437322083757863603290851 69655983125636795404936277)
                  ·
                    refine ⟨816281052253556196151597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69655983125636795404936277 816281052253556196151597)
                    ·
                      rfl

theorem cell23_4769105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_4769105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769105 prefixEnd_4769105 := by exact prefixLift 4769105
  have htrace : WordTrace (prefixWord ++ tailWord_4769105) baseStart_4769105 baseEnd_4769105 := by
    simpa [prefixWord, tailWord_4769105, baseEnd_4769105] using wordTrace_append hprefix tailTrace_4769105
  have hstable : (prefixWord ++ tailWord_4769105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769105).length < 2 ^ (prefixWord ++ tailWord_4769105).sum := by decide
  have hdescent : baseEnd_4769105 < baseStart_4769105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769117 : List Nat := [1, 4, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4769117 : Nat := 118140960795 + 4769117 * 2 ^ 59
def prefixEnd_4769117 : Nat := 4983230072969 + 3 ^ 40 * 4769117 * 2
def baseEnd_4769117 : Nat := 816283106176174180501579

theorem tailTrace_4769117 : CollatzResearch.WordTrace tailWord_4769117 prefixEnd_4769117 816283106176174180501579 := by
  unfold tailWord_4769117
  simp only [CollatzResearch.WordTrace]
  refine ⟨173943987063311084183025605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115962658042207389455350403 173943987063311084183025605)
  ·
    refine ⟨32614497574370828284317301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173943987063311084183025605 32614497574370828284317301)
    ·
      refine ⟨3057609147597265151654747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32614497574370828284317301 3057609147597265151654747)
      ·
        refine ⟨4586413721395897727482121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3057609147597265151654747 4586413721395897727482121)
        ·
          refine ⟨3439810291046923295611591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4586413721395897727482121 3439810291046923295611591)
          ·
            refine ⟨5159715436570384943417387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439810291046923295611591 5159715436570384943417387)
            ·
              refine ⟨7739573154855577415126081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159715436570384943417387 7739573154855577415126081)
              ·
                refine ⟨5804679866141683061344561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7739573154855577415126081 5804679866141683061344561)
                ·
                  refine ⟨4353509899606262296008421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5804679866141683061344561 4353509899606262296008421)
                  ·
                    refine ⟨816283106176174180501579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4353509899606262296008421 816283106176174180501579)
                    ·
                      rfl

theorem cell23_4769117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4769117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769117 prefixEnd_4769117 := by exact prefixLift 4769117
  have htrace : WordTrace (prefixWord ++ tailWord_4769117) baseStart_4769117 baseEnd_4769117 := by
    simpa [prefixWord, tailWord_4769117, baseEnd_4769117] using wordTrace_append hprefix tailTrace_4769117
  have hstable : (prefixWord ++ tailWord_4769117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769117).length < 2 ^ (prefixWord ++ tailWord_4769117).sum := by decide
  have hdescent : baseEnd_4769117 < baseStart_4769117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769122 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_4769122 : Nat := 118140960795 + 4769122 * 2 ^ 59
def prefixEnd_4769122 : Nat := 4983230072969 + 3 ^ 40 * 4769122 * 2
def baseEnd_4769122 : Nat := 816283961977265007314071

theorem tailTrace_4769122 : CollatzResearch.WordTrace tailWord_4769122 prefixEnd_4769122 816283961977265007314071 := by
  unfold tailWord_4769122
  simp only [CollatzResearch.WordTrace]
  refine ⟨43486042357073242509239405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115962779618861980024638413 43486042357073242509239405)
  ·
    refine ⟨16307265883902465940964777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43486042357073242509239405 16307265883902465940964777)
    ·
      refine ⟨12230449412926849455723583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16307265883902465940964777 12230449412926849455723583)
      ·
        refine ⟨18345674119390274183585375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12230449412926849455723583 18345674119390274183585375)
        ·
          refine ⟨27518511179085411275378063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18345674119390274183585375 27518511179085411275378063)
          ·
            refine ⟨41277766768628116913067095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27518511179085411275378063 41277766768628116913067095)
            ·
              refine ⟨61916650152942175369600643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41277766768628116913067095 61916650152942175369600643)
              ·
                refine ⟨92874975229413263054400965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61916650152942175369600643 92874975229413263054400965)
                ·
                  refine ⟨17414057855514986822700181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92874975229413263054400965 17414057855514986822700181)
                  ·
                    refine ⟨816283961977265007314071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17414057855514986822700181 816283961977265007314071)
                    ·
                      rfl

theorem cell23_4769122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_4769122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769122 prefixEnd_4769122 := by exact prefixLift 4769122
  have htrace : WordTrace (prefixWord ++ tailWord_4769122) baseStart_4769122 baseEnd_4769122 := by
    simpa [prefixWord, tailWord_4769122, baseEnd_4769122] using wordTrace_append hprefix tailTrace_4769122
  have hstable : (prefixWord ++ tailWord_4769122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769122).length < 2 ^ (prefixWord ++ tailWord_4769122).sum := by decide
  have hdescent : baseEnd_4769122 < baseStart_4769122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769195 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 3, 10]
def baseStart_4769195 : Nat := 118140960795 + 4769195 * 2 ^ 59
def prefixEnd_4769195 : Nat := 4983230072969 + 3 ^ 40 * 4769195 * 2
def baseEnd_4769195 : Nat := 816296456673191078776459

theorem tailTrace_4769195 : CollatzResearch.WordTrace tailWord_4769195 prefixEnd_4769195 816296456673191078776459 := by
  unfold tailWord_4769195
  simp only [CollatzResearch.WordTrace]
  refine ⟨173946831957028503504365039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115964554638019002336243359 173946831957028503504365039)
  ·
    refine ⟨260920247935542755256547559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173946831957028503504365039 260920247935542755256547559)
    ·
      refine ⟨391380371903314132884821339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260920247935542755256547559 391380371903314132884821339)
      ·
        refine ⟨587070557854971199327232009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391380371903314132884821339 587070557854971199327232009)
        ·
          refine ⟨440302918391228399495424007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587070557854971199327232009 440302918391228399495424007)
          ·
            refine ⟨660454377586842599243136011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440302918391228399495424007 660454377586842599243136011)
            ·
              refine ⟨990681566380263898864704017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660454377586842599243136011 990681566380263898864704017)
              ·
                refine ⟨743011174785197924148528013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990681566380263898864704017 743011174785197924148528013)
                ·
                  refine ⟨278629190544449221555698005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743011174785197924148528013 278629190544449221555698005)
                  ·
                    refine ⟨816296456673191078776459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 278629190544449221555698005 816296456673191078776459)
                    ·
                      rfl

theorem cell23_4769195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 10].length) (baseStart_4769195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769195 prefixEnd_4769195 := by exact prefixLift 4769195
  have htrace : WordTrace (prefixWord ++ tailWord_4769195) baseStart_4769195 baseEnd_4769195 := by
    simpa [prefixWord, tailWord_4769195, baseEnd_4769195] using wordTrace_append hprefix tailTrace_4769195
  have hstable : (prefixWord ++ tailWord_4769195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769195).length < 2 ^ (prefixWord ++ tailWord_4769195).sum := by decide
  have hdescent : baseEnd_4769195 < baseStart_4769195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769197 : List Nat := [1, 5, 2, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_4769197 : Nat := 118140960795 + 4769197 * 2 ^ 59
def prefixEnd_4769197 : Nat := 4983230072969 + 3 ^ 40 * 4769197 * 2
def baseEnd_4769197 : Nat := 2448890396980882228504369

theorem tailTrace_4769197 : CollatzResearch.WordTrace tailWord_4769197 prefixEnd_4769197 2448890396980882228504369 := by
  unfold tailWord_4769197
  simp only [CollatzResearch.WordTrace]
  refine ⟨173946904903021257845937845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115964603268680838563958563 173946904903021257845937845)
  ·
    refine ⟨16307522334658242923056673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173946904903021257845937845 16307522334658242923056673)
    ·
      refine ⟨12230641750993682192292505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16307522334658242923056673 12230641750993682192292505)
      ·
        refine ⟨9172981313245261644219379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12230641750993682192292505 9172981313245261644219379)
        ·
          refine ⟨13759471969867892466329069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9172981313245261644219379 13759471969867892466329069)
          ·
            refine ⟨5159801988700459674873401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13759471969867892466329069 5159801988700459674873401)
            ·
              refine ⟨3869851491525344756155051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5159801988700459674873401 3869851491525344756155051)
              ·
                refine ⟨5804777237288017134232577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3869851491525344756155051 5804777237288017134232577)
                ·
                  refine ⟨4353582927966012850674433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5804777237288017134232577 4353582927966012850674433)
                  ·
                    refine ⟨3265187195974509638005825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4353582927966012850674433 3265187195974509638005825)
                    ·
                      refine ⟨2448890396980882228504369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3265187195974509638005825 2448890396980882228504369)
                      ·
                        rfl

theorem cell23_4769197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_4769197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769197 prefixEnd_4769197 := by exact prefixLift 4769197
  have htrace : WordTrace (prefixWord ++ tailWord_4769197) baseStart_4769197 baseEnd_4769197 := by
    simpa [prefixWord, tailWord_4769197, baseEnd_4769197] using wordTrace_append hprefix tailTrace_4769197
  have hstable : (prefixWord ++ tailWord_4769197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769197).length < 2 ^ (prefixWord ++ tailWord_4769197).sum := by decide
  have hdescent : baseEnd_4769197 < baseStart_4769197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769202 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_4769202 : Nat := 118140960795 + 4769202 * 2 ^ 59
def prefixEnd_4769202 : Nat := 4983230072969 + 3 ^ 40 * 4769202 * 2
def baseEnd_4769202 : Nat := 2448892964384154708941845

theorem tailTrace_4769202 : CollatzResearch.WordTrace tailWord_4769202 prefixEnd_4769202 2448892964384154708941845 := by
  unfold tailWord_4769202
  simp only [CollatzResearch.WordTrace]
  refine ⟨43486771817000785924967465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115964724845335429133246573 43486771817000785924967465)
  ·
    refine ⟨32615078862750589443725599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43486771817000785924967465 32615078862750589443725599)
    ·
      refine ⟨48922618294125884165588399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32615078862750589443725599 48922618294125884165588399)
      ·
        refine ⟨73383927441188826248382599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48922618294125884165588399 73383927441188826248382599)
        ·
          refine ⟨110075891161783239372573899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73383927441188826248382599 110075891161783239372573899)
          ·
            refine ⟨165113836742674859058860849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110075891161783239372573899 165113836742674859058860849)
            ·
              refine ⟨123835377557006144294145637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165113836742674859058860849 123835377557006144294145637)
              ·
                refine ⟨23219133291938652055152307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123835377557006144294145637 23219133291938652055152307)
                ·
                  refine ⟨34828699937907978082728461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23219133291938652055152307 34828699937907978082728461)
                  ·
                    refine ⟨13060762476715491781023173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34828699937907978082728461 13060762476715491781023173)
                    ·
                      refine ⟨2448892964384154708941845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13060762476715491781023173 2448892964384154708941845)
                      ·
                        rfl

theorem cell23_4769202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_4769202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769202 prefixEnd_4769202 := by exact prefixLift 4769202
  have htrace : WordTrace (prefixWord ++ tailWord_4769202) baseStart_4769202 baseEnd_4769202 := by
    simpa [prefixWord, tailWord_4769202, baseEnd_4769202] using wordTrace_append hprefix tailTrace_4769202
  have hstable : (prefixWord ++ tailWord_4769202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769202).length < 2 ^ (prefixWord ++ tailWord_4769202).sum := by decide
  have hdescent : baseEnd_4769202 < baseStart_4769202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769289 : List Nat := [1, 2, 1, 1, 3, 1, 5, 3, 1, 5]
def baseStart_4769289 : Nat := 118140960795 + 4769289 * 2 ^ 59
def prefixEnd_4769289 : Nat := 4983230072969 + 3 ^ 40 * 4769289 * 2
def baseEnd_4769289 : Nat := 816312545733698622851315

theorem tailTrace_4769289 : CollatzResearch.WordTrace tailWord_4769289 prefixEnd_4769289 816312545733698622851315 := by
  unfold tailWord_4769289
  simp only [CollatzResearch.WordTrace]
  refine ⟨173950260418687957558286921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115966840279125305038857947 173950260418687957558286921)
  ·
    refine ⟨130462695314015968168715191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173950260418687957558286921 130462695314015968168715191)
    ·
      refine ⟨195694042971023952253072787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130462695314015968168715191 195694042971023952253072787)
      ·
        refine ⟨293541064456535928379609181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195694042971023952253072787 293541064456535928379609181)
        ·
          refine ⟨110077899171200973142353443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293541064456535928379609181 110077899171200973142353443)
          ·
            refine ⟨165116848756801459713530165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110077899171200973142353443 165116848756801459713530165)
            ·
              refine ⟨15479704570950136848143453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165116848756801459713530165 15479704570950136848143453)
              ·
                refine ⟨5804889214106301318053795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15479704570950136848143453 5804889214106301318053795)
                ·
                  refine ⟨8707333821159451977080693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5804889214106301318053795 8707333821159451977080693)
                  ·
                    refine ⟨816312545733698622851315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8707333821159451977080693 816312545733698622851315)
                    ·
                      rfl

theorem cell23_4769289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 5].length) (baseStart_4769289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769289 prefixEnd_4769289 := by exact prefixLift 4769289
  have htrace : WordTrace (prefixWord ++ tailWord_4769289) baseStart_4769289 baseEnd_4769289 := by
    simpa [prefixWord, tailWord_4769289, baseEnd_4769289] using wordTrace_append hprefix tailTrace_4769289
  have hstable : (prefixWord ++ tailWord_4769289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769289).length < 2 ^ (prefixWord ++ tailWord_4769289).sum := by decide
  have hdescent : baseEnd_4769289 < baseStart_4769289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769293 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 8]
def baseStart_4769293 : Nat := 118140960795 + 4769293 * 2 ^ 59
def prefixEnd_4769293 : Nat := 4983230072969 + 3 ^ 40 * 4769293 * 2
def baseEnd_4769293 : Nat := 272104410124857094767103

theorem tailTrace_4769293 : CollatzResearch.WordTrace tailWord_4769293 prefixEnd_4769293 272104410124857094767103 := by
  unfold tailWord_4769293
  simp only [CollatzResearch.WordTrace]
  refine ⟨173950406310673466241432533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115966937540448977494288355 173950406310673466241432533)
  ·
    refine ⟨4076962647906409365033575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 173950406310673466241432533 4076962647906409365033575)
    ·
      refine ⟨6115443971859614047550363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4076962647906409365033575 6115443971859614047550363)
      ·
        refine ⟨9173165957789421071325545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6115443971859614047550363 9173165957789421071325545)
        ·
          refine ⟨6879874468342065803494159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9173165957789421071325545 6879874468342065803494159)
          ·
            refine ⟨10319811702513098705241239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6879874468342065803494159 10319811702513098705241239)
            ·
              refine ⟨15479717553769648057861859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10319811702513098705241239 15479717553769648057861859)
              ·
                refine ⟨23219576330654472086792789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15479717553769648057861859 23219576330654472086792789)
                ·
                  refine ⟨272104410124857094767103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23219576330654472086792789 272104410124857094767103)
                  ·
                    rfl

theorem cell23_4769293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_4769293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769293 prefixEnd_4769293 := by exact prefixLift 4769293
  have htrace : WordTrace (prefixWord ++ tailWord_4769293) baseStart_4769293 baseEnd_4769293 := by
    simpa [prefixWord, tailWord_4769293, baseEnd_4769293] using wordTrace_append hprefix tailTrace_4769293
  have hstable : (prefixWord ++ tailWord_4769293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769293).length < 2 ^ (prefixWord ++ tailWord_4769293).sum := by decide
  have hdescent : baseEnd_4769293 < baseStart_4769293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769419 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 3]
def baseStart_4769419 : Nat := 118140960795 + 4769419 * 2 ^ 59
def prefixEnd_4769419 : Nat := 4983230072969 + 3 ^ 40 * 4769419 * 2
def baseEnd_4769419 : Nat := 2449004389686180359928347

theorem tailTrace_4769419 : CollatzResearch.WordTrace tailWord_4769419 prefixEnd_4769419 2449004389686180359928347 := by
  unfold tailWord_4769419
  simp only [CollatzResearch.WordTrace]
  refine ⟨173955001908216989760519311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115970001272144659840346207 173955001908216989760519311)
  ·
    refine ⟨260932502862325484640778967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173955001908216989760519311 260932502862325484640778967)
    ·
      refine ⟨391398754293488226961168451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260932502862325484640778967 391398754293488226961168451)
      ·
        refine ⟨587098131440232340441752677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391398754293488226961168451 587098131440232340441752677)
        ·
          refine ⟨110080899645043563832828627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 587098131440232340441752677 110080899645043563832828627)
          ·
            refine ⟨165121349467565345749242941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110080899645043563832828627 165121349467565345749242941)
            ·
              refine ⟨61920506050337004655966103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165121349467565345749242941 61920506050337004655966103)
              ·
                refine ⟨92880759075505506983949155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61920506050337004655966103 92880759075505506983949155)
                ·
                  refine ⟨139321138613258260475923733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92880759075505506983949155 139321138613258260475923733)
                  ·
                    refine ⟨6530678372496480959808925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 139321138613258260475923733 6530678372496480959808925)
                    ·
                      refine ⟨2449004389686180359928347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6530678372496480959808925 2449004389686180359928347)
                      ·
                        rfl

theorem cell23_4769419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 3].length) (baseStart_4769419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769419 prefixEnd_4769419 := by exact prefixLift 4769419
  have htrace : WordTrace (prefixWord ++ tailWord_4769419) baseStart_4769419 baseEnd_4769419 := by
    simpa [prefixWord, tailWord_4769419, baseEnd_4769419] using wordTrace_append hprefix tailTrace_4769419
  have hstable : (prefixWord ++ tailWord_4769419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769419).length < 2 ^ (prefixWord ++ tailWord_4769419).sum := by decide
  have hdescent : baseEnd_4769419 < baseStart_4769419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769456 : List Nat := [2, 1, 1, 1, 2, 1, 5, 5, 5]
def baseStart_4769456 : Nat := 118140960795 + 4769456 * 2 ^ 59
def prefixEnd_4769456 : Nat := 4983230072969 + 3 ^ 40 * 4769456 * 2
def baseEnd_4769456 : Nat := 272113709830044079462853

theorem tailTrace_4769456 : CollatzResearch.WordTrace tailWord_4769456 prefixEnd_4769456 272113709830044079462853 := by
  unfold tailWord_4769456
  simp only [CollatzResearch.WordTrace]
  refine ⟨86978175704541472539808111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115970900939388630053077481 86978175704541472539808111)
  ·
    refine ⟨130467263556812208809712167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86978175704541472539808111 130467263556812208809712167)
    ·
      refine ⟨195700895335218313214568251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130467263556812208809712167 195700895335218313214568251)
      ·
        refine ⟨293551343002827469821852377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195700895335218313214568251 293551343002827469821852377)
        ·
          refine ⟨220163507252120602366389283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293551343002827469821852377 220163507252120602366389283)
          ·
            refine ⟨330245260878180903549583925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220163507252120602366389283 330245260878180903549583925)
            ·
              refine ⟨30960493207329459707773493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 330245260878180903549583925 30960493207329459707773493)
              ·
                refine ⟨2902546238187136847603765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30960493207329459707773493 2902546238187136847603765)
                ·
                  refine ⟨272113709830044079462853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2902546238187136847603765 272113709830044079462853)
                  ·
                    rfl

theorem cell23_4769456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 5].length) (baseStart_4769456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769456 prefixEnd_4769456 := by exact prefixLift 4769456
  have htrace : WordTrace (prefixWord ++ tailWord_4769456) baseStart_4769456 baseEnd_4769456 := by
    simpa [prefixWord, tailWord_4769456, baseEnd_4769456] using wordTrace_append hprefix tailTrace_4769456
  have hstable : (prefixWord ++ tailWord_4769456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769456).length < 2 ^ (prefixWord ++ tailWord_4769456).sum := by decide
  have hdescent : baseEnd_4769456 < baseStart_4769456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769466 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3]
def baseStart_4769466 : Nat := 118140960795 + 4769466 * 2 ^ 59
def prefixEnd_4769466 : Nat := 4983230072969 + 3 ^ 40 * 4769466 * 2
def baseEnd_4769466 : Nat := 2449028523276941676040631

theorem tailTrace_4769466 : CollatzResearch.WordTrace tailWord_4769466 prefixEnd_4769466 2449028523276941676040631 := by
  unfold tailWord_4769466
  simp only [CollatzResearch.WordTrace]
  refine ⟨43489179034761679196870063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115971144092697811191653501 43489179034761679196870063)
  ·
    refine ⟨65233768552142518795305095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43489179034761679196870063 65233768552142518795305095)
    ·
      refine ⟨97850652828213778192957643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65233768552142518795305095 97850652828213778192957643)
      ·
        refine ⟨146775979242320667289436465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97850652828213778192957643 146775979242320667289436465)
        ·
          refine ⟨110081984431740500467077349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146775979242320667289436465 110081984431740500467077349)
          ·
            refine ⟨20640372080951343837577003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110081984431740500467077349 20640372080951343837577003)
            ·
              refine ⟨30960558121427015756365505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20640372080951343837577003 30960558121427015756365505)
              ·
                refine ⟨23220418591070261817274129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30960558121427015756365505 23220418591070261817274129)
                ·
                  refine ⟨17415313943302696362955597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23220418591070261817274129 17415313943302696362955597)
                  ·
                    refine ⟨6530742728738511136108349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17415313943302696362955597 6530742728738511136108349)
                    ·
                      refine ⟨2449028523276941676040631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6530742728738511136108349 2449028523276941676040631)
                      ·
                        rfl

theorem cell23_4769466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_4769466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769466 prefixEnd_4769466 := by exact prefixLift 4769466
  have htrace : WordTrace (prefixWord ++ tailWord_4769466) baseStart_4769466 baseEnd_4769466 := by
    simpa [prefixWord, tailWord_4769466, baseEnd_4769466] using wordTrace_append hprefix tailTrace_4769466
  have hstable : (prefixWord ++ tailWord_4769466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769466).length < 2 ^ (prefixWord ++ tailWord_4769466).sum := by decide
  have hdescent : baseEnd_4769466 < baseStart_4769466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769479 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_4769479 : Nat := 118140960795 + 4769479 * 2 ^ 59
def prefixEnd_4769479 : Nat := 4983230072969 + 3 ^ 40 * 4769479 * 2
def baseEnd_4769479 : Nat := 2449035198525450125178071

theorem tailTrace_4769479 : CollatzResearch.WordTrace tailWord_4769479 prefixEnd_4769479 2449035198525450125178071 := by
  unfold tailWord_4769479
  simp only [CollatzResearch.WordTrace]
  refine ⟨173957190287999620007703491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115971460191999746671802327 173957190287999620007703491)
  ·
    refine ⟨260935785431999430011555237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173957190287999620007703491 260935785431999430011555237)
    ·
      refine ⟨48925459768499893127166607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260935785431999430011555237 48925459768499893127166607)
      ·
        refine ⟨73388189652749839690749911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48925459768499893127166607 73388189652749839690749911)
        ·
          refine ⟨110082284479124759536124867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73388189652749839690749911 110082284479124759536124867)
          ·
            refine ⟨165123426718687139304187301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110082284479124759536124867 165123426718687139304187301)
            ·
              refine ⟨30960642509753838619535119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165123426718687139304187301 30960642509753838619535119)
              ·
                refine ⟨46440963764630757929302679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30960642509753838619535119 46440963764630757929302679)
                ·
                  refine ⟨69661445646946136893954019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46440963764630757929302679 69661445646946136893954019)
                  ·
                    refine ⟨104492168470419205340931029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69661445646946136893954019 104492168470419205340931029)
                    ·
                      refine ⟨2449035198525450125178071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104492168470419205340931029 2449035198525450125178071)
                      ·
                        rfl

theorem cell23_4769479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_4769479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769479 prefixEnd_4769479 := by exact prefixLift 4769479
  have htrace : WordTrace (prefixWord ++ tailWord_4769479) baseStart_4769479 baseEnd_4769479 := by
    simpa [prefixWord, tailWord_4769479, baseEnd_4769479] using wordTrace_append hprefix tailTrace_4769479
  have hstable : (prefixWord ++ tailWord_4769479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769479).length < 2 ^ (prefixWord ++ tailWord_4769479).sum := by decide
  have hdescent : baseEnd_4769479 < baseStart_4769479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769484 : List Nat := [2, 2, 1, 5, 2, 1, 3, 1, 2, 2, 2]
def baseStart_4769484 : Nat := 118140960795 + 4769484 * 2 ^ 59
def prefixEnd_4769484 : Nat := 4983230072969 + 3 ^ 40 * 4769484 * 2
def baseEnd_4769484 : Nat := 2449037765928722605615549

theorem tailTrace_4769484 : CollatzResearch.WordTrace tailWord_4769484 prefixEnd_4769484 2449037765928722605615549 := by
  unfold tailWord_4769484
  simp only [CollatzResearch.WordTrace]
  refine ⟨86978686326490752930817753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115971581768654337241090337 86978686326490752930817753)
  ·
    refine ⟨65234014744868064698113315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86978686326490752930817753 65234014744868064698113315)
    ·
      refine ⟨97851022117302097047169973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65234014744868064698113315 97851022117302097047169973)
      ·
        refine ⟨9173533323497071598172185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97851022117302097047169973 9173533323497071598172185)
        ·
          refine ⟨6880149992622803698629139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9173533323497071598172185 6880149992622803698629139)
          ·
            refine ⟨10320224988934205547943709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6880149992622803698629139 10320224988934205547943709)
            ·
              refine ⟨3870084370850327080478891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10320224988934205547943709 3870084370850327080478891)
              ·
                refine ⟨5805126556275490620718337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870084370850327080478891 5805126556275490620718337)
                ·
                  refine ⟨4353844917206617965538753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5805126556275490620718337 4353844917206617965538753)
                  ·
                    refine ⟨3265383687904963474154065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4353844917206617965538753 3265383687904963474154065)
                    ·
                      refine ⟨2449037765928722605615549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3265383687904963474154065 2449037765928722605615549)
                      ·
                        rfl

theorem cell23_4769484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_4769484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769484 prefixEnd_4769484 := by exact prefixLift 4769484
  have htrace : WordTrace (prefixWord ++ tailWord_4769484) baseStart_4769484 baseEnd_4769484 := by
    simpa [prefixWord, tailWord_4769484, baseEnd_4769484] using wordTrace_append hprefix tailTrace_4769484
  have hstable : (prefixWord ++ tailWord_4769484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769484).length < 2 ^ (prefixWord ++ tailWord_4769484).sum := by decide
  have hdescent : baseEnd_4769484 < baseStart_4769484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769507 : List Nat := [1, 1, 1, 7, 3, 1, 1, 3, 5]
def baseStart_4769507 : Nat := 118140960795 + 4769507 * 2 ^ 59
def prefixEnd_4769507 : Nat := 4983230072969 + 3 ^ 40 * 4769507 * 2
def baseEnd_4769507 : Nat := 272116619553752890625327

theorem tailTrace_4769507 : CollatzResearch.WordTrace tailWord_4769507 prefixEnd_4769507 272116619553752890625327 := by
  unfold tailWord_4769507
  simp only [CollatzResearch.WordTrace]
  refine ⟨173958211531898180789722775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115972141021265453859815183 173958211531898180789722775)
  ·
    refine ⟨260937317297847271184584163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173958211531898180789722775 260937317297847271184584163)
    ·
      refine ⟨391405975946770906776876245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260937317297847271184584163 391405975946770906776876245)
      ·
        refine ⟨9173577561252443127583037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 391405975946770906776876245 9173577561252443127583037)
        ·
          refine ⟨3440091585469666172843639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9173577561252443127583037 3440091585469666172843639)
          ·
            refine ⟨5160137378204499259265459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3440091585469666172843639 5160137378204499259265459)
            ·
              refine ⟨7740206067306748888898189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5160137378204499259265459 7740206067306748888898189)
              ·
                refine ⟨2902577275240030833336821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7740206067306748888898189 2902577275240030833336821)
                ·
                  refine ⟨272116619553752890625327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2902577275240030833336821 272116619553752890625327)
                  ·
                    rfl

theorem cell23_4769507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 5].length) (baseStart_4769507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769507 prefixEnd_4769507 := by exact prefixLift 4769507
  have htrace : WordTrace (prefixWord ++ tailWord_4769507) baseStart_4769507 baseEnd_4769507 := by
    simpa [prefixWord, tailWord_4769507, baseEnd_4769507] using wordTrace_append hprefix tailTrace_4769507
  have hstable : (prefixWord ++ tailWord_4769507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769507).length < 2 ^ (prefixWord ++ tailWord_4769507).sum := by decide
  have hdescent : baseEnd_4769507 < baseStart_4769507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769516 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 5, 4]
def baseStart_4769516 : Nat := 118140960795 + 4769516 * 2 ^ 59
def prefixEnd_4769516 : Nat := 4983230072969 + 3 ^ 40 * 4769516 * 2
def baseEnd_4769516 : Nat := 816351399103222160138467

theorem tailTrace_4769516 : CollatzResearch.WordTrace tailWord_4769516 prefixEnd_4769516 816351399103222160138467 := by
  unfold tailWord_4769516
  simp only [CollatzResearch.WordTrace]
  refine ⟨86979269894432787663400201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115972359859243716884533601 86979269894432787663400201)
  ·
    refine ⟨65234452420824590747550151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86979269894432787663400201 65234452420824590747550151)
    ·
      refine ⟨97851678631236886121325227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65234452420824590747550151 97851678631236886121325227)
      ·
        refine ⟨146777517946855329181987841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97851678631236886121325227 146777517946855329181987841)
        ·
          refine ⟨110083138460141496886490881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146777517946855329181987841 110083138460141496886490881)
          ·
            refine ⟨82562353845106122664868161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110083138460141496886490881 82562353845106122664868161)
            ·
              refine ⟨61921765383829591998651121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82562353845106122664868161 61921765383829591998651121)
              ·
                refine ⟨46441324037872193998988341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61921765383829591998651121 46441324037872193998988341)
                ·
                  refine ⟨4353874128550518187405157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46441324037872193998988341 4353874128550518187405157)
                  ·
                    refine ⟨816351399103222160138467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4353874128550518187405157 816351399103222160138467)
                    ·
                      rfl

theorem cell23_4769516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_4769516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769516 prefixEnd_4769516 := by exact prefixLift 4769516
  have htrace : WordTrace (prefixWord ++ tailWord_4769516) baseStart_4769516 baseEnd_4769516 := by
    simpa [prefixWord, tailWord_4769516, baseEnd_4769516] using wordTrace_append hprefix tailTrace_4769516
  have hstable : (prefixWord ++ tailWord_4769516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769516).length < 2 ^ (prefixWord ++ tailWord_4769516).sum := by decide
  have hdescent : baseEnd_4769516 < baseStart_4769516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769524 : List Nat := [2, 6, 1, 1, 1, 2, 3, 2, 5]
def baseStart_4769524 : Nat := 118140960795 + 4769524 * 2 ^ 59
def prefixEnd_4769524 : Nat := 4983230072969 + 3 ^ 40 * 4769524 * 2
def baseEnd_4769524 : Nat := 272117589461655827679485

theorem tailTrace_4769524 : CollatzResearch.WordTrace tailWord_4769524 prefixEnd_4769524 272117589461655827679485 := by
  unfold tailWord_4769524
  simp only [CollatzResearch.WordTrace]
  refine ⟨86979415786418296346545813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115972554381891061795394417 86979415786418296346545813)
  ·
    refine ⟨4077160114988357641244335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86979415786418296346545813 4077160114988357641244335)
    ·
      refine ⟨6115740172482536461866503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4077160114988357641244335 6115740172482536461866503)
      ·
        refine ⟨9173610258723804692799755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6115740172482536461866503 9173610258723804692799755)
        ·
          refine ⟨13760415388085707039199633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9173610258723804692799755 13760415388085707039199633)
          ·
            refine ⟨10320311541064280279399725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13760415388085707039199633 10320311541064280279399725)
            ·
              refine ⟨3870116827899105104774897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10320311541064280279399725 3870116827899105104774897)
              ·
                refine ⟨2902587620924328828581173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3870116827899105104774897 2902587620924328828581173)
                ·
                  refine ⟨272117589461655827679485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2902587620924328828581173 272117589461655827679485)
                  ·
                    rfl

theorem cell23_4769524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_4769524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769524 prefixEnd_4769524 := by exact prefixLift 4769524
  have htrace : WordTrace (prefixWord ++ tailWord_4769524) baseStart_4769524 baseEnd_4769524 := by
    simpa [prefixWord, tailWord_4769524, baseEnd_4769524] using wordTrace_append hprefix tailTrace_4769524
  have hstable : (prefixWord ++ tailWord_4769524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769524).length < 2 ^ (prefixWord ++ tailWord_4769524).sum := by decide
  have hdescent : baseEnd_4769524 < baseStart_4769524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769617 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 2, 3, 2]
def baseStart_4769617 : Nat := 118140960795 + 4769617 * 2 ^ 59
def prefixEnd_4769617 : Nat := 4983230072969 + 3 ^ 40 * 4769617 * 2
def baseEnd_4769617 : Nat := 2449106058855770585252437

theorem tailTrace_4769617 : CollatzResearch.WordTrace tailWord_4769617 prefixEnd_4769617 2449106058855770585252437 := by
  unfold tailWord_4769617
  simp only [CollatzResearch.WordTrace]
  refine ⟨173962223561499669576227105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115974815707666446384151403 173962223561499669576227105)
  ·
    refine ⟨130471667671124752182170329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173962223561499669576227105 130471667671124752182170329)
    ·
      refine ⟨97853750753343564136627747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130471667671124752182170329 97853750753343564136627747)
      ·
        refine ⟨146780626130015346204941621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97853750753343564136627747 146780626130015346204941621)
        ·
          refine ⟨13760683699688938706713277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146780626130015346204941621 13760683699688938706713277)
          ·
            refine ⟨5160256387383352015017479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13760683699688938706713277 5160256387383352015017479)
            ·
              refine ⟨7740384581075028022526219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5160256387383352015017479 7740384581075028022526219)
              ·
                refine ⟨11610576871612542033789329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7740384581075028022526219 11610576871612542033789329)
                ·
                  refine ⟨8707932653709406525341997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11610576871612542033789329 8707932653709406525341997)
                  ·
                    refine ⟨3265474745141027447003249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8707932653709406525341997 3265474745141027447003249)
                    ·
                      refine ⟨2449106058855770585252437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3265474745141027447003249 2449106058855770585252437)
                      ·
                        rfl

theorem cell23_4769617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 3, 2].length) (baseStart_4769617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769617 prefixEnd_4769617 := by exact prefixLift 4769617
  have htrace : WordTrace (prefixWord ++ tailWord_4769617) baseStart_4769617 baseEnd_4769617 := by
    simpa [prefixWord, tailWord_4769617, baseEnd_4769617] using wordTrace_append hprefix tailTrace_4769617
  have hstable : (prefixWord ++ tailWord_4769617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769617).length < 2 ^ (prefixWord ++ tailWord_4769617).sum := by decide
  have hdescent : baseEnd_4769617 < baseStart_4769617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769698 : List Nat := [3, 3, 1, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_4769698 : Nat := 118140960795 + 4769698 * 2 ^ 59
def prefixEnd_4769698 : Nat := 4983230072969 + 3 ^ 40 * 4769698 * 2
def baseEnd_4769698 : Nat := 2449147650788784768339565

theorem tailTrace_4769698 : CollatzResearch.WordTrace tailWord_4769698 prefixEnd_4769698 2449147650788784768339565 := by
  unfold tailWord_4769698
  simp only [CollatzResearch.WordTrace]
  refine ⟨43491294468551555102481437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115976785249470813606617165 43491294468551555102481437)
  ·
    refine ⟨16309235425706833163430539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43491294468551555102481437 16309235425706833163430539)
    ·
      refine ⟨24463853138560249745145809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16309235425706833163430539 24463853138560249745145809)
      ·
        refine ⟨18347889853920187308859357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24463853138560249745145809 18347889853920187308859357)
        ·
          refine ⟨6880458695220070240822259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18347889853920187308859357 6880458695220070240822259)
          ·
            refine ⟨10320688042830105361233389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6880458695220070240822259 10320688042830105361233389)
            ·
              refine ⟨3870258016061289510462521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10320688042830105361233389 3870258016061289510462521)
              ·
                refine ⟨2902693512045967132846891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3870258016061289510462521 2902693512045967132846891)
                ·
                  refine ⟨4354040268068950699270337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902693512045967132846891 4354040268068950699270337)
                  ·
                    refine ⟨3265530201051713024452753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4354040268068950699270337 3265530201051713024452753)
                    ·
                      refine ⟨2449147650788784768339565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3265530201051713024452753 2449147650788784768339565)
                      ·
                        rfl

theorem cell23_4769698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_4769698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769698 prefixEnd_4769698 := by exact prefixLift 4769698
  have htrace : WordTrace (prefixWord ++ tailWord_4769698) baseStart_4769698 baseEnd_4769698 := by
    simpa [prefixWord, tailWord_4769698, baseEnd_4769698] using wordTrace_append hprefix tailTrace_4769698
  have hstable : (prefixWord ++ tailWord_4769698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769698).length < 2 ^ (prefixWord ++ tailWord_4769698).sum := by decide
  have hdescent : baseEnd_4769698 < baseStart_4769698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769720 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 1, 4, 2]
def baseStart_4769720 : Nat := 118140960795 + 4769720 * 2 ^ 59
def prefixEnd_4769720 : Nat := 4983230072969 + 3 ^ 40 * 4769720 * 2
def baseEnd_4769720 : Nat := 2449158947363183682264463

theorem tailTrace_4769720 : CollatzResearch.WordTrace tailWord_4769720 prefixEnd_4769720 2449158947363183682264463 := by
  unfold tailWord_4769720
  simp only [CollatzResearch.WordTrace]
  refine ⟨86982990140063259083613307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115977320186751012111484409 86982990140063259083613307)
  ·
    refine ⟨130474485210094888625419961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86982990140063259083613307 130474485210094888625419961)
    ·
      refine ⟨97855863907571166469064971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130474485210094888625419961 97855863907571166469064971)
      ·
        refine ⟨146783795861356749703597457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97855863907571166469064971 146783795861356749703597457)
        ·
          refine ⟨110087846896017562277698093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146783795861356749703597457 110087846896017562277698093)
          ·
            refine ⟨41282942586006585854136785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110087846896017562277698093 41282942586006585854136785)
            ·
              refine ⟨30962206939504939390602589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41282942586006585854136785 30962206939504939390602589)
              ·
                refine ⟨11610827602314352271475971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30962206939504939390602589 11610827602314352271475971)
                ·
                  refine ⟨17416241403471528407213957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11610827602314352271475971 17416241403471528407213957)
                  ·
                    refine ⟨3265545263150911576352617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17416241403471528407213957 3265545263150911576352617)
                    ·
                      refine ⟨2449158947363183682264463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3265545263150911576352617 2449158947363183682264463)
                      ·
                        rfl

theorem cell23_4769720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 4, 2].length) (baseStart_4769720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769720 prefixEnd_4769720 := by exact prefixLift 4769720
  have htrace : WordTrace (prefixWord ++ tailWord_4769720) baseStart_4769720 baseEnd_4769720 := by
    simpa [prefixWord, tailWord_4769720, baseEnd_4769720] using wordTrace_append hprefix tailTrace_4769720
  have hstable : (prefixWord ++ tailWord_4769720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769720).length < 2 ^ (prefixWord ++ tailWord_4769720).sum := by decide
  have hdescent : baseEnd_4769720 < baseStart_4769720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769724 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4769724 : Nat := 118140960795 + 4769724 * 2 ^ 59
def prefixEnd_4769724 : Nat := 4983230072969 + 3 ^ 40 * 4769724 * 2
def baseEnd_4769724 : Nat := 2449161001285801666614445

theorem tailTrace_4769724 : CollatzResearch.WordTrace tailWord_4769724 prefixEnd_4769724 2449161001285801666614445 := by
  unfold tailWord_4769724
  simp only [CollatzResearch.WordTrace]
  refine ⟨86983063086056013425186113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115977417448074684566914817 86983063086056013425186113)
  ·
    refine ⟨65237297314542010068889585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86983063086056013425186113 65237297314542010068889585)
    ·
      refine ⟨48927972985906507551667189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65237297314542010068889585 48927972985906507551667189)
      ·
        refine ⟨4586997467428735082968799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48927972985906507551667189 4586997467428735082968799)
        ·
          refine ⟨6880496201143102624453199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4586997467428735082968799 6880496201143102624453199)
          ·
            refine ⟨10320744301714653936679799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6880496201143102624453199 10320744301714653936679799)
            ·
              refine ⟨15481116452571980905019699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10320744301714653936679799 15481116452571980905019699)
              ·
                refine ⟨23221674678857971357529549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15481116452571980905019699 23221674678857971357529549)
                ·
                  refine ⟨8708128004571739259073581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23221674678857971357529549 8708128004571739259073581)
                  ·
                    refine ⟨3265548001714402222152593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8708128004571739259073581 3265548001714402222152593)
                    ·
                      refine ⟨2449161001285801666614445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3265548001714402222152593 2449161001285801666614445)
                      ·
                        rfl

theorem cell23_4769724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4769724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769724 prefixEnd_4769724 := by exact prefixLift 4769724
  have htrace : WordTrace (prefixWord ++ tailWord_4769724) baseStart_4769724 baseEnd_4769724 := by
    simpa [prefixWord, tailWord_4769724, baseEnd_4769724] using wordTrace_append hprefix tailTrace_4769724
  have hstable : (prefixWord ++ tailWord_4769724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769724).length < 2 ^ (prefixWord ++ tailWord_4769724).sum := by decide
  have hdescent : baseEnd_4769724 < baseStart_4769724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769770 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_4769770 : Nat := 118140960795 + 4769770 * 2 ^ 59
def prefixEnd_4769770 : Nat := 4983230072969 + 3 ^ 40 * 4769770 * 2
def baseEnd_4769770 : Nat := 2449184621395908486639233

theorem tailTrace_4769770 : CollatzResearch.WordTrace tailWord_4769770 prefixEnd_4769770 2449184621395908486639233 := by
  unfold tailWord_4769770
  simp only [CollatzResearch.WordTrace]
  refine ⟨43491950982486344176636691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115978535953296917804364509 43491950982486344176636691)
  ·
    refine ⟨65237926473729516264955037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43491950982486344176636691 65237926473729516264955037)
    ·
      refine ⟨24464222427648568599358139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65237926473729516264955037 24464222427648568599358139)
      ·
        refine ⟨36696333641472852899037209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24464222427648568599358139 36696333641472852899037209)
        ·
          refine ⟨27522250231104639674277907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36696333641472852899037209 27522250231104639674277907)
          ·
            refine ⟨41283375346656959511416861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27522250231104639674277907 41283375346656959511416861)
            ·
              refine ⟨15481265754996359816781323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41283375346656959511416861 15481265754996359816781323)
              ·
                refine ⟨23221898632494539725171985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15481265754996359816781323 23221898632494539725171985)
                ·
                  refine ⟨17416423974370904793878989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23221898632494539725171985 17416423974370904793878989)
                  ·
                    refine ⟨6531158990389089297704621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17416423974370904793878989 6531158990389089297704621)
                    ·
                      refine ⟨2449184621395908486639233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6531158990389089297704621 2449184621395908486639233)
                      ·
                        rfl

theorem cell23_4769770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_4769770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769770 prefixEnd_4769770 := by exact prefixLift 4769770
  have htrace : WordTrace (prefixWord ++ tailWord_4769770) baseStart_4769770 baseEnd_4769770 := by
    simpa [prefixWord, tailWord_4769770, baseEnd_4769770] using wordTrace_append hprefix tailTrace_4769770
  have hstable : (prefixWord ++ tailWord_4769770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769770).length < 2 ^ (prefixWord ++ tailWord_4769770).sum := by decide
  have hdescent : baseEnd_4769770 < baseStart_4769770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769823 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 6]
def baseStart_4769823 : Nat := 118140960795 + 4769823 * 2 ^ 59
def prefixEnd_4769823 : Nat := 4983230072969 + 3 ^ 40 * 4769823 * 2
def baseEnd_4769823 : Nat := 2449211835870596779276489

theorem tailTrace_4769823 : CollatzResearch.WordTrace tailWord_4769823 prefixEnd_4769823 2449211835870596779276489 := by
  unfold tailWord_4769823
  simp only [CollatzResearch.WordTrace]
  refine ⟨173969736998753366758226123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115979824665835577838817415 173969736998753366758226123)
  ·
    refine ⟨260954605498130050137339185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173969736998753366758226123 260954605498130050137339185)
    ·
      refine ⟨195715954123597537603004389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260954605498130050137339185 195715954123597537603004389)
      ·
        refine ⟨36696741398174538300563323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195715954123597537603004389 36696741398174538300563323)
        ·
          refine ⟨55045112097261807450844985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36696741398174538300563323 55045112097261807450844985)
          ·
            refine ⟨41283834072946355588133739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55045112097261807450844985 41283834072946355588133739)
            ·
              refine ⟨61925751109419533382200609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41283834072946355588133739 61925751109419533382200609)
              ·
                refine ⟨46444313332064650036650457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61925751109419533382200609 46444313332064650036650457)
                ·
                  refine ⟨34833234999048487527487843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46444313332064650036650457 34833234999048487527487843)
                  ·
                    refine ⟨52249852498572731291231765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34833234999048487527487843 52249852498572731291231765)
                    ·
                      refine ⟨2449211835870596779276489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52249852498572731291231765 2449211835870596779276489)
                      ·
                        rfl

theorem cell23_4769823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_4769823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769823 prefixEnd_4769823 := by exact prefixLift 4769823
  have htrace : WordTrace (prefixWord ++ tailWord_4769823) baseStart_4769823 baseEnd_4769823 := by
    simpa [prefixWord, tailWord_4769823, baseEnd_4769823] using wordTrace_append hprefix tailTrace_4769823
  have hstable : (prefixWord ++ tailWord_4769823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769823).length < 2 ^ (prefixWord ++ tailWord_4769823).sum := by decide
  have hdescent : baseEnd_4769823 < baseStart_4769823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769873 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_4769873 : Nat := 118140960795 + 4769873 * 2 ^ 59
def prefixEnd_4769873 : Nat := 4983230072969 + 3 ^ 40 * 4769873 * 2
def baseEnd_4769873 : Nat := 2449237509903321583651259

theorem tailTrace_4769873 : CollatzResearch.WordTrace tailWord_4769873 prefixEnd_4769873 2449237509903321583651259 := by
  unfold tailWord_4769873
  simp only [CollatzResearch.WordTrace]
  refine ⟨173971560648572225297546273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115981040432381483531697515 173971560648572225297546273)
  ·
    refine ⟨130478670486429168973159705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173971560648572225297546273 130478670486429168973159705)
    ·
      refine ⟨97859002864821876729869779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130478670486429168973159705 97859002864821876729869779)
      ·
        refine ⟨146788504297232815094804669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97859002864821876729869779 146788504297232815094804669)
        ·
          refine ⟨55045689111462305660551751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146788504297232815094804669 55045689111462305660551751)
          ·
            refine ⟨82568533667193458490827627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55045689111462305660551751 82568533667193458490827627)
            ·
              refine ⟨123852800500790187736241441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82568533667193458490827627 123852800500790187736241441)
              ·
                refine ⟨92889600375592640802181081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123852800500790187736241441 92889600375592640802181081)
                ·
                  refine ⟨69667200281694480601635811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92889600375592640802181081 69667200281694480601635811)
                  ·
                    refine ⟨104500800422541720902453717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69667200281694480601635811 104500800422541720902453717)
                    ·
                      refine ⟨2449237509903321583651259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104500800422541720902453717 2449237509903321583651259)
                      ·
                        rfl

theorem cell23_4769873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_4769873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769873 prefixEnd_4769873 := by exact prefixLift 4769873
  have htrace : WordTrace (prefixWord ++ tailWord_4769873) baseStart_4769873 baseEnd_4769873 := by
    simpa [prefixWord, tailWord_4769873, baseEnd_4769873] using wordTrace_append hprefix tailTrace_4769873
  have hstable : (prefixWord ++ tailWord_4769873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769873).length < 2 ^ (prefixWord ++ tailWord_4769873).sum := by decide
  have hdescent : baseEnd_4769873 < baseStart_4769873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769884 : List Nat := [2, 2, 4, 1, 1, 4, 2, 1, 6]
def baseStart_4769884 : Nat := 118140960795 + 4769884 * 2 ^ 59
def prefixEnd_4769884 : Nat := 4983230072969 + 3 ^ 40 * 4769884 * 2
def baseEnd_4769884 : Nat := 272138128687835671179301

theorem tailTrace_4769884 : CollatzResearch.WordTrace tailWord_4769884 prefixEnd_4769884 272138128687835671179301 := by
  unfold tailWord_4769884
  simp only [CollatzResearch.WordTrace]
  refine ⟨86985980925766187088098353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115981307901021582784131137 86985980925766187088098353)
  ·
    refine ⟨65239485694324640316073765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86985980925766187088098353 65239485694324640316073765)
    ·
      refine ⟨12232403567685870059263831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65239485694324640316073765 12232403567685870059263831)
      ·
        refine ⟨18348605351528805088895747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12232403567685870059263831 18348605351528805088895747)
        ·
          refine ⟨27522908027293207633343621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18348605351528805088895747 27522908027293207633343621)
          ·
            refine ⟨5160545255117476431251929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27522908027293207633343621 5160545255117476431251929)
            ·
              refine ⟨3870408941338107323438947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5160545255117476431251929 3870408941338107323438947)
              ·
                refine ⟨5805613412007160985158421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870408941338107323438947 5805613412007160985158421)
                ·
                  refine ⟨272138128687835671179301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5805613412007160985158421 272138128687835671179301)
                  ·
                    rfl

theorem cell23_4769884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_4769884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769884 prefixEnd_4769884 := by exact prefixLift 4769884
  have htrace : WordTrace (prefixWord ++ tailWord_4769884) baseStart_4769884 baseEnd_4769884 := by
    simpa [prefixWord, tailWord_4769884, baseEnd_4769884] using wordTrace_append hprefix tailTrace_4769884
  have hstable : (prefixWord ++ tailWord_4769884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769884).length < 2 ^ (prefixWord ++ tailWord_4769884).sum := by decide
  have hdescent : baseEnd_4769884 < baseStart_4769884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769904 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 2, 3, 2]
def baseStart_4769904 : Nat := 118140960795 + 4769904 * 2 ^ 59
def prefixEnd_4769904 : Nat := 4983230072969 + 3 ^ 40 * 4769904 * 2
def baseEnd_4769904 : Nat := 2449253427803610962363617

theorem tailTrace_4769904 : CollatzResearch.WordTrace tailWord_4769904 prefixEnd_4769904 2449253427803610962363617 := by
  unfold tailWord_4769904
  simp only [CollatzResearch.WordTrace]
  refine ⟨86986345655729958795962383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115981794207639945061283177 86986345655729958795962383)
  ·
    refine ⟨130479518483594938193943575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86986345655729958795962383 130479518483594938193943575)
    ·
      refine ⟨195719277725392407290915363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130479518483594938193943575 195719277725392407290915363)
      ·
        refine ⟨293578916588088610936373045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195719277725392407290915363 293578916588088610936373045)
        ·
          refine ⟨27523023430133307275284973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 293578916588088610936373045 27523023430133307275284973)
          ·
            refine ⟨10321133786299990228231865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27523023430133307275284973 10321133786299990228231865)
            ·
              refine ⟨7740850339724992671173899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10321133786299990228231865 7740850339724992671173899)
              ·
                refine ⟨11611275509587489006760849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7740850339724992671173899 11611275509587489006760849)
                ·
                  refine ⟨8708456632190616755070637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11611275509587489006760849 8708456632190616755070637)
                  ·
                    refine ⟨3265671237071481283151489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8708456632190616755070637 3265671237071481283151489)
                    ·
                      refine ⟨2449253427803610962363617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3265671237071481283151489 2449253427803610962363617)
                      ·
                        rfl

theorem cell23_4769904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 2, 3, 2].length) (baseStart_4769904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769904 prefixEnd_4769904 := by exact prefixLift 4769904
  have htrace : WordTrace (prefixWord ++ tailWord_4769904) baseStart_4769904 baseEnd_4769904 := by
    simpa [prefixWord, tailWord_4769904, baseEnd_4769904] using wordTrace_append hprefix tailTrace_4769904
  have hstable : (prefixWord ++ tailWord_4769904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769904).length < 2 ^ (prefixWord ++ tailWord_4769904).sum := by decide
  have hdescent : baseEnd_4769904 < baseStart_4769904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769923 : List Nat := [1, 1, 1, 3, 3, 14]
def baseStart_4769923 : Nat := 118140960795 + 4769923 * 2 ^ 59
def prefixEnd_4769923 : Nat := 4983230072969 + 3 ^ 40 * 4769923 * 2
def baseEnd_4769923 : Nat := 10079272361876734107103

theorem tailTrace_4769923 : CollatzResearch.WordTrace tailWord_4769923 prefixEnd_4769923 10079272361876734107103 := by
  unfold tailWord_4769923
  simp only [CollatzResearch.WordTrace]
  refine ⟨173973384298391083836866423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115982256198927389224577615 173973384298391083836866423)
  ·
    refine ⟨260960076447586625755299635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173973384298391083836866423 260960076447586625755299635)
    ·
      refine ⟨391440114671379938632949453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260960076447586625755299635 391440114671379938632949453)
      ·
        refine ⟨146790043001767476987356045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 391440114671379938632949453 146790043001767476987356045)
        ·
          refine ⟨55046266125662803870258517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146790043001767476987356045 55046266125662803870258517)
          ·
            refine ⟨10079272361876734107103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 55046266125662803870258517 10079272361876734107103)
            ·
              rfl

theorem cell23_4769923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 14].length) (baseStart_4769923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769923 prefixEnd_4769923 := by exact prefixLift 4769923
  have htrace : WordTrace (prefixWord ++ tailWord_4769923) baseStart_4769923 baseEnd_4769923 := by
    simpa [prefixWord, tailWord_4769923, baseEnd_4769923] using wordTrace_append hprefix tailTrace_4769923
  have hstable : (prefixWord ++ tailWord_4769923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769923).length < 2 ^ (prefixWord ++ tailWord_4769923).sum := by decide
  have hdescent : baseEnd_4769923 < baseStart_4769923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769927 : List Nat := [1, 1, 4, 2, 1, 1, 3, 4, 2, 4]
def baseStart_4769927 : Nat := 118140960795 + 4769927 * 2 ^ 59
def prefixEnd_4769927 : Nat := 4983230072969 + 3 ^ 40 * 4769927 * 2
def baseEnd_4769927 : Nat := 816421745952888124125337

theorem tailTrace_4769927 : CollatzResearch.WordTrace tailWord_4769927 prefixEnd_4769927 816421745952888124125337 := by
  unfold tailWord_4769927
  simp only [CollatzResearch.WordTrace]
  refine ⟨173973530190376592520012035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115982353460251061680008023 173973530190376592520012035)
  ·
    refine ⟨260960295285564888780018053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173973530190376592520012035 260960295285564888780018053)
    ·
      refine ⟨48930055366043416646253385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260960295285564888780018053 48930055366043416646253385)
      ·
        refine ⟨36697541524532562484690039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48930055366043416646253385 36697541524532562484690039)
        ·
          refine ⟨55046312286798843727035059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36697541524532562484690039 55046312286798843727035059)
          ·
            refine ⟨82569468430198265590552589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55046312286798843727035059 82569468430198265590552589)
            ·
              refine ⟨30963550661324349596457221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82569468430198265590552589 30963550661324349596457221)
              ·
                refine ⟨5805665748998315549335729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30963550661324349596457221 5805665748998315549335729)
                ·
                  refine ⟨4354249311748736662001797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5805665748998315549335729 4354249311748736662001797)
                  ·
                    refine ⟨816421745952888124125337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4354249311748736662001797 816421745952888124125337)
                    ·
                      rfl

theorem cell23_4769927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_4769927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769927 prefixEnd_4769927 := by exact prefixLift 4769927
  have htrace : WordTrace (prefixWord ++ tailWord_4769927) baseStart_4769927 baseEnd_4769927 := by
    simpa [prefixWord, tailWord_4769927, baseEnd_4769927] using wordTrace_append hprefix tailTrace_4769927
  have hstable : (prefixWord ++ tailWord_4769927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769927).length < 2 ^ (prefixWord ++ tailWord_4769927).sum := by decide
  have hdescent : baseEnd_4769927 < baseStart_4769927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769928 : List Nat := [2, 1, 3, 4, 1, 1, 4, 2, 1, 1, 3]
def baseStart_4769928 : Nat := 118140960795 + 4769928 * 2 ^ 59
def prefixEnd_4769928 : Nat := 4983230072969 + 3 ^ 40 * 4769928 * 2
def baseEnd_4769928 : Nat := 2449265751339318868463507

theorem tailTrace_4769928 : CollatzResearch.WordTrace tailWord_4769928 prefixEnd_4769928 2449265751339318868463507 := by
  unfold tailWord_4769928
  simp only [CollatzResearch.WordTrace]
  refine ⟨86986783331686484845399219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115982377775581979793865625 86986783331686484845399219)
  ·
    refine ⟨130480174997529727268098829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86986783331686484845399219 130480174997529727268098829)
    ·
      refine ⟨48930065624073647725537061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130480174997529727268098829 48930065624073647725537061)
      ·
        refine ⟨9174387304513808948538199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48930065624073647725537061 9174387304513808948538199)
        ·
          refine ⟨13761580956770713422807299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9174387304513808948538199 13761580956770713422807299)
          ·
            refine ⟨20642371435156070134210949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13761580956770713422807299 20642371435156070134210949)
            ·
              refine ⟨3870444644091763150164553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20642371435156070134210949 3870444644091763150164553)
              ·
                refine ⟨2902833483068822362623415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3870444644091763150164553 2902833483068822362623415)
                ·
                  refine ⟨4354250224603233543935123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902833483068822362623415 4354250224603233543935123)
                  ·
                    refine ⟨6531375336904850315902685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4354250224603233543935123 6531375336904850315902685)
                    ·
                      refine ⟨2449265751339318868463507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6531375336904850315902685 2449265751339318868463507)
                      ·
                        rfl

theorem cell23_4769928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_4769928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769928 prefixEnd_4769928 := by exact prefixLift 4769928
  have htrace : WordTrace (prefixWord ++ tailWord_4769928) baseStart_4769928 baseEnd_4769928 := by
    simpa [prefixWord, tailWord_4769928, baseEnd_4769928] using wordTrace_append hprefix tailTrace_4769928
  have hstable : (prefixWord ++ tailWord_4769928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769928).length < 2 ^ (prefixWord ++ tailWord_4769928).sum := by decide
  have hdescent : baseEnd_4769928 < baseStart_4769928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769951 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 3, 2, 2]
def baseStart_4769951 : Nat := 118140960795 + 4769951 * 2 ^ 59
def prefixEnd_4769951 : Nat := 4983230072969 + 3 ^ 40 * 4769951 * 2
def baseEnd_4769951 : Nat := 2449277561394372278475901

theorem tailTrace_4769951 : CollatzResearch.WordTrace tailWord_4769951 prefixEnd_4769951 2449277561394372278475901 := by
  unfold tailWord_4769951
  simp only [CollatzResearch.WordTrace]
  refine ⟨173974405542289644618885707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115982937028193096412590471 173974405542289644618885707)
  ·
    refine ⟨260961608313434466928328561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173974405542289644618885707 260961608313434466928328561)
    ·
      refine ⟨195721206235075850196246421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260961608313434466928328561 195721206235075850196246421)
      ·
        refine ⟨9174431542269180477949051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 195721206235075850196246421 9174431542269180477949051)
        ·
          refine ⟨13761647313403770716923577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9174431542269180477949051 13761647313403770716923577)
          ·
            refine ⟨10321235485052828037692683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13761647313403770716923577 10321235485052828037692683)
            ·
              refine ⟨15481853227579242056539025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10321235485052828037692683 15481853227579242056539025)
              ·
                refine ⟨11611389920684431542404269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15481853227579242056539025 11611389920684431542404269)
                ·
                  refine ⟨4354271220256661828401601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11611389920684431542404269 4354271220256661828401601)
                  ·
                    refine ⟨3265703415192496371301201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4354271220256661828401601 3265703415192496371301201)
                    ·
                      refine ⟨2449277561394372278475901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3265703415192496371301201 2449277561394372278475901)
                      ·
                        rfl

theorem cell23_4769951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_4769951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769951 prefixEnd_4769951 := by exact prefixLift 4769951
  have htrace : WordTrace (prefixWord ++ tailWord_4769951) baseStart_4769951 baseEnd_4769951 := by
    simpa [prefixWord, tailWord_4769951, baseEnd_4769951] using wordTrace_append hprefix tailTrace_4769951
  have hstable : (prefixWord ++ tailWord_4769951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769951).length < 2 ^ (prefixWord ++ tailWord_4769951).sum := by decide
  have hdescent : baseEnd_4769951 < baseStart_4769951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769954 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_4769954 : Nat := 118140960795 + 4769954 * 2 ^ 59
def prefixEnd_4769954 : Nat := 4983230072969 + 3 ^ 40 * 4769954 * 2
def baseEnd_4769954 : Nat := 2449279101836335766738387

theorem tailTrace_4769954 : CollatzResearch.WordTrace tailWord_4769954 prefixEnd_4769954 2449279101836335766738387 := by
  unfold tailWord_4769954
  simp only [CollatzResearch.WordTrace]
  refine ⟨43493628740319694032811229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115983009974185850754163277 43493628740319694032811229)
  ·
    refine ⟨16310110777619885262304211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43493628740319694032811229 16310110777619885262304211)
    ·
      refine ⟨24465166166429827893456317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16310110777619885262304211 24465166166429827893456317)
      ·
        refine ⟨9174437312411185460046119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24465166166429827893456317 9174437312411185460046119)
        ·
          refine ⟨13761655968616778190069179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9174437312411185460046119 13761655968616778190069179)
          ·
            refine ⟨20642483952925167285103769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13761655968616778190069179 20642483952925167285103769)
            ·
              refine ⟨15481862964693875463827827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20642483952925167285103769 15481862964693875463827827)
              ·
                refine ⟨23222794447040813195741741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15481862964693875463827827 23222794447040813195741741)
                ·
                  refine ⟨8708547917640304948403153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23222794447040813195741741 8708547917640304948403153)
                  ·
                    refine ⟨6531410938230228711302365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8708547917640304948403153 6531410938230228711302365)
                    ·
                      refine ⟨2449279101836335766738387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6531410938230228711302365 2449279101836335766738387)
                      ·
                        rfl

theorem cell23_4769954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_4769954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769954 prefixEnd_4769954 := by exact prefixLift 4769954
  have htrace : WordTrace (prefixWord ++ tailWord_4769954) baseStart_4769954 baseEnd_4769954 := by
    simpa [prefixWord, tailWord_4769954, baseEnd_4769954] using wordTrace_append hprefix tailTrace_4769954
  have hstable : (prefixWord ++ tailWord_4769954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769954).length < 2 ^ (prefixWord ++ tailWord_4769954).sum := by decide
  have hdescent : baseEnd_4769954 < baseStart_4769954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769967 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 4, 1, 3]
def baseStart_4769967 : Nat := 118140960795 + 4769967 * 2 ^ 59
def prefixEnd_4769967 : Nat := 4983230072969 + 3 ^ 40 * 4769967 * 2
def baseEnd_4769967 : Nat := 2449285777084844215875827

theorem tailTrace_4769967 : CollatzResearch.WordTrace tailWord_4769967 prefixEnd_4769967 2449285777084844215875827 := by
  unfold tailWord_4769967
  simp only [CollatzResearch.WordTrace]
  refine ⟨173974989110231679351468155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115983326073487786234312103 173974989110231679351468155)
  ·
    refine ⟨260962483665347519027202233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173974989110231679351468155 260962483665347519027202233)
    ·
      refine ⟨195721862749010639270401675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260962483665347519027202233 195721862749010639270401675)
      ·
        refine ⟨293582794123515958905602513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195721862749010639270401675 293582794123515958905602513)
        ·
          refine ⟨220187095592636969179201885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293582794123515958905602513 220187095592636969179201885)
          ·
            refine ⟨82570160847238863442200707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220187095592636969179201885 82570160847238863442200707)
            ·
              refine ⟨123855241270858295163301061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82570160847238863442200707 123855241270858295163301061)
              ·
                refine ⟨23222857738285930343118949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123855241270858295163301061 23222857738285930343118949)
                ·
                  refine ⟨4354285825928611939334803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23222857738285930343118949 4354285825928611939334803)
                  ·
                    refine ⟨6531428738892917909002205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4354285825928611939334803 6531428738892917909002205)
                    ·
                      refine ⟨2449285777084844215875827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6531428738892917909002205 2449285777084844215875827)
                      ·
                        rfl

theorem cell23_4769967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 1, 3].length) (baseStart_4769967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769967 prefixEnd_4769967 := by exact prefixLift 4769967
  have htrace : WordTrace (prefixWord ++ tailWord_4769967) baseStart_4769967 baseEnd_4769967 := by
    simpa [prefixWord, tailWord_4769967, baseEnd_4769967] using wordTrace_append hprefix tailTrace_4769967
  have hstable : (prefixWord ++ tailWord_4769967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769967).length < 2 ^ (prefixWord ++ tailWord_4769967).sum := by decide
  have hdescent : baseEnd_4769967 < baseStart_4769967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4769984 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 4, 1, 3]
def baseStart_4769984 : Nat := 118140960795 + 4769984 * 2 ^ 59
def prefixEnd_4769984 : Nat := 4983230072969 + 3 ^ 40 * 4769984 * 2
def baseEnd_4769984 : Nat := 2449294506255970649363249

theorem tailTrace_4769984 : CollatzResearch.WordTrace tailWord_4769984 prefixEnd_4769984 2449294506255970649363249 := by
  unfold tailWord_4769984
  simp only [CollatzResearch.WordTrace]
  refine ⟨86987804575585045627418503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115983739434113394169891337 86987804575585045627418503)
  ·
    refine ⟨130481706863377568441127755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86987804575585045627418503 130481706863377568441127755)
    ·
      refine ⟨195722560295066352661691633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130481706863377568441127755 195722560295066352661691633)
      ·
        refine ⟨146791920221299764496268725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195722560295066352661691633 146791920221299764496268725)
        ·
          refine ⟨13761742520746852921525193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146791920221299764496268725 13761742520746852921525193)
          ·
            refine ⟨10321306890560139691143895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13761742520746852921525193 10321306890560139691143895)
            ·
              refine ⟨15481960335840209536715843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10321306890560139691143895 15481960335840209536715843)
              ·
                refine ⟨23222940503760314305073765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15481960335840209536715843 23222940503760314305073765)
                ·
                  refine ⟨4354301344455058932201331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23222940503760314305073765 4354301344455058932201331)
                  ·
                    refine ⟨6531452016682588398301997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4354301344455058932201331 6531452016682588398301997)
                    ·
                      refine ⟨2449294506255970649363249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6531452016682588398301997 2449294506255970649363249)
                      ·
                        rfl

theorem cell23_4769984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_4769984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4769984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4769984 prefixEnd_4769984 := by exact prefixLift 4769984
  have htrace : WordTrace (prefixWord ++ tailWord_4769984) baseStart_4769984 baseEnd_4769984 := by
    simpa [prefixWord, tailWord_4769984, baseEnd_4769984] using wordTrace_append hprefix tailTrace_4769984
  have hstable : (prefixWord ++ tailWord_4769984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4769984).length < 2 ^ (prefixWord ++ tailWord_4769984).sum := by decide
  have hdescent : baseEnd_4769984 < baseStart_4769984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4769984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770058 : List Nat := [3, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2]
def baseStart_4770058 : Nat := 118140960795 + 4770058 * 2 ^ 59
def prefixEnd_4770058 : Nat := 4983230072969 + 3 ^ 40 * 4770058 * 2
def baseEnd_4770058 : Nat := 2449332503824403359837909

theorem tailTrace_4770058 : CollatzResearch.WordTrace tailWord_4770058 prefixEnd_4770058 2449332503824403359837909 := by
  unfold tailWord_4770058
  simp only [CollatzResearch.WordTrace]
  refine ⟨43494577038225500473257707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115985538768601334595353885 43494577038225500473257707)
  ·
    refine ⟨65241865557338250709886561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43494577038225500473257707 65241865557338250709886561)
    ·
      refine ⟨48931399168003688032414921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65241865557338250709886561 48931399168003688032414921)
      ·
        refine ⟨36698549376002766024311191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48931399168003688032414921 36698549376002766024311191)
        ·
          refine ⟨55047824064004149036466787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36698549376002766024311191 55047824064004149036466787)
          ·
            refine ⟨82571736096006223554700181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55047824064004149036466787 82571736096006223554700181)
            ·
              refine ⟨3870550129500291729126571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82571736096006223554700181 3870550129500291729126571)
              ·
                refine ⟨5805825194250437593689857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870550129500291729126571 5805825194250437593689857)
                ·
                  refine ⟨4354368895687828195267393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5805825194250437593689857 4354368895687828195267393)
                  ·
                    refine ⟨3265776671765871146450545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4354368895687828195267393 3265776671765871146450545)
                    ·
                      refine ⟨2449332503824403359837909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3265776671765871146450545 2449332503824403359837909)
                      ·
                        rfl

theorem cell23_4770058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_4770058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770058 prefixEnd_4770058 := by exact prefixLift 4770058
  have htrace : WordTrace (prefixWord ++ tailWord_4770058) baseStart_4770058 baseEnd_4770058 := by
    simpa [prefixWord, tailWord_4770058, baseEnd_4770058] using wordTrace_append hprefix tailTrace_4770058
  have hstable : (prefixWord ++ tailWord_4770058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770058).length < 2 ^ (prefixWord ++ tailWord_4770058).sum := by decide
  have hdescent : baseEnd_4770058 < baseStart_4770058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770098 : List Nat := [3, 2, 1, 1, 5, 2, 2, 2, 5]
def baseStart_4770098 : Nat := 118140960795 + 4770098 * 2 ^ 59
def prefixEnd_4770098 : Nat := 4983230072969 + 3 ^ 40 * 4770098 * 2
def baseEnd_4770098 : Nat := 272150338116731467037525

theorem tailTrace_4770098 : CollatzResearch.WordTrace tailWord_4770098 prefixEnd_4770098 272150338116731467037525 := by
  unfold tailWord_4770098
  simp only [CollatzResearch.WordTrace]
  refine ⟨43494941768189272181121737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115986511381838059149657965 43494941768189272181121737)
  ·
    refine ⟨32621206326141954135841303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43494941768189272181121737 32621206326141954135841303)
    ·
      refine ⟨48931809489212931203761955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32621206326141954135841303 48931809489212931203761955)
      ·
        refine ⟨73397714233819396805642933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48931809489212931203761955 73397714233819396805642933)
        ·
          refine ⟨6881035709420568450529025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73397714233819396805642933 6881035709420568450529025)
          ·
            refine ⟨5160776782065426337896769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6881035709420568450529025 5160776782065426337896769)
            ·
              refine ⟨3870582586549069753422577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5160776782065426337896769 3870582586549069753422577)
              ·
                refine ⟨2902936939911802315066933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3870582586549069753422577 2902936939911802315066933)
                ·
                  refine ⟨272150338116731467037525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2902936939911802315066933 272150338116731467037525)
                  ·
                    rfl

theorem cell23_4770098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_4770098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770098 prefixEnd_4770098 := by exact prefixLift 4770098
  have htrace : WordTrace (prefixWord ++ tailWord_4770098) baseStart_4770098 baseEnd_4770098 := by
    simpa [prefixWord, tailWord_4770098, baseEnd_4770098] using wordTrace_append hprefix tailTrace_4770098
  have hstable : (prefixWord ++ tailWord_4770098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770098).length < 2 ^ (prefixWord ++ tailWord_4770098).sum := by decide
  have hdescent : baseEnd_4770098 < baseStart_4770098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770124 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 3, 4]
def baseStart_4770124 : Nat := 118140960795 + 4770124 * 2 ^ 59
def prefixEnd_4770124 : Nat := 4983230072969 + 3 ^ 40 * 4770124 * 2
def baseEnd_4770124 : Nat := 816455464515866700537535

theorem tailTrace_4770124 : CollatzResearch.WordTrace tailWord_4770124 prefixEnd_4770124 816455464515866700537535 := by
  unfold tailWord_4770124
  simp only [CollatzResearch.WordTrace]
  refine ⟨86990357685331447582466713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115987143580441930109955617 86990357685331447582466713)
  ·
    refine ⟨65242768263998585686850035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86990357685331447582466713 65242768263998585686850035)
    ·
      refine ⟨97864152395997878530275053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65242768263998585686850035 97864152395997878530275053)
      ·
        refine ⟨36699057148499204448853145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97864152395997878530275053 36699057148499204448853145)
        ·
          refine ⟨27524292861374403336639859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36699057148499204448853145 27524292861374403336639859)
          ·
            refine ⟨41286439292061605004959789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27524292861374403336639859 41286439292061605004959789)
            ·
              refine ⟨15482414734523101876859921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41286439292061605004959789 15482414734523101876859921)
              ·
                refine ⟨11611811050892326407644941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15482414734523101876859921 11611811050892326407644941)
                ·
                  refine ⟨4354429144084622402866853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11611811050892326407644941 4354429144084622402866853)
                  ·
                    refine ⟨816455464515866700537535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4354429144084622402866853 816455464515866700537535)
                    ·
                      rfl

theorem cell23_4770124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_4770124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770124 prefixEnd_4770124 := by exact prefixLift 4770124
  have htrace : WordTrace (prefixWord ++ tailWord_4770124) baseStart_4770124 baseEnd_4770124 := by
    simpa [prefixWord, tailWord_4770124, baseEnd_4770124] using wordTrace_append hprefix tailTrace_4770124
  have hstable : (prefixWord ++ tailWord_4770124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770124).length < 2 ^ (prefixWord ++ tailWord_4770124).sum := by decide
  have hdescent : baseEnd_4770124 < baseStart_4770124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770154 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 8]
def baseStart_4770154 : Nat := 118140960795 + 4770154 * 2 ^ 59
def prefixEnd_4770154 : Nat := 4983230072969 + 3 ^ 40 * 4770154 * 2
def baseEnd_4770154 : Nat := 272153533107470553804163

theorem tailTrace_4770154 : CollatzResearch.WordTrace tailWord_4770154 prefixEnd_4770154 272153533107470553804163 := by
  unfold tailWord_4770154
  simp only [CollatzResearch.WordTrace]
  refine ⟨43495452390138552572131379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115987873040369473525683677 43495452390138552572131379)
  ·
    refine ⟨65243178585207828858197069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43495452390138552572131379 65243178585207828858197069)
    ·
      refine ⟨24466191969452935821823901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65243178585207828858197069 24466191969452935821823901)
      ·
        refine ⟨9174821988544850933183963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24466191969452935821823901 9174821988544850933183963)
        ·
          refine ⟨13762232982817276399775945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9174821988544850933183963 13762232982817276399775945)
          ·
            refine ⟨10321674737112957299831959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13762232982817276399775945 10321674737112957299831959)
            ·
              refine ⟨15482512105669435949747939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10321674737112957299831959 15482512105669435949747939)
              ·
                refine ⟨23223768158504153924621909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15482512105669435949747939 23223768158504153924621909)
                ·
                  refine ⟨272153533107470553804163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23223768158504153924621909 272153533107470553804163)
                  ·
                    rfl

theorem cell23_4770154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_4770154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770154 prefixEnd_4770154 := by exact prefixLift 4770154
  have htrace : WordTrace (prefixWord ++ tailWord_4770154) baseStart_4770154 baseEnd_4770154 := by
    simpa [prefixWord, tailWord_4770154, baseEnd_4770154] using wordTrace_append hprefix tailTrace_4770154
  have hstable : (prefixWord ++ tailWord_4770154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770154).length < 2 ^ (prefixWord ++ tailWord_4770154).sum := by decide
  have hdescent : baseEnd_4770154 < baseStart_4770154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770157 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_4770157 : Nat := 118140960795 + 4770157 * 2 ^ 59
def prefixEnd_4770157 : Nat := 4983230072969 + 3 ^ 40 * 4770157 * 2
def baseEnd_4770157 : Nat := 2449383338409198472499953

theorem tailTrace_4770157 : CollatzResearch.WordTrace tailWord_4770157 prefixEnd_4770157 2449383338409198472499953 := by
  unfold tailWord_4770157
  simp only [CollatzResearch.WordTrace]
  refine ⟨173981918979543341800884725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115987945986362227867256483 173981918979543341800884725)
  ·
    refine ⟨16310804904332188293832943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173981918979543341800884725 16310804904332188293832943)
    ·
      refine ⟨24466207356498282440749415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16310804904332188293832943 24466207356498282440749415)
      ·
        refine ⟨36699311034747423661124123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24466207356498282440749415 36699311034747423661124123)
        ·
          refine ⟨55048966552121135491686185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36699311034747423661124123 55048966552121135491686185)
          ·
            refine ⟨41286724914090851618764639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55048966552121135491686185 41286724914090851618764639)
            ·
              refine ⟨61930087371136277428146959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41286724914090851618764639 61930087371136277428146959)
              ·
                refine ⟨92895131056704416142220439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61930087371136277428146959 92895131056704416142220439)
                ·
                  refine ⟨139342696585056624213330659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92895131056704416142220439 139342696585056624213330659)
                  ·
                    refine ⟨209014044877584936319995989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139342696585056624213330659 209014044877584936319995989)
                    ·
                      refine ⟨2449383338409198472499953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 209014044877584936319995989 2449383338409198472499953)
                      ·
                        rfl

theorem cell23_4770157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_4770157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770157 prefixEnd_4770157 := by exact prefixLift 4770157
  have htrace : WordTrace (prefixWord ++ tailWord_4770157) baseStart_4770157 baseEnd_4770157 := by
    simpa [prefixWord, tailWord_4770157, baseEnd_4770157] using wordTrace_append hprefix tailTrace_4770157
  have hstable : (prefixWord ++ tailWord_4770157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770157).length < 2 ^ (prefixWord ++ tailWord_4770157).sum := by decide
  have hdescent : baseEnd_4770157 < baseStart_4770157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770167 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 3, 5]
def baseStart_4770167 : Nat := 118140960795 + 4770167 * 2 ^ 59
def prefixEnd_4770167 : Nat := 4983230072969 + 3 ^ 40 * 4770167 * 2
def baseEnd_4770167 : Nat := 816462824405247811124969

theorem tailTrace_4770167 : CollatzResearch.WordTrace tailWord_4770167 prefixEnd_4770167 816462824405247811124969 := by
  unfold tailWord_4770167
  simp only [CollatzResearch.WordTrace]
  refine ⟨173982283709507113508748755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115988189139671409005832503 173982283709507113508748755)
  ·
    refine ⟨260973425564260670263123133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173982283709507113508748755 260973425564260670263123133)
    ·
      refine ⟨97865034586597751348671175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260973425564260670263123133 97865034586597751348671175)
      ·
        refine ⟨146797551879896627023006763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97865034586597751348671175 146797551879896627023006763)
        ·
          refine ⟨220196327819844940534510145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146797551879896627023006763 220196327819844940534510145)
          ·
            refine ⟨165147245864883705400882609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220196327819844940534510145 165147245864883705400882609)
            ·
              refine ⟨123860434398662779050661957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165147245864883705400882609 123860434398662779050661957)
              ·
                refine ⟨23223831449749271071999117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123860434398662779050661957 23223831449749271071999117)
                ·
                  refine ⟨8708936793655976651999669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23223831449749271071999117 8708936793655976651999669)
                  ·
                    refine ⟨816462824405247811124969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8708936793655976651999669 816462824405247811124969)
                    ·
                      rfl

theorem cell23_4770167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_4770167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770167 prefixEnd_4770167 := by exact prefixLift 4770167
  have htrace : WordTrace (prefixWord ++ tailWord_4770167) baseStart_4770167 baseEnd_4770167 := by
    simpa [prefixWord, tailWord_4770167, baseEnd_4770167] using wordTrace_append hprefix tailTrace_4770167
  have hstable : (prefixWord ++ tailWord_4770167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770167).length < 2 ^ (prefixWord ++ tailWord_4770167).sum := by decide
  have hdescent : baseEnd_4770167 < baseStart_4770167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770197 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 3, 6]
def baseStart_4770197 : Nat := 118140960795 + 4770197 * 2 ^ 59
def prefixEnd_4770197 : Nat := 4983230072969 + 3 ^ 40 * 4770197 * 2
def baseEnd_4770197 : Nat := 816467959211792771999923

theorem tailTrace_4770197 : CollatzResearch.WordTrace tailWord_4770197 prefixEnd_4770197 816467959211792771999923 := by
  unfold tailWord_4770197
  simp only [CollatzResearch.WordTrace]
  refine ⟨173983377899398428632340845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115988918599598952421560563 173983377899398428632340845)
  ·
    refine ⟨65243766712274410737127817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173983377899398428632340845 65243766712274410737127817)
    ·
      refine ⟨48932825034205808052845863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65243766712274410737127817 48932825034205808052845863)
      ·
        refine ⟨73399237551308712079268795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48932825034205808052845863 73399237551308712079268795)
        ·
          refine ⟨110098856326963068118903193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73399237551308712079268795 110098856326963068118903193)
          ·
            refine ⟨82574142245222301089177395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110098856326963068118903193 82574142245222301089177395)
            ·
              refine ⟨123861213367833451633766093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82574142245222301089177395 123861213367833451633766093)
              ·
                refine ⟨46447955012937544362662285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123861213367833451633766093 46447955012937544362662285)
                ·
                  refine ⟨17417983129851579135998357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46447955012937544362662285 17417983129851579135998357)
                  ·
                    refine ⟨816467959211792771999923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17417983129851579135998357 816467959211792771999923)
                    ·
                      rfl

theorem cell23_4770197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_4770197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770197 prefixEnd_4770197 := by exact prefixLift 4770197
  have htrace : WordTrace (prefixWord ++ tailWord_4770197) baseStart_4770197 baseEnd_4770197 := by
    simpa [prefixWord, tailWord_4770197, baseEnd_4770197] using wordTrace_append hprefix tailTrace_4770197
  have hstable : (prefixWord ++ tailWord_4770197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770197).length < 2 ^ (prefixWord ++ tailWord_4770197).sum := by decide
  have hdescent : baseEnd_4770197 < baseStart_4770197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770231 : List Nat := [1, 1, 3, 1, 3, 4, 1, 3, 2, 4]
def baseStart_4770231 : Nat := 118140960795 + 4770231 * 2 ^ 59
def prefixEnd_4770231 : Nat := 4983230072969 + 3 ^ 40 * 4770231 * 2
def baseEnd_4770231 : Nat := 816473778659210394324871

theorem tailTrace_4770231 : CollatzResearch.WordTrace tailWord_4770231 prefixEnd_4770231 816473778659210394324871 := by
  unfold tailWord_4770231
  simp only [CollatzResearch.WordTrace]
  refine ⟨173984617981275252439078547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115989745320850168292719031 173984617981275252439078547)
  ·
    refine ⟨260976926971912878658617821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173984617981275252439078547 260976926971912878658617821)
    ·
      refine ⟨97866347614467329496981683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260976926971912878658617821 97866347614467329496981683)
      ·
        refine ⟨146799521421700994245472525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97866347614467329496981683 146799521421700994245472525)
        ·
          refine ⟨55049820533137872842052197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146799521421700994245472525 55049820533137872842052197)
          ·
            refine ⟨10321841349963351157884787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55049820533137872842052197 10321841349963351157884787)
            ·
              refine ⟨15482762024945026736827181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10321841349963351157884787 15482762024945026736827181)
              ·
                refine ⟨5806035759354385026310193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15482762024945026736827181 5806035759354385026310193)
                ·
                  refine ⟨4354526819515788769732645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5806035759354385026310193 4354526819515788769732645)
                  ·
                    refine ⟨816473778659210394324871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4354526819515788769732645 816473778659210394324871)
                    ·
                      rfl

theorem cell23_4770231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_4770231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770231 prefixEnd_4770231 := by exact prefixLift 4770231
  have htrace : WordTrace (prefixWord ++ tailWord_4770231) baseStart_4770231 baseEnd_4770231 := by
    simpa [prefixWord, tailWord_4770231, baseEnd_4770231] using wordTrace_append hprefix tailTrace_4770231
  have hstable : (prefixWord ++ tailWord_4770231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770231).length < 2 ^ (prefixWord ++ tailWord_4770231).sum := by decide
  have hdescent : baseEnd_4770231 < baseStart_4770231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770238 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_4770238 : Nat := 118140960795 + 4770238 * 2 ^ 59
def prefixEnd_4770238 : Nat := 4983230072969 + 3 ^ 40 * 4770238 * 2
def baseEnd_4770238 : Nat := 2449424930342212655587081

theorem tailTrace_4770238 : CollatzResearch.WordTrace tailWord_4770238 prefixEnd_4770238 2449424930342212655587081 := by
  unfold tailWord_4770238
  simp only [CollatzResearch.WordTrace]
  refine ⟨21748109161531236579322921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115989915528166595089722245 21748109161531236579322921)
  ·
    refine ⟨16311081871148427434492191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21748109161531236579322921 16311081871148427434492191)
    ·
      refine ⟨24466622806722641151738287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16311081871148427434492191 24466622806722641151738287)
      ·
        refine ⟨36699934210083961727607431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24466622806722641151738287 36699934210083961727607431)
        ·
          refine ⟨55049901315125942591411147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36699934210083961727607431 55049901315125942591411147)
          ·
            refine ⟨82574851972688913887116721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55049901315125942591411147 82574851972688913887116721)
            ·
              refine ⟨61931138979516685415337541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82574851972688913887116721 61931138979516685415337541)
              ·
                refine ⟨11612088558659378515375789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61931138979516685415337541 11612088558659378515375789)
                ·
                  refine ⟨4354533209497266943265921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11612088558659378515375789 4354533209497266943265921)
                  ·
                    refine ⟨3265899907122950207449441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4354533209497266943265921 3265899907122950207449441)
                    ·
                      refine ⟨2449424930342212655587081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3265899907122950207449441 2449424930342212655587081)
                      ·
                        rfl

theorem cell23_4770238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_4770238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770238 prefixEnd_4770238 := by exact prefixLift 4770238
  have htrace : WordTrace (prefixWord ++ tailWord_4770238) baseStart_4770238 baseEnd_4770238 := by
    simpa [prefixWord, tailWord_4770238, baseEnd_4770238] using wordTrace_append hprefix tailTrace_4770238
  have hstable : (prefixWord ++ tailWord_4770238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770238).length < 2 ^ (prefixWord ++ tailWord_4770238).sum := by decide
  have hdescent : baseEnd_4770238 < baseStart_4770238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770257 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 4, 7]
def baseStart_4770257 : Nat := 118140960795 + 4770257 * 2 ^ 59
def prefixEnd_4770257 : Nat := 4983230072969 + 3 ^ 40 * 4770257 * 2
def baseEnd_4770257 : Nat := 816478228824882693749831

theorem tailTrace_4770257 : CollatzResearch.WordTrace tailWord_4770257 prefixEnd_4770257 816478228824882693749831 := by
  unfold tailWord_4770257
  simp only [CollatzResearch.WordTrace]
  refine ⟨173985566279181058879525025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115990377519454039253016683 173985566279181058879525025)
  ·
    refine ⟨130489174709385794159643769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173985566279181058879525025 130489174709385794159643769)
    ·
      refine ⟨97866881032039345619732827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130489174709385794159643769 97866881032039345619732827)
      ·
        refine ⟨146800321548059018429599241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97866881032039345619732827 146800321548059018429599241)
        ·
          refine ⟨110100241161044263822199431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146800321548059018429599241 110100241161044263822199431)
          ·
            refine ⟨165150361741566395733299147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110100241161044263822199431 165150361741566395733299147)
            ·
              refine ⟨247725542612349593599948721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165150361741566395733299147 247725542612349593599948721)
              ·
                refine ⟨185794156959262195199961541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247725542612349593599948721 185794156959262195199961541)
                ·
                  refine ⟨34836404429861661599992789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185794156959262195199961541 34836404429861661599992789)
                  ·
                    refine ⟨816478228824882693749831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34836404429861661599992789 816478228824882693749831)
                    ·
                      rfl

theorem cell23_4770257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_4770257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770257 prefixEnd_4770257 := by exact prefixLift 4770257
  have htrace : WordTrace (prefixWord ++ tailWord_4770257) baseStart_4770257 baseEnd_4770257 := by
    simpa [prefixWord, tailWord_4770257, baseEnd_4770257] using wordTrace_append hprefix tailTrace_4770257
  have hstable : (prefixWord ++ tailWord_4770257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770257).length < 2 ^ (prefixWord ++ tailWord_4770257).sum := by decide
  have hdescent : baseEnd_4770257 < baseStart_4770257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770314 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_4770314 : Nat := 118140960795 + 4770314 * 2 ^ 59
def prefixEnd_4770314 : Nat := 4983230072969 + 3 ^ 40 * 4770314 * 2
def baseEnd_4770314 : Nat := 2449463954871954358236731

theorem tailTrace_4770314 : CollatzResearch.WordTrace tailWord_4770314 prefixEnd_4770314 2449463954871954358236731 := by
  unfold tailWord_4770314
  simp only [CollatzResearch.WordTrace]
  refine ⟨43496911309993639403587499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115991763493316371742899997 43496911309993639403587499)
  ·
    refine ⟨65245366964990459105381249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43496911309993639403587499 65245366964990459105381249)
    ·
      refine ⟨48934025223742844329035937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65245366964990459105381249 48934025223742844329035937)
      ·
        refine ⟨36700518917807133246776953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48934025223742844329035937 36700518917807133246776953)
        ·
          refine ⟨27525389188355349935082715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36700518917807133246776953 27525389188355349935082715)
          ·
            refine ⟨41288083782533024902624073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27525389188355349935082715 41288083782533024902624073)
            ·
              refine ⟨30966062836899768676968055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41288083782533024902624073 30966062836899768676968055)
              ·
                refine ⟨46449094255349653015452083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30966062836899768676968055 46449094255349653015452083)
                ·
                  refine ⟨69673641383024479523178125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46449094255349653015452083 69673641383024479523178125)
                  ·
                    refine ⟨26127615518634179821191797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69673641383024479523178125 26127615518634179821191797)
                    ·
                      refine ⟨2449463954871954358236731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26127615518634179821191797 2449463954871954358236731)
                      ·
                        rfl

theorem cell23_4770314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_4770314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770314 prefixEnd_4770314 := by exact prefixLift 4770314
  have htrace : WordTrace (prefixWord ++ tailWord_4770314) baseStart_4770314 baseEnd_4770314 := by
    simpa [prefixWord, tailWord_4770314, baseEnd_4770314] using wordTrace_append hprefix tailTrace_4770314
  have hstable : (prefixWord ++ tailWord_4770314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770314).length < 2 ^ (prefixWord ++ tailWord_4770314).sum := by decide
  have hdescent : baseEnd_4770314 < baseStart_4770314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770315 : List Nat := [1, 1, 1, 1, 7, 1, 4, 1, 1, 3, 2]
def baseStart_4770315 : Nat := 118140960795 + 4770315 * 2 ^ 59
def prefixEnd_4770315 : Nat := 4983230072969 + 3 ^ 40 * 4770315 * 2
def baseEnd_4770315 : Nat := 2449464468352608854324227

theorem tailTrace_4770315 : CollatzResearch.WordTrace tailWord_4770315 prefixEnd_4770315 2449464468352608854324227 := by
  unfold tailWord_4770315
  simp only [CollatzResearch.WordTrace]
  refine ⟨173987681712970934785136399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115991787808647289856757599 173987681712970934785136399)
  ·
    refine ⟨260981522569456402177704599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173987681712970934785136399 260981522569456402177704599)
    ·
      refine ⟨391472283854184603266556899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260981522569456402177704599 391472283854184603266556899)
      ·
        refine ⟨587208425781276904899835349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391472283854184603266556899 587208425781276904899835349)
        ·
          refine ⟨13762697479248677458589891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 587208425781276904899835349 13762697479248677458589891)
          ·
            refine ⟨20644046218873016187884837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13762697479248677458589891 20644046218873016187884837)
            ·
              refine ⟨3870758666038690535228407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20644046218873016187884837 3870758666038690535228407)
              ·
                refine ⟨5806137999058035802842611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870758666038690535228407 5806137999058035802842611)
                ·
                  refine ⟨8709206998587053704263917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5806137999058035802842611 8709206998587053704263917)
                  ·
                    refine ⟨3265952624470145139098969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8709206998587053704263917 3265952624470145139098969)
                    ·
                      refine ⟨2449464468352608854324227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3265952624470145139098969 2449464468352608854324227)
                      ·
                        rfl

theorem cell23_4770315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 1, 3, 2].length) (baseStart_4770315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770315 prefixEnd_4770315 := by exact prefixLift 4770315
  have htrace : WordTrace (prefixWord ++ tailWord_4770315) baseStart_4770315 baseEnd_4770315 := by
    simpa [prefixWord, tailWord_4770315, baseEnd_4770315] using wordTrace_append hprefix tailTrace_4770315
  have hstable : (prefixWord ++ tailWord_4770315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770315).length < 2 ^ (prefixWord ++ tailWord_4770315).sum := by decide
  have hdescent : baseEnd_4770315 < baseStart_4770315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770384 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 4]
def baseStart_4770384 : Nat := 118140960795 + 4770384 * 2 ^ 59
def prefixEnd_4770384 : Nat := 4983230072969 + 3 ^ 40 * 4770384 * 2
def baseEnd_4770384 : Nat := 2449499898517769084361409

theorem tailTrace_4770384 : CollatzResearch.WordTrace tailWord_4770384 prefixEnd_4770384 2449499898517769084361409 := by
  unfold tailWord_4770384
  simp only [CollatzResearch.WordTrace]
  refine ⟨86995099174860479784699103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115993465566480639712932137 86995099174860479784699103)
  ·
    refine ⟨130492648762290719677048655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86995099174860479784699103 130492648762290719677048655)
    ·
      refine ⟨195738973143436079515572983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130492648762290719677048655 195738973143436079515572983)
      ·
        refine ⟨293608459715154119273359475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195738973143436079515572983 293608459715154119273359475)
        ·
          refine ⟨440412689572731178910039213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293608459715154119273359475 440412689572731178910039213)
          ·
            refine ⟨165154758589774192091264705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 440412689572731178910039213 165154758589774192091264705)
            ·
              refine ⟨123866068942330644068448529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165154758589774192091264705 123866068942330644068448529)
              ·
                refine ⟨92899551706747983051336397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123866068942330644068448529 92899551706747983051336397)
                ·
                  refine ⟨34837331890030493644251149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92899551706747983051336397 34837331890030493644251149)
                  ·
                    refine ⟨13063999458761435116594181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34837331890030493644251149 13063999458761435116594181)
                    ·
                      refine ⟨2449499898517769084361409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13063999458761435116594181 2449499898517769084361409)
                      ·
                        rfl

theorem cell23_4770384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_4770384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770384 prefixEnd_4770384 := by exact prefixLift 4770384
  have htrace : WordTrace (prefixWord ++ tailWord_4770384) baseStart_4770384 baseEnd_4770384 := by
    simpa [prefixWord, tailWord_4770384, baseEnd_4770384] using wordTrace_append hprefix tailTrace_4770384
  have hstable : (prefixWord ++ tailWord_4770384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770384).length < 2 ^ (prefixWord ++ tailWord_4770384).sum := by decide
  have hdescent : baseEnd_4770384 < baseStart_4770384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770396 : List Nat := [2, 2, 4, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_4770396 : Nat := 118140960795 + 4770396 * 2 ^ 59
def prefixEnd_4770396 : Nat := 4983230072969 + 3 ^ 40 * 4770396 * 2
def baseEnd_4770396 : Nat := 2449506060285623037411355

theorem tailTrace_4770396 : CollatzResearch.WordTrace tailWord_4770396 prefixEnd_4770396 2449506060285623037411355 := by
  unfold tailWord_4770396
  simp only [CollatzResearch.WordTrace]
  refine ⟨86995318012838742809417521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115993757350451657079223361 86995318012838742809417521)
  ·
    refine ⟨65246488509629057107063141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86995318012838742809417521 65246488509629057107063141)
    ·
      refine ⟨12233716595555448207574339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65246488509629057107063141 12233716595555448207574339)
      ·
        refine ⟨18350574893333172311361509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12233716595555448207574339 18350574893333172311361509)
        ·
          refine ⟨3440732792499969808380283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18350574893333172311361509 3440732792499969808380283)
          ·
            refine ⟨5161099188749954712570425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3440732792499969808380283 5161099188749954712570425)
            ·
              refine ⟨3870824391562466034427819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5161099188749954712570425 3870824391562466034427819)
              ·
                refine ⟨5806236587343699051641729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870824391562466034427819 5806236587343699051641729)
                ·
                  refine ⟨4354677440507774288731297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5806236587343699051641729 4354677440507774288731297)
                  ·
                    refine ⟨3266008080380830716548473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4354677440507774288731297 3266008080380830716548473)
                    ·
                      refine ⟨2449506060285623037411355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3266008080380830716548473 2449506060285623037411355)
                      ·
                        rfl

theorem cell23_4770396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_4770396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770396 prefixEnd_4770396 := by exact prefixLift 4770396
  have htrace : WordTrace (prefixWord ++ tailWord_4770396) baseStart_4770396 baseEnd_4770396 := by
    simpa [prefixWord, tailWord_4770396, baseEnd_4770396] using wordTrace_append hprefix tailTrace_4770396
  have hstable : (prefixWord ++ tailWord_4770396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770396).length < 2 ^ (prefixWord ++ tailWord_4770396).sum := by decide
  have hdescent : baseEnd_4770396 < baseStart_4770396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770521 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 6]
def baseStart_4770521 : Nat := 118140960795 + 4770521 * 2 ^ 59
def prefixEnd_4770521 : Nat := 4983230072969 + 3 ^ 40 * 4770521 * 2
def baseEnd_4770521 : Nat := 2449570245367435048348279

theorem tailTrace_4770521 : CollatzResearch.WordTrace tailWord_4770521 prefixEnd_4770521 2449570245367435048348279 := by
  unfold tailWord_4770521
  simp only [CollatzResearch.WordTrace]
  refine ⟨173995195150224631967135417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115996796766816421311423611 173995195150224631967135417)
  ·
    refine ⟨130496396362668473975351563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173995195150224631967135417 130496396362668473975351563)
    ·
      refine ⟨195744594544002710963027345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130496396362668473975351563 195744594544002710963027345)
      ·
        refine ⟨146808445908002033222270509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195744594544002710963027345 146808445908002033222270509)
        ·
          refine ⟨55053167215500762458351441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146808445908002033222270509 55053167215500762458351441)
          ·
            refine ⟨41289875411625571843763581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55053167215500762458351441 41289875411625571843763581)
            ·
              refine ⟨15483703279359589441411343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41289875411625571843763581 15483703279359589441411343)
              ·
                refine ⟨23225554919039384162117015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15483703279359589441411343 23225554919039384162117015)
                ·
                  refine ⟨34838332378559076243175523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23225554919039384162117015 34838332378559076243175523)
                  ·
                    refine ⟨52257498567838614364763285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34838332378559076243175523 52257498567838614364763285)
                    ·
                      refine ⟨2449570245367435048348279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52257498567838614364763285 2449570245367435048348279)
                      ·
                        rfl

theorem cell23_4770521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_4770521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770521 prefixEnd_4770521 := by exact prefixLift 4770521
  have htrace : WordTrace (prefixWord ++ tailWord_4770521) baseStart_4770521 baseEnd_4770521 := by
    simpa [prefixWord, tailWord_4770521, baseEnd_4770521] using wordTrace_append hprefix tailTrace_4770521
  have hstable : (prefixWord ++ tailWord_4770521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770521).length < 2 ^ (prefixWord ++ tailWord_4770521).sum := by decide
  have hdescent : baseEnd_4770521 < baseStart_4770521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770536 : List Nat := [2, 1, 4, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_4770536 : Nat := 118140960795 + 4770536 * 2 ^ 59
def prefixEnd_4770536 : Nat := 4983230072969 + 3 ^ 40 * 4770536 * 2
def baseEnd_4770536 : Nat := 2449577947577252489660711

theorem tailTrace_4770536 : CollatzResearch.WordTrace tailWord_4770536 prefixEnd_4770536 2449577947577252489660711 := by
  unfold tailWord_4770536
  simp only [CollatzResearch.WordTrace]
  refine ⟨86997871122585144764465731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115997161496780193019287641 86997871122585144764465731)
  ·
    refine ⟨130496806683877717146698597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86997871122585144764465731 130496806683877717146698597)
    ·
      refine ⟨24468151253227071965005987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130496806683877717146698597 24468151253227071965005987)
      ·
        refine ⟨36702226879840607947508981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24468151253227071965005987 36702226879840607947508981)
        ·
          refine ⟨3440833769985056995078967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36702226879840607947508981 3440833769985056995078967)
          ·
            refine ⟨5161250654977585492618451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3440833769985056995078967 5161250654977585492618451)
            ·
              refine ⟨7741875982466378238927677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5161250654977585492618451 7741875982466378238927677)
              ·
                refine ⟨2903203493424891839597879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7741875982466378238927677 2903203493424891839597879)
                ·
                  refine ⟨4354805240137337759396819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2903203493424891839597879 4354805240137337759396819)
                  ·
                    refine ⟨6532207860206006639095229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4354805240137337759396819 6532207860206006639095229)
                    ·
                      refine ⟨2449577947577252489660711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6532207860206006639095229 2449577947577252489660711)
                      ·
                        rfl

theorem cell23_4770536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_4770536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770536 prefixEnd_4770536 := by exact prefixLift 4770536
  have htrace : WordTrace (prefixWord ++ tailWord_4770536) baseStart_4770536 baseEnd_4770536 := by
    simpa [prefixWord, tailWord_4770536, baseEnd_4770536] using wordTrace_append hprefix tailTrace_4770536
  have hstable : (prefixWord ++ tailWord_4770536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770536).length < 2 ^ (prefixWord ++ tailWord_4770536).sum := by decide
  have hdescent : baseEnd_4770536 < baseStart_4770536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770561 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 2, 7]
def baseStart_4770561 : Nat := 118140960795 + 4770561 * 2 ^ 59
def prefixEnd_4770561 : Nat := 4983230072969 + 3 ^ 40 * 4770561 * 2
def baseEnd_4770561 : Nat := 816530261531204963949365

theorem tailTrace_4770561 : CollatzResearch.WordTrace tailWord_4770561 prefixEnd_4770561 816530261531204963949365 := by
  unfold tailWord_4770561
  simp only [CollatzResearch.WordTrace]
  refine ⟨173996654070079718798591537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115997769380053145865727691 173996654070079718798591537)
  ·
    refine ⟨130497490552559789098943653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173996654070079718798591537 130497490552559789098943653)
    ·
      refine ⟨24468279478604960456051935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130497490552559789098943653 24468279478604960456051935)
      ·
        refine ⟨36702419217907440684077903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24468279478604960456051935 36702419217907440684077903)
        ·
          refine ⟨55053628826861161026116855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36702419217907440684077903 55053628826861161026116855)
          ·
            refine ⟨82580443240291741539175283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55053628826861161026116855 82580443240291741539175283)
            ·
              refine ⟨123870664860437612308762925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82580443240291741539175283 123870664860437612308762925)
              ·
                refine ⟨46451499322664104615786097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123870664860437612308762925 46451499322664104615786097)
                ·
                  refine ⟨34838624491998078461839573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46451499322664104615786097 34838624491998078461839573)
                  ·
                    refine ⟨816530261531204963949365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34838624491998078461839573 816530261531204963949365)
                    ·
                      rfl

theorem cell23_4770561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_4770561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770561 prefixEnd_4770561 := by exact prefixLift 4770561
  have htrace : WordTrace (prefixWord ++ tailWord_4770561) baseStart_4770561 baseEnd_4770561 := by
    simpa [prefixWord, tailWord_4770561, baseEnd_4770561] using wordTrace_append hprefix tailTrace_4770561
  have hstable : (prefixWord ++ tailWord_4770561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770561).length < 2 ^ (prefixWord ++ tailWord_4770561).sum := by decide
  have hdescent : baseEnd_4770561 < baseStart_4770561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770575 : List Nat := [1, 1, 2, 1, 1, 1, 7, 3, 2, 1, 3]
def baseStart_4770575 : Nat := 118140960795 + 4770575 * 2 ^ 59
def prefixEnd_4770575 : Nat := 4983230072969 + 3 ^ 40 * 4770575 * 2
def baseEnd_4770575 : Nat := 2449597973322777837073031

theorem tailTrace_4770575 : CollatzResearch.WordTrace tailWord_4770575 prefixEnd_4770575 2449597973322777837073031 := by
  unfold tailWord_4770575
  simp only [CollatzResearch.WordTrace]
  refine ⟨173997164692028999189601179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115998109794685999459734119 173997164692028999189601179)
  ·
    refine ⟨260995747038043498784401769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173997164692028999189601179 260995747038043498784401769)
    ·
      refine ⟨195746810278532624088301327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260995747038043498784401769 195746810278532624088301327)
      ·
        refine ⟨293620215417798936132451991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195746810278532624088301327 293620215417798936132451991)
        ·
          refine ⟨440430323126698404198677987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293620215417798936132451991 440430323126698404198677987)
          ·
            refine ⟨660645484690047606298016981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440430323126698404198677987 660645484690047606298016981)
            ·
              refine ⟨15483878547422990772609773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 660645484690047606298016981 15483878547422990772609773)
              ·
                refine ⟨5806454455283621539728665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15483878547422990772609773 5806454455283621539728665)
                ·
                  refine ⟨4354840841462716154796499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5806454455283621539728665 4354840841462716154796499)
                  ·
                    refine ⟨6532261262194074232194749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4354840841462716154796499 6532261262194074232194749)
                    ·
                      refine ⟨2449597973322777837073031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6532261262194074232194749 2449597973322777837073031)
                      ·
                        rfl

theorem cell23_4770575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 1, 3].length) (baseStart_4770575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770575 prefixEnd_4770575 := by exact prefixLift 4770575
  have htrace : WordTrace (prefixWord ++ tailWord_4770575) baseStart_4770575 baseEnd_4770575 := by
    simpa [prefixWord, tailWord_4770575, baseEnd_4770575] using wordTrace_append hprefix tailTrace_4770575
  have hstable : (prefixWord ++ tailWord_4770575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770575).length < 2 ^ (prefixWord ++ tailWord_4770575).sum := by decide
  have hdescent : baseEnd_4770575 < baseStart_4770575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770585 : List Nat := [1, 2, 1, 2, 1, 1, 1, 8, 1, 3, 2]
def baseStart_4770585 : Nat := 118140960795 + 4770585 * 2 ^ 59
def prefixEnd_4770585 : Nat := 4983230072969 + 3 ^ 40 * 4770585 * 2
def baseEnd_4770585 : Nat := 2449603108129322797947985

theorem tailTrace_4770585 : CollatzResearch.WordTrace tailWord_4770585 prefixEnd_4770585 2449603108129322797947985 := by
  unfold tailWord_4770585
  simp only [CollatzResearch.WordTrace]
  refine ⟨173997529421992770897465209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115998352947995180598310139 173997529421992770897465209)
  ·
    refine ⟨130498147066494578173098907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173997529421992770897465209 130498147066494578173098907)
    ·
      refine ⟨195747220599741867259648361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130498147066494578173098907 195747220599741867259648361)
      ·
        refine ⟨146810415449806400444736271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195747220599741867259648361 146810415449806400444736271)
        ·
          refine ⟨220215623174709600667104407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146810415449806400444736271 220215623174709600667104407)
          ·
            refine ⟨330323434762064401000656611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220215623174709600667104407 330323434762064401000656611)
            ·
              refine ⟨495485152143096601500984917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330323434762064401000656611 495485152143096601500984917)
              ·
                refine ⟨5806466626676913298839667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 495485152143096601500984917 5806466626676913298839667)
                ·
                  refine ⟨8709699940015369948259501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5806466626676913298839667 8709699940015369948259501)
                  ·
                    refine ⟨3266137477505763730597313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8709699940015369948259501 3266137477505763730597313)
                    ·
                      refine ⟨2449603108129322797947985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3266137477505763730597313 2449603108129322797947985)
                      ·
                        rfl

theorem cell23_4770585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 3, 2].length) (baseStart_4770585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770585 prefixEnd_4770585 := by exact prefixLift 4770585
  have htrace : WordTrace (prefixWord ++ tailWord_4770585) baseStart_4770585 baseEnd_4770585 := by
    simpa [prefixWord, tailWord_4770585, baseEnd_4770585] using wordTrace_append hprefix tailTrace_4770585
  have hstable : (prefixWord ++ tailWord_4770585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770585).length < 2 ^ (prefixWord ++ tailWord_4770585).sum := by decide
  have hdescent : baseEnd_4770585 < baseStart_4770585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770632 : List Nat := [2, 1, 3, 1, 1, 3, 1, 5, 2, 2, 2]
def baseStart_4770632 : Nat := 118140960795 + 4770632 * 2 ^ 59
def prefixEnd_4770632 : Nat := 4983230072969 + 3 ^ 40 * 4770632 * 2
def baseEnd_4770632 : Nat := 2449627241720084114060269

theorem tailTrace_4770632 : CollatzResearch.WordTrace tailWord_4770632 prefixEnd_4770632 2449627241720084114060269 := by
  unfold tailWord_4770632
  simp only [CollatzResearch.WordTrace]
  refine ⟨86999621826411248962213075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115999495768548331949617433 86999621826411248962213075)
  ·
    refine ⟨130499432739616873443319613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86999621826411248962213075 130499432739616873443319613)
    ·
      refine ⟨48937287277356327541244855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130499432739616873443319613 48937287277356327541244855)
      ·
        refine ⟨73405930916034491311867283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48937287277356327541244855 73405930916034491311867283)
        ·
          refine ⟨110108896374051736967800925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73405930916034491311867283 110108896374051736967800925)
          ·
            refine ⟨41290836140269401362925347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110108896374051736967800925 41290836140269401362925347)
            ·
              refine ⟨61936254210404102044388021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41290836140269401362925347 61936254210404102044388021)
              ·
                refine ⟨5806523832225384566661377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61936254210404102044388021 5806523832225384566661377)
                ·
                  refine ⟨4354892874169038424996033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5806523832225384566661377 4354892874169038424996033)
                  ·
                    refine ⟨3266169655626778818747025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4354892874169038424996033 3266169655626778818747025)
                    ·
                      refine ⟨2449627241720084114060269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3266169655626778818747025 2449627241720084114060269)
                      ·
                        rfl

theorem cell23_4770632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_4770632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770632 prefixEnd_4770632 := by exact prefixLift 4770632
  have htrace : WordTrace (prefixWord ++ tailWord_4770632) baseStart_4770632 baseEnd_4770632 := by
    simpa [prefixWord, tailWord_4770632, baseEnd_4770632] using wordTrace_append hprefix tailTrace_4770632
  have hstable : (prefixWord ++ tailWord_4770632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770632).length < 2 ^ (prefixWord ++ tailWord_4770632).sum := by decide
  have hdescent : baseEnd_4770632 < baseStart_4770632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770655 : List Nat := [1, 1, 2, 3, 1, 3, 4, 3, 5]
def baseStart_4770655 : Nat := 118140960795 + 4770655 * 2 ^ 59
def prefixEnd_4770655 : Nat := 4983230072969 + 3 ^ 40 * 4770655 * 2
def baseEnd_4770655 : Nat := 272182116863904169341407

theorem tailTrace_4770655 : CollatzResearch.WordTrace tailWord_4770655 prefixEnd_4770655 272182116863904169341407 := by
  unfold tailWord_4770655
  simp only [CollatzResearch.WordTrace]
  refine ⟨174000082531739172852513419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116000055021159448568342279 174000082531739172852513419)
  ·
    refine ⟨261000123797608759278770129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174000082531739172852513419 261000123797608759278770129)
    ·
      refine ⟨195750092848206569459077597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261000123797608759278770129 195750092848206569459077597)
      ·
        refine ⟨73406284818077463547154099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195750092848206569459077597 73406284818077463547154099)
        ·
          refine ⟨110109427227116195320731149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73406284818077463547154099 110109427227116195320731149)
          ·
            refine ⟨41291035210168573245274181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110109427227116195320731149 41291035210168573245274181)
            ·
              refine ⟨7742069101906607483488909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41291035210168573245274181 7742069101906607483488909)
              ·
                refine ⟨2903275913214977806308341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7742069101906607483488909 2903275913214977806308341)
                ·
                  refine ⟨272182116863904169341407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2903275913214977806308341 272182116863904169341407)
                  ·
                    rfl

theorem cell23_4770655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 5].length) (baseStart_4770655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770655 prefixEnd_4770655 := by exact prefixLift 4770655
  have htrace : WordTrace (prefixWord ++ tailWord_4770655) baseStart_4770655 baseEnd_4770655 := by
    simpa [prefixWord, tailWord_4770655, baseEnd_4770655] using wordTrace_append hprefix tailTrace_4770655
  have hstable : (prefixWord ++ tailWord_4770655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770655).length < 2 ^ (prefixWord ++ tailWord_4770655).sum := by decide
  have hdescent : baseEnd_4770655 < baseStart_4770655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770668 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 4, 5]
def baseStart_4770668 : Nat := 118140960795 + 4770668 * 2 ^ 59
def prefixEnd_4770668 : Nat := 4983230072969 + 3 ^ 40 * 4770668 * 2
def baseEnd_4770668 : Nat := 816548575674548657736701

theorem tailTrace_4770668 : CollatzResearch.WordTrace tailWord_4770668 prefixEnd_4770668 816548575674548657736701 := by
  unfold tailWord_4770668
  simp only [CollatzResearch.WordTrace]
  refine ⟨87000278340346038036368329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116000371120461384048491105 87000278340346038036368329)
  ·
    refine ⟨65250208755259528527276247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87000278340346038036368329 65250208755259528527276247)
    ·
      refine ⟨97875313132889292790914371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65250208755259528527276247 97875313132889292790914371)
      ·
        refine ⟨146812969699333939186371557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97875313132889292790914371 146812969699333939186371557)
        ·
          refine ⟨27527431818625113597444667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146812969699333939186371557 27527431818625113597444667)
          ·
            refine ⟨41291147727937670396167001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27527431818625113597444667 41291147727937670396167001)
            ·
              refine ⟨30968360795953252797125251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41291147727937670396167001 30968360795953252797125251)
              ·
                refine ⟨46452541193929879195687877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30968360795953252797125251 46452541193929879195687877)
                ·
                  refine ⟨8709851473861852349191477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46452541193929879195687877 8709851473861852349191477)
                  ·
                    refine ⟨816548575674548657736701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8709851473861852349191477 816548575674548657736701)
                    ·
                      rfl

theorem cell23_4770668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_4770668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770668 prefixEnd_4770668 := by exact prefixLift 4770668
  have htrace : WordTrace (prefixWord ++ tailWord_4770668) baseStart_4770668 baseEnd_4770668 := by
    simpa [prefixWord, tailWord_4770668, baseEnd_4770668] using wordTrace_append hprefix tailTrace_4770668
  have hstable : (prefixWord ++ tailWord_4770668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770668).length < 2 ^ (prefixWord ++ tailWord_4770668).sum := by decide
  have hdescent : baseEnd_4770668 < baseStart_4770668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770688 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 4]
def baseStart_4770688 : Nat := 118140960795 + 4770688 * 2 ^ 59
def prefixEnd_4770688 : Nat := 4983230072969 + 3 ^ 40 * 4770688 * 2
def baseEnd_4770688 : Nat := 2449655996636735894960011

theorem tailTrace_4770688 : CollatzResearch.WordTrace tailWord_4770688 prefixEnd_4770688 2449655996636735894960011 := by
  unfold tailWord_4770688
  simp only [CollatzResearch.WordTrace]
  refine ⟨87000643070309809744232359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116000857427079746325643145 87000643070309809744232359)
  ·
    refine ⟨130500964605464714616348539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87000643070309809744232359 130500964605464714616348539)
    ·
      refine ⟨195751446908197071924522809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130500964605464714616348539 195751446908197071924522809)
      ·
        refine ⟨146813585181147803943392107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195751446908197071924522809 146813585181147803943392107)
        ·
          refine ⟨220220377771721705915088161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146813585181147803943392107 220220377771721705915088161)
          ·
            refine ⟨165165283328791279436316121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220220377771721705915088161 165165283328791279436316121)
            ·
              refine ⟨123873962496593459577237091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165165283328791279436316121 123873962496593459577237091)
              ·
                refine ⟨185810943744890189365855637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123873962496593459577237091 185810943744890189365855637)
                ·
                  refine ⟨8709887988041727626524483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 185810943744890189365855637 8709887988041727626524483)
                  ·
                    refine ⟨13064831982062591439786725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8709887988041727626524483 13064831982062591439786725)
                    ·
                      refine ⟨2449655996636735894960011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13064831982062591439786725 2449655996636735894960011)
                      ·
                        rfl

theorem cell23_4770688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_4770688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770688 prefixEnd_4770688 := by exact prefixLift 4770688
  have htrace : WordTrace (prefixWord ++ tailWord_4770688) baseStart_4770688 baseEnd_4770688 := by
    simpa [prefixWord, tailWord_4770688, baseEnd_4770688] using wordTrace_append hprefix tailTrace_4770688
  have hstable : (prefixWord ++ tailWord_4770688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770688).length < 2 ^ (prefixWord ++ tailWord_4770688).sum := by decide
  have hdescent : baseEnd_4770688 < baseStart_4770688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770706 : List Nat := [3, 2, 3, 2, 3, 1, 1, 3, 5]
def baseStart_4770706 : Nat := 118140960795 + 4770706 * 2 ^ 59
def prefixEnd_4770706 : Nat := 4983230072969 + 3 ^ 40 * 4770706 * 2
def baseEnd_4770706 : Nat := 272185026587612980503881

theorem tailTrace_4770706 : CollatzResearch.WordTrace tailWord_4770706 prefixEnd_4770706 272185026587612980503881 := by
  unfold tailWord_4770706
  simp only [CollatzResearch.WordTrace]
  refine ⟨43500485663638602140654993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116001295103036272375079981 43500485663638602140654993)
  ·
    refine ⟨32625364247728951605491245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43500485663638602140654993 32625364247728951605491245)
    ·
      refine ⟨12234511592898356852059217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32625364247728951605491245 12234511592898356852059217)
      ·
        refine ⟨9175883694673767639044413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12234511592898356852059217 9175883694673767639044413)
        ·
          refine ⟨3440956385502662864641655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9175883694673767639044413 3440956385502662864641655)
          ·
            refine ⟨5161434578253994296962483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3440956385502662864641655 5161434578253994296962483)
            ·
              refine ⟨7742151867380991445443725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5161434578253994296962483 7742151867380991445443725)
              ·
                refine ⟨2903306950267871792041397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7742151867380991445443725 2903306950267871792041397)
                ·
                  refine ⟨272185026587612980503881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2903306950267871792041397 272185026587612980503881)
                  ·
                    rfl

theorem cell23_4770706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_4770706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770706 prefixEnd_4770706 := by exact prefixLift 4770706
  have htrace : WordTrace (prefixWord ++ tailWord_4770706) baseStart_4770706 baseEnd_4770706 := by
    simpa [prefixWord, tailWord_4770706, baseEnd_4770706] using wordTrace_append hprefix tailTrace_4770706
  have hstable : (prefixWord ++ tailWord_4770706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770706).length < 2 ^ (prefixWord ++ tailWord_4770706).sum := by decide
  have hdescent : baseEnd_4770706 < baseStart_4770706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770722 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_4770722 : Nat := 118140960795 + 4770722 * 2 ^ 59
def prefixEnd_4770722 : Nat := 4983230072969 + 3 ^ 40 * 4770722 * 2
def baseEnd_4770722 : Nat := 2449673454978988761934855

theorem tailTrace_4770722 : CollatzResearch.WordTrace tailWord_4770722 prefixEnd_4770722 2449673454978988761934855 := by
  unfold tailWord_4770722
  simp only [CollatzResearch.WordTrace]
  refine ⟨43500631555624110823800605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116001684148330962196801613 43500631555624110823800605)
  ·
    refine ⟨16312736833359041558925227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43500631555624110823800605 16312736833359041558925227)
    ·
      refine ⟨24469105250038562338387841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16312736833359041558925227 24469105250038562338387841)
      ·
        refine ⟨18351828937528921753790881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24469105250038562338387841 18351828937528921753790881)
        ·
          refine ⟨13763871703146691315343161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18351828937528921753790881 13763871703146691315343161)
          ·
            refine ⟨10322903777360018486507371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13763871703146691315343161 10322903777360018486507371)
            ·
              refine ⟨15484355666040027729761057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10322903777360018486507371 15484355666040027729761057)
              ·
                refine ⟨11613266749530020797320793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15484355666040027729761057 11613266749530020797320793)
                ·
                  refine ⟨8709950062147515597990595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11613266749530020797320793 8709950062147515597990595)
                  ·
                    refine ⟨13064925093221273396985893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8709950062147515597990595 13064925093221273396985893)
                    ·
                      refine ⟨2449673454978988761934855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13064925093221273396985893 2449673454978988761934855)
                      ·
                        rfl

theorem cell23_4770722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_4770722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770722 prefixEnd_4770722 := by exact prefixLift 4770722
  have htrace : WordTrace (prefixWord ++ tailWord_4770722) baseStart_4770722 baseEnd_4770722 := by
    simpa [prefixWord, tailWord_4770722, baseEnd_4770722] using wordTrace_append hprefix tailTrace_4770722
  have hstable : (prefixWord ++ tailWord_4770722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770722).length < 2 ^ (prefixWord ++ tailWord_4770722).sum := by decide
  have hdescent : baseEnd_4770722 < baseStart_4770722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770745 : List Nat := [1, 2, 1, 4, 2, 3, 1, 3, 6]
def baseStart_4770745 : Nat := 118140960795 + 4770745 * 2 ^ 59
def prefixEnd_4770745 : Nat := 4983230072969 + 3 ^ 40 * 4770745 * 2
def baseEnd_4770745 : Nat := 272187251670449130216361

theorem tailTrace_4770745 : CollatzResearch.WordTrace tailWord_4770745 prefixEnd_4770745 272187251670449130216361 := by
  unfold tailWord_4770745
  simp only [CollatzResearch.WordTrace]
  refine ⟨174003365101413118223289689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116002243400942078815526459 174003365101413118223289689)
  ·
    refine ⟨130502523826059838667467267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174003365101413118223289689 130502523826059838667467267)
    ·
      refine ⟨195753785739089758001200901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130502523826059838667467267 195753785739089758001200901)
      ·
        refine ⟨36703834826079329625225169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195753785739089758001200901 36703834826079329625225169)
        ·
          refine ⟨27527876119559497218918877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36703834826079329625225169 27527876119559497218918877)
          ·
            refine ⟨10322953544834811457094579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27527876119559497218918877 10322953544834811457094579)
            ·
              refine ⟨15484430317252217185641869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10322953544834811457094579 15484430317252217185641869)
              ·
                refine ⟨5806661368969581444615701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15484430317252217185641869 5806661368969581444615701)
                ·
                  refine ⟨272187251670449130216361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5806661368969581444615701 272187251670449130216361)
                  ·
                    rfl

theorem cell23_4770745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 6].length) (baseStart_4770745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770745 prefixEnd_4770745 := by exact prefixLift 4770745
  have htrace : WordTrace (prefixWord ++ tailWord_4770745) baseStart_4770745 baseEnd_4770745 := by
    simpa [prefixWord, tailWord_4770745, baseEnd_4770745] using wordTrace_append hprefix tailTrace_4770745
  have hstable : (prefixWord ++ tailWord_4770745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770745).length < 2 ^ (prefixWord ++ tailWord_4770745).sum := by decide
  have hdescent : baseEnd_4770745 < baseStart_4770745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770783 : List Nat := [1, 1, 2, 3, 6, 1, 2, 2, 1, 4]
def baseStart_4770783 : Nat := 118140960795 + 4770783 * 2 ^ 59
def prefixEnd_4770783 : Nat := 4983230072969 + 3 ^ 40 * 4770783 * 2
def baseEnd_4770783 : Nat := 816568259099637674424025

theorem tailTrace_4770783 : CollatzResearch.WordTrace tailWord_4770783 prefixEnd_4770783 816568259099637674424025 := by
  unfold tailWord_4770783
  simp only [CollatzResearch.WordTrace]
  refine ⟨174004751075275450713173003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116003167383516967142115335 174004751075275450713173003)
  ·
    refine ⟨261007126612913176069759505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174004751075275450713173003 261007126612913176069759505)
    ·
      refine ⟨195755344959684882052319629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261007126612913176069759505 195755344959684882052319629)
      ·
        refine ⟨73408254359881830769619861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195755344959684882052319629 73408254359881830769619861)
        ·
          refine ⟨3441011923119460817325931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73408254359881830769619861 3441011923119460817325931)
          ·
            refine ⟨5161517884679191225988897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441011923119460817325931 5161517884679191225988897)
            ·
              refine ⟨3871138413509393419491673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5161517884679191225988897 3871138413509393419491673)
              ·
                refine ⟨2903353810132045064618755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3871138413509393419491673 2903353810132045064618755)
                ·
                  refine ⟨4355030715198067596928133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2903353810132045064618755 4355030715198067596928133)
                  ·
                    refine ⟨816568259099637674424025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4355030715198067596928133 816568259099637674424025)
                    ·
                      rfl

theorem cell23_4770783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 1, 4].length) (baseStart_4770783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770783 prefixEnd_4770783 := by exact prefixLift 4770783
  have htrace : WordTrace (prefixWord ++ tailWord_4770783) baseStart_4770783 baseEnd_4770783 := by
    simpa [prefixWord, tailWord_4770783, baseEnd_4770783] using wordTrace_append hprefix tailTrace_4770783
  have hstable : (prefixWord ++ tailWord_4770783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770783).length < 2 ^ (prefixWord ++ tailWord_4770783).sum := by decide
  have hdescent : baseEnd_4770783 < baseStart_4770783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770795 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 4, 6, 2]
def baseStart_4770795 : Nat := 118140960795 + 4770795 * 2 ^ 59
def prefixEnd_4770795 : Nat := 4983230072969 + 3 ^ 40 * 4770795 * 2
def baseEnd_4770795 : Nat := 2449710939066766976322019

theorem tailTrace_4770795 : CollatzResearch.WordTrace tailWord_4770795 prefixEnd_4770795 2449710939066766976322019 := by
  unfold tailWord_4770795
  simp only [CollatzResearch.WordTrace]
  refine ⟨174005188751231976762609839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116003459167487984508406559 174005188751231976762609839)
  ·
    refine ⟨261007783126847965143914759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174005188751231976762609839 261007783126847965143914759)
    ·
      refine ⟨391511674690271947715872139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261007783126847965143914759 391511674690271947715872139)
      ·
        refine ⟨587267512035407921573808209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391511674690271947715872139 587267512035407921573808209)
        ·
          refine ⟨440450634026555941180356157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587267512035407921573808209 440450634026555941180356157)
          ·
            refine ⟨165168987759958477942633559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 440450634026555941180356157 165168987759958477942633559)
            ·
              refine ⟨247753481639937716913950339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165168987759958477942633559 247753481639937716913950339)
              ·
                refine ⟨371630222459906575370925509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247753481639937716913950339 371630222459906575370925509)
                ·
                  refine ⟨69680666711232482882048533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 371630222459906575370925509 69680666711232482882048533)
                  ·
                    refine ⟨3266281252089022635096025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69680666711232482882048533 3266281252089022635096025)
                    ·
                      refine ⟨2449710939066766976322019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3266281252089022635096025 2449710939066766976322019)
                      ·
                        rfl

theorem cell23_4770795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 6, 2].length) (baseStart_4770795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770795 prefixEnd_4770795 := by exact prefixLift 4770795
  have htrace : WordTrace (prefixWord ++ tailWord_4770795) baseStart_4770795 baseEnd_4770795 := by
    simpa [prefixWord, tailWord_4770795, baseEnd_4770795] using wordTrace_append hprefix tailTrace_4770795
  have hstable : (prefixWord ++ tailWord_4770795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770795).length < 2 ^ (prefixWord ++ tailWord_4770795).sum := by decide
  have hdescent : baseEnd_4770795 < baseStart_4770795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770839 : List Nat := [1, 1, 3, 5, 1, 1, 3, 2, 2, 4]
def baseStart_4770839 : Nat := 118140960795 + 4770839 * 2 ^ 59
def prefixEnd_4770839 : Nat := 4983230072969 + 3 ^ 40 * 4770839 * 2
def baseEnd_4770839 : Nat := 816577844071854934723939

theorem tailTrace_4770839 : CollatzResearch.WordTrace tailWord_4770839 prefixEnd_4770839 816577844071854934723939 := by
  unfold tailWord_4770839
  simp only [CollatzResearch.WordTrace]
  refine ⟨174006793563072572277211571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116004529042048381518141047 174006793563072572277211571)
  ·
    refine ⟨261010190344608858415817357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174006793563072572277211571 261010190344608858415817357)
    ·
      refine ⟨97878821379228321905931509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261010190344608858415817357 97878821379228321905931509)
      ·
        refine ⟨9176139504302655178681079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97878821379228321905931509 9176139504302655178681079)
        ·
          refine ⟨13764209256453982768021619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9176139504302655178681079 13764209256453982768021619)
          ·
            refine ⟨20646313884680974152032429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13764209256453982768021619 20646313884680974152032429)
            ·
              refine ⟨7742367706755365307012161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20646313884680974152032429 7742367706755365307012161)
              ·
                refine ⟨5806775780066523980259121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7742367706755365307012161 5806775780066523980259121)
                ·
                  refine ⟨4355081835049892985194341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5806775780066523980259121 4355081835049892985194341)
                  ·
                    refine ⟨816577844071854934723939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4355081835049892985194341 816577844071854934723939)
                    ·
                      rfl

theorem cell23_4770839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_4770839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770839 prefixEnd_4770839 := by exact prefixLift 4770839
  have htrace : WordTrace (prefixWord ++ tailWord_4770839) baseStart_4770839 baseEnd_4770839 := by
    simpa [prefixWord, tailWord_4770839, baseEnd_4770839] using wordTrace_append hprefix tailTrace_4770839
  have hstable : (prefixWord ++ tailWord_4770839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770839).length < 2 ^ (prefixWord ++ tailWord_4770839).sum := by decide
  have hdescent : baseEnd_4770839 < baseStart_4770839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770915 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 4]
def baseStart_4770915 : Nat := 118140960795 + 4770915 * 2 ^ 59
def prefixEnd_4770915 : Nat := 4983230072969 + 3 ^ 40 * 4770915 * 2
def baseEnd_4770915 : Nat := 2449772556745306506821467

theorem tailTrace_4770915 : CollatzResearch.WordTrace tailWord_4770915 prefixEnd_4770915 2449772556745306506821467 := by
  unfold tailWord_4770915
  simp only [CollatzResearch.WordTrace]
  refine ⟨174009565510797237256978199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116006377007198158171318799 174009565510797237256978199)
  ·
    refine ⟨261014348266195855885467299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174009565510797237256978199 261014348266195855885467299)
    ·
      refine ⟨391521522399293783828200949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261014348266195855885467299 391521522399293783828200949)
      ·
        refine ⟨36705142724933792233893839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 391521522399293783828200949 36705142724933792233893839)
        ·
          refine ⟨55057714087400688350840759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36705142724933792233893839 55057714087400688350840759)
          ·
            refine ⟨82586571131101032526261139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55057714087400688350840759 82586571131101032526261139)
            ·
              refine ⟨123879856696651548789391709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82586571131101032526261139 123879856696651548789391709)
              ·
                refine ⟨46454946261244330796021891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123879856696651548789391709 46454946261244330796021891)
                ·
                  refine ⟨69682419391866496194032837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46454946261244330796021891 69682419391866496194032837)
                  ·
                    refine ⟨13065453635974968036381157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69682419391866496194032837 13065453635974968036381157)
                    ·
                      refine ⟨2449772556745306506821467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13065453635974968036381157 2449772556745306506821467)
                      ·
                        rfl

theorem cell23_4770915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_4770915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770915 prefixEnd_4770915 := by exact prefixLift 4770915
  have htrace : WordTrace (prefixWord ++ tailWord_4770915) baseStart_4770915 baseEnd_4770915 := by
    simpa [prefixWord, tailWord_4770915, baseEnd_4770915] using wordTrace_append hprefix tailTrace_4770915
  have hstable : (prefixWord ++ tailWord_4770915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770915).length < 2 ^ (prefixWord ++ tailWord_4770915).sum := by decide
  have hdescent : baseEnd_4770915 < baseStart_4770915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770922 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_4770922 : Nat := 118140960795 + 4770922 * 2 ^ 59
def prefixEnd_4770922 : Nat := 4983230072969 + 3 ^ 40 * 4770922 * 2
def baseEnd_4770922 : Nat := 2449776151109887979433935

theorem tailTrace_4770922 : CollatzResearch.WordTrace tailWord_4770922 prefixEnd_4770922 2449776151109887979433935 := by
  unfold tailWord_4770922
  simp only [CollatzResearch.WordTrace]
  refine ⟨43502455205442969363120755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116006547214514584968322013 43502455205442969363120755)
  ·
    refine ⟨65253682808164454044681133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43502455205442969363120755 65253682808164454044681133)
    ·
      refine ⟨24470131053061670266755425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65253682808164454044681133 24470131053061670266755425)
      ·
        refine ⟨18352598289796252700066569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24470131053061670266755425 18352598289796252700066569)
        ·
          refine ⟨13764448717347189525049927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18352598289796252700066569 13764448717347189525049927)
          ·
            refine ⟨20646673076020784287574891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13764448717347189525049927 20646673076020784287574891)
            ·
              refine ⟨30970009614031176431362337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20646673076020784287574891 30970009614031176431362337)
              ·
                refine ⟨23227507210523382323521753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30970009614031176431362337 23227507210523382323521753)
                ·
                  refine ⟨17420630407892536742641315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23227507210523382323521753 17420630407892536742641315)
                  ·
                    refine ⟨26130945611838805113961973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17420630407892536742641315 26130945611838805113961973)
                    ·
                      refine ⟨2449776151109887979433935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26130945611838805113961973 2449776151109887979433935)
                      ·
                        rfl

theorem cell23_4770922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_4770922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770922 prefixEnd_4770922 := by exact prefixLift 4770922
  have htrace : WordTrace (prefixWord ++ tailWord_4770922) baseStart_4770922 baseEnd_4770922 := by
    simpa [prefixWord, tailWord_4770922, baseEnd_4770922] using wordTrace_append hprefix tailTrace_4770922
  have hstable : (prefixWord ++ tailWord_4770922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770922).length < 2 ^ (prefixWord ++ tailWord_4770922).sum := by decide
  have hdescent : baseEnd_4770922 < baseStart_4770922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770965 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_4770965 : Nat := 118140960795 + 4770965 * 2 ^ 59
def prefixEnd_4770965 : Nat := 4983230072969 + 3 ^ 40 * 4770965 * 2
def baseEnd_4770965 : Nat := 2449798230778031311196237

theorem tailTrace_4770965 : CollatzResearch.WordTrace tailWord_4770965 prefixEnd_4770965 2449798230778031311196237 := by
  unfold tailWord_4770965
  simp only [CollatzResearch.WordTrace]
  refine ⟨174011389160616095796298349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116007592773744063864198899 174011389160616095796298349)
  ·
    refine ⟨65254270935231035923611881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174011389160616095796298349 65254270935231035923611881)
    ·
      refine ⟨48940703201423276942708911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65254270935231035923611881 48940703201423276942708911)
      ·
        refine ⟨73411054802134915414063367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48940703201423276942708911 73411054802134915414063367)
        ·
          refine ⟨110116582203202373121095051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73411054802134915414063367 110116582203202373121095051)
          ·
            refine ⟨165174873304803559681642577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110116582203202373121095051 165174873304803559681642577)
            ·
              refine ⟨123881154978602669761231933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165174873304803559681642577 123881154978602669761231933)
              ·
                refine ⟨46455433116976001160461975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123881154978602669761231933 46455433116976001160461975)
                ·
                  refine ⟨69683149675464001740692963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46455433116976001160461975 69683149675464001740692963)
                  ·
                    refine ⟨104524724513196002611039445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69683149675464001740692963 104524724513196002611039445)
                    ·
                      refine ⟨2449798230778031311196237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104524724513196002611039445 2449798230778031311196237)
                      ·
                        rfl

theorem cell23_4770965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_4770965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770965 prefixEnd_4770965 := by exact prefixLift 4770965
  have htrace : WordTrace (prefixWord ++ tailWord_4770965) baseStart_4770965 baseEnd_4770965 := by
    simpa [prefixWord, tailWord_4770965, baseEnd_4770965] using wordTrace_append hprefix tailTrace_4770965
  have hstable : (prefixWord ++ tailWord_4770965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770965).length < 2 ^ (prefixWord ++ tailWord_4770965).sum := by decide
  have hdescent : baseEnd_4770965 < baseStart_4770965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4770989 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_4770989 : Nat := 118140960795 + 4770989 * 2 ^ 59
def prefixEnd_4770989 : Nat := 4983230072969 + 3 ^ 40 * 4770989 * 2
def baseEnd_4770989 : Nat := 816603518104579739098709

theorem tailTrace_4770989 : CollatzResearch.WordTrace tailWord_4770989 prefixEnd_4770989 816603518104579739098709 := by
  unfold tailWord_4770989
  simp only [CollatzResearch.WordTrace]
  refine ⟨174012264512529147895172021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116008176341686098596781347 174012264512529147895172021)
  ·
    refine ⟨16313649798049607615172377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174012264512529147895172021 16313649798049607615172377)
    ·
      refine ⟨12235237348537205711379283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16313649798049607615172377 12235237348537205711379283)
      ·
        refine ⟨18352856022805808567068925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12235237348537205711379283 18352856022805808567068925)
        ·
          refine ⟨6882321008552178212650847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18352856022805808567068925 6882321008552178212650847)
          ·
            refine ⟨10323481512828267318976271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6882321008552178212650847 10323481512828267318976271)
            ·
              refine ⟨15485222269242400978464407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10323481512828267318976271 15485222269242400978464407)
              ·
                refine ⟨23227833403863601467696611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15485222269242400978464407 23227833403863601467696611)
                ·
                  refine ⟨34841750105795402201544917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23227833403863601467696611 34841750105795402201544917)
                  ·
                    refine ⟨816603518104579739098709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34841750105795402201544917 816603518104579739098709)
                    ·
                      rfl

theorem cell23_4770989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_4770989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4770989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4770989 prefixEnd_4770989 := by exact prefixLift 4770989
  have htrace : WordTrace (prefixWord ++ tailWord_4770989) baseStart_4770989 baseEnd_4770989 := by
    simpa [prefixWord, tailWord_4770989, baseEnd_4770989] using wordTrace_append hprefix tailTrace_4770989
  have hstable : (prefixWord ++ tailWord_4770989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4770989).length < 2 ^ (prefixWord ++ tailWord_4770989).sum := by decide
  have hdescent : baseEnd_4770989 < baseStart_4770989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4770989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771002 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 7, 4]
def baseStart_4771002 : Nat := 118140960795 + 4771002 * 2 ^ 59
def prefixEnd_4771002 : Nat := 4983230072969 + 3 ^ 40 * 4771002 * 2
def baseEnd_4771002 : Nat := 816605743187415888811189

theorem tailTrace_4771002 : CollatzResearch.WordTrace tailWord_4771002 prefixEnd_4771002 816605743187415888811189 := by
  unfold tailWord_4771002
  simp only [CollatzResearch.WordTrace]
  refine ⟨43503184665370512778848815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116008492440988034076930173 43503184665370512778848815)
  ·
    refine ⟨65254776998055769168273223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43503184665370512778848815 65254776998055769168273223)
    ·
      refine ⟨97882165497083653752409835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65254776998055769168273223 97882165497083653752409835)
      ·
        refine ⟨146823248245625480628614753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97882165497083653752409835 146823248245625480628614753)
        ·
          refine ⟨110117436184219110471461065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146823248245625480628614753 110117436184219110471461065)
          ·
            refine ⟨82588077138164332853595799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110117436184219110471461065 82588077138164332853595799)
            ·
              refine ⟨123882115707246499280393699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82588077138164332853595799 123882115707246499280393699)
              ·
                refine ⟨185823173560869748920590549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123882115707246499280393699 185823173560869748920590549)
                ·
                  refine ⟨4355230630332884740326341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 185823173560869748920590549 4355230630332884740326341)
                  ·
                    refine ⟨816605743187415888811189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4355230630332884740326341 816605743187415888811189)
                    ·
                      rfl

theorem cell23_4771002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_4771002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771002 prefixEnd_4771002 := by exact prefixLift 4771002
  have htrace : WordTrace (prefixWord ++ tailWord_4771002) baseStart_4771002 baseEnd_4771002 := by
    simpa [prefixWord, tailWord_4771002, baseEnd_4771002] using wordTrace_append hprefix tailTrace_4771002
  have hstable : (prefixWord ++ tailWord_4771002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771002).length < 2 ^ (prefixWord ++ tailWord_4771002).sum := by decide
  have hdescent : baseEnd_4771002 < baseStart_4771002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771029 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4771029 : Nat := 118140960795 + 4771029 * 2 ^ 59
def prefixEnd_4771029 : Nat := 4983230072969 + 3 ^ 40 * 4771029 * 2
def baseEnd_4771029 : Nat := 2449831093539919060795943

theorem tailTrace_4771029 : CollatzResearch.WordTrace tailWord_4771029 prefixEnd_4771029 2449831093539919060795943 := by
  unfold tailWord_4771029
  simp only [CollatzResearch.WordTrace]
  refine ⟨174013723432384234726628141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116009148954922823151085427 174013723432384234726628141)
  ·
    refine ⟨65255146287144088022485553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174013723432384234726628141 65255146287144088022485553)
    ·
      refine ⟨48941359715358066016864165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65255146287144088022485553 48941359715358066016864165)
      ·
        refine ⟨9176504946629637378162031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48941359715358066016864165 9176504946629637378162031)
        ·
          refine ⟨13764757419944456067243047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9176504946629637378162031 13764757419944456067243047)
          ·
            refine ⟨20647136129916684100864571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13764757419944456067243047 20647136129916684100864571)
            ·
              refine ⟨30970704194875026151296857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20647136129916684100864571 30970704194875026151296857)
              ·
                refine ⟨23228028146156269613472643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30970704194875026151296857 23228028146156269613472643)
                ·
                  refine ⟨34842042219234404420208965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23228028146156269613472643 34842042219234404420208965)
                  ·
                    refine ⟨6532882916106450828789181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34842042219234404420208965 6532882916106450828789181)
                    ·
                      refine ⟨2449831093539919060795943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6532882916106450828789181 2449831093539919060795943)
                      ·
                        rfl

theorem cell23_4771029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4771029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771029 prefixEnd_4771029 := by exact prefixLift 4771029
  have htrace : WordTrace (prefixWord ++ tailWord_4771029) baseStart_4771029 baseEnd_4771029 := by
    simpa [prefixWord, tailWord_4771029, baseEnd_4771029] using wordTrace_append hprefix tailTrace_4771029
  have hstable : (prefixWord ++ tailWord_4771029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771029).length < 2 ^ (prefixWord ++ tailWord_4771029).sum := by decide
  have hdescent : baseEnd_4771029 < baseStart_4771029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771035 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 8]
def baseStart_4771035 : Nat := 118140960795 + 4771035 * 2 ^ 59
def prefixEnd_4771035 : Nat := 4983230072969 + 3 ^ 40 * 4771035 * 2
def baseEnd_4771035 : Nat := 2449834174423846037320915

theorem tailTrace_4771035 : CollatzResearch.WordTrace tailWord_4771035 prefixEnd_4771035 2449834174423846037320915 := by
  unfold tailWord_4771035
  simp only [CollatzResearch.WordTrace]
  refine ⟨174013942270362497751346559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116009294846908331834231039 174013942270362497751346559)
  ·
    refine ⟨261020913405543746627019839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174013942270362497751346559 261020913405543746627019839)
    ·
      refine ⟨391531370108315619940529759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261020913405543746627019839 391531370108315619940529759)
      ·
        refine ⟨587297055162473429910794639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391531370108315619940529759 587297055162473429910794639)
        ·
          refine ⟨880945582743710144866191959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587297055162473429910794639 880945582743710144866191959)
          ·
            refine ⟨1321418374115565217299287939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880945582743710144866191959 1321418374115565217299287939)
            ·
              refine ⟨1982127561173347825948931909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321418374115565217299287939 1982127561173347825948931909)
              ·
                refine ⟨371648917720002717365424733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1982127561173347825948931909 371648917720002717365424733)
                ·
                  refine ⟨139368344145001019012034275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371648917720002717365424733 139368344145001019012034275)
                  ·
                    refine ⟨209052516217501528518051413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139368344145001019012034275 209052516217501528518051413)
                    ·
                      refine ⟨2449834174423846037320915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 209052516217501528518051413 2449834174423846037320915)
                      ·
                        rfl

theorem cell23_4771035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_4771035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771035 prefixEnd_4771035 := by exact prefixLift 4771035
  have htrace : WordTrace (prefixWord ++ tailWord_4771035) baseStart_4771035 baseEnd_4771035 := by
    simpa [prefixWord, tailWord_4771035, baseEnd_4771035] using wordTrace_append hprefix tailTrace_4771035
  have hstable : (prefixWord ++ tailWord_4771035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771035).length < 2 ^ (prefixWord ++ tailWord_4771035).sum := by decide
  have hdescent : baseEnd_4771035 < baseStart_4771035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771053 : List Nat := [1, 5, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_4771053 : Nat := 118140960795 + 4771053 * 2 ^ 59
def prefixEnd_4771053 : Nat := 4983230072969 + 3 ^ 40 * 4771053 * 2
def baseEnd_4771053 : Nat := 816614472358542322298611

theorem tailTrace_4771053 : CollatzResearch.WordTrace tailWord_4771053 prefixEnd_4771053 816614472358542322298611 := by
  unfold tailWord_4771053
  simp only [CollatzResearch.WordTrace]
  refine ⟨174014598784297286825501813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116009732522864857883667875 174014598784297286825501813)
  ·
    refine ⟨16313868636027870639890795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174014598784297286825501813 16313868636027870639890795)
    ·
      refine ⟨24470802954041805959836193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16313868636027870639890795 24470802954041805959836193)
      ·
        refine ⟨18353102215531354469877145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24470802954041805959836193 18353102215531354469877145)
        ·
          refine ⟨13764826661648515852407859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18353102215531354469877145 13764826661648515852407859)
          ·
            refine ⟨20647239992472773778611789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13764826661648515852407859 20647239992472773778611789)
            ·
              refine ⟨7742714997177290166979421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20647239992472773778611789 7742714997177290166979421)
              ·
                refine ⟨2903518123941483812617283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7742714997177290166979421 2903518123941483812617283)
                ·
                  refine ⟨4355277185912225718925925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2903518123941483812617283 4355277185912225718925925)
                  ·
                    refine ⟨816614472358542322298611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4355277185912225718925925 816614472358542322298611)
                    ·
                      rfl

theorem cell23_4771053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_4771053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771053 prefixEnd_4771053 := by exact prefixLift 4771053
  have htrace : WordTrace (prefixWord ++ tailWord_4771053) baseStart_4771053 baseEnd_4771053 := by
    simpa [prefixWord, tailWord_4771053, baseEnd_4771053] using wordTrace_append hprefix tailTrace_4771053
  have hstable : (prefixWord ++ tailWord_4771053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771053).length < 2 ^ (prefixWord ++ tailWord_4771053).sum := by decide
  have hdescent : baseEnd_4771053 < baseStart_4771053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771060 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4771060 : Nat := 118140960795 + 4771060 * 2 ^ 59
def prefixEnd_4771060 : Nat := 4983230072969 + 3 ^ 40 * 4771060 * 2
def baseEnd_4771060 : Nat := 2449847011440208439508301

theorem tailTrace_4771060 : CollatzResearch.WordTrace tailWord_4771060 prefixEnd_4771060 2449847011440208439508301 := by
  unfold tailWord_4771060
  simp only [CollatzResearch.WordTrace]
  refine ⟨87007427047635963510503317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116009902730181284680671089 87007427047635963510503317)
  ·
    refine ⟨4078473142857935789554843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87007427047635963510503317 4078473142857935789554843)
    ·
      refine ⟨6117709714286903684332265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4078473142857935789554843 6117709714286903684332265)
      ·
        refine ⟨4588282285715177763249199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6117709714286903684332265 4588282285715177763249199)
        ·
          refine ⟨6882423428572766644873799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4588282285715177763249199 6882423428572766644873799)
          ·
            refine ⟨10323635142859149967310699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6882423428572766644873799 10323635142859149967310699)
            ·
              refine ⟨15485452714288724950966049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10323635142859149967310699 15485452714288724950966049)
              ·
                refine ⟨11614089535716543713224537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15485452714288724950966049 11614089535716543713224537)
                ·
                  refine ⟨8710567151787407784918403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11614089535716543713224537 8710567151787407784918403)
                  ·
                    refine ⟨13065850727681111677377605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8710567151787407784918403 13065850727681111677377605)
                    ·
                      refine ⟨2449847011440208439508301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13065850727681111677377605 2449847011440208439508301)
                      ·
                        rfl

theorem cell23_4771060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4771060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771060 prefixEnd_4771060 := by exact prefixLift 4771060
  have htrace : WordTrace (prefixWord ++ tailWord_4771060) baseStart_4771060 baseEnd_4771060 := by
    simpa [prefixWord, tailWord_4771060, baseEnd_4771060] using wordTrace_append hprefix tailTrace_4771060
  have hstable : (prefixWord ++ tailWord_4771060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771060).length < 2 ^ (prefixWord ++ tailWord_4771060).sum := by decide
  have hdescent : baseEnd_4771060 < baseStart_4771060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771070 : List Nat := [4, 2, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_4771070 : Nat := 118140960795 + 4771070 * 2 ^ 59
def prefixEnd_4771070 : Nat := 4983230072969 + 3 ^ 40 * 4771070 * 2
def baseEnd_4771070 : Nat := 816617382082251133461085

theorem tailTrace_4771070 : CollatzResearch.WordTrace tailWord_4771070 prefixEnd_4771070 816617382082251133461085 := by
  unfold tailWord_4771070
  simp only [CollatzResearch.WordTrace]
  refine ⟨21751902353154462341108833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116010145883490465819247109 21751902353154462341108833)
  ·
    refine ⟨16313926764865846755831625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21751902353154462341108833 16313926764865846755831625)
    ·
      refine ⟨12235445073649385066873719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16313926764865846755831625 12235445073649385066873719)
      ·
        refine ⟨18353167610474077600310579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12235445073649385066873719 18353167610474077600310579)
        ·
          refine ⟨27529751415711116400465869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18353167610474077600310579 27529751415711116400465869)
          ·
            refine ⟨10323656780891668650174701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27529751415711116400465869 10323656780891668650174701)
            ·
              refine ⟨3871371292834375743815513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10323656780891668650174701 3871371292834375743815513)
              ·
                refine ⟨2903528469625781807861635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3871371292834375743815513 2903528469625781807861635)
                ·
                  refine ⟨4355292704438672711792453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2903528469625781807861635 4355292704438672711792453)
                  ·
                    refine ⟨816617382082251133461085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4355292704438672711792453 816617382082251133461085)
                    ·
                      rfl

theorem cell23_4771070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_4771070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771070 prefixEnd_4771070 := by exact prefixLift 4771070
  have htrace : WordTrace (prefixWord ++ tailWord_4771070) baseStart_4771070 baseEnd_4771070 := by
    simpa [prefixWord, tailWord_4771070, baseEnd_4771070] using wordTrace_append hprefix tailTrace_4771070
  have hstable : (prefixWord ++ tailWord_4771070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771070).length < 2 ^ (prefixWord ++ tailWord_4771070).sum := by decide
  have hdescent : baseEnd_4771070 < baseStart_4771070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771082 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_4771082 : Nat := 118140960795 + 4771082 * 2 ^ 59
def prefixEnd_4771082 : Nat := 4983230072969 + 3 ^ 40 * 4771082 * 2
def baseEnd_4771082 : Nat := 2449858308014607353433199

theorem tailTrace_4771082 : CollatzResearch.WordTrace tailWord_4771082 prefixEnd_4771082 2449858308014607353433199 := by
  unfold tailWord_4771082
  simp only [CollatzResearch.WordTrace]
  refine ⟨43503914125298056194576875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116010437667461483185538333 43503914125298056194576875)
  ·
    refine ⟨65255871187947084291865313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43503914125298056194576875 65255871187947084291865313)
    ·
      refine ⟨48941903390960313218898985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65255871187947084291865313 48941903390960313218898985)
      ·
        refine ⟨36706427543220234914174239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48941903390960313218898985 36706427543220234914174239)
        ·
          refine ⟨55059641314830352371261359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36706427543220234914174239 55059641314830352371261359)
          ·
            refine ⟨82589461972245528556892039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55059641314830352371261359 82589461972245528556892039)
            ·
              refine ⟨123884192958368292835338059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82589461972245528556892039 123884192958368292835338059)
              ·
                refine ⟨185826289437552439253007089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123884192958368292835338059 185826289437552439253007089)
                ·
                  refine ⟨139369717078164329439755317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185826289437552439253007089 139369717078164329439755317)
                  ·
                    refine ⟨13065910976077905884977061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 139369717078164329439755317 13065910976077905884977061)
                    ·
                      refine ⟨2449858308014607353433199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13065910976077905884977061 2449858308014607353433199)
                      ·
                        rfl

theorem cell23_4771082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_4771082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771082 prefixEnd_4771082 := by exact prefixLift 4771082
  have htrace : WordTrace (prefixWord ++ tailWord_4771082) baseStart_4771082 baseEnd_4771082 := by
    simpa [prefixWord, tailWord_4771082, baseEnd_4771082] using wordTrace_append hprefix tailTrace_4771082
  have hstable : (prefixWord ++ tailWord_4771082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771082).length < 2 ^ (prefixWord ++ tailWord_4771082).sum := by decide
  have hdescent : baseEnd_4771082 < baseStart_4771082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771096 : List Nat := [2, 1, 2, 3, 1, 5, 1, 2, 1, 5]
def baseStart_4771096 : Nat := 118140960795 + 4771096 * 2 ^ 59
def prefixEnd_4771096 : Nat := 4983230072969 + 3 ^ 40 * 4771096 * 2
def baseEnd_4771096 : Nat := 816621832247923432886045

theorem tailTrace_4771096 : CollatzResearch.WordTrace tailWord_4771096 prefixEnd_4771096 816621832247923432886045 := by
  unfold tailWord_4771096
  simp only [CollatzResearch.WordTrace]
  refine ⟨87008083561570752584658571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116010778082094336779544761 87008083561570752584658571)
  ·
    refine ⟨130512125342356128876987857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87008083561570752584658571 130512125342356128876987857)
    ·
      refine ⟨97884094006767096657740893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130512125342356128876987857 97884094006767096657740893)
      ·
        refine ⟨36706535252537661246652835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97884094006767096657740893 36706535252537661246652835)
        ·
          refine ⟨55059802878806491869979253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36706535252537661246652835 55059802878806491869979253)
          ·
            refine ⟨5161856519888108612810555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55059802878806491869979253 5161856519888108612810555)
            ·
              refine ⟨7742784779832162919215833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5161856519888108612810555 7742784779832162919215833)
              ·
                refine ⟨5807088584874122189411875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7742784779832162919215833 5807088584874122189411875)
                ·
                  refine ⟨8710632877311183284117813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5807088584874122189411875 8710632877311183284117813)
                  ·
                    refine ⟨816621832247923432886045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8710632877311183284117813 816621832247923432886045)
                    ·
                      rfl

theorem cell23_4771096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_4771096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771096 prefixEnd_4771096 := by exact prefixLift 4771096
  have htrace : WordTrace (prefixWord ++ tailWord_4771096) baseStart_4771096 baseEnd_4771096 := by
    simpa [prefixWord, tailWord_4771096, baseEnd_4771096] using wordTrace_append hprefix tailTrace_4771096
  have hstable : (prefixWord ++ tailWord_4771096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771096).length < 2 ^ (prefixWord ++ tailWord_4771096).sum := by decide
  have hdescent : baseEnd_4771096 < baseStart_4771096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771103 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 2, 3, 2]
def baseStart_4771103 : Nat := 118140960795 + 4771103 * 2 ^ 59
def prefixEnd_4771103 : Nat := 4983230072969 + 3 ^ 40 * 4771103 * 2
def baseEnd_4771103 : Nat := 2449869091108351771270603

theorem tailTrace_4771103 : CollatzResearch.WordTrace tailWord_4771103 prefixEnd_4771103 2449869091108351771270603 := by
  unfold tailWord_4771103
  simp only [CollatzResearch.WordTrace]
  refine ⟨174016422434116145364821963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116010948289410763576547975 174016422434116145364821963)
  ·
    refine ⟨261024633651174218047232945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174016422434116145364821963 261024633651174218047232945)
    ·
      refine ⟨195768475238380663535424709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261024633651174218047232945 195768475238380663535424709)
      ·
        refine ⟨36706589107196374412892133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195768475238380663535424709 36706589107196374412892133)
        ·
          refine ⟨6882485457599320202417275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36706589107196374412892133 6882485457599320202417275)
          ·
            refine ⟨10323728186398980303625913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6882485457599320202417275 10323728186398980303625913)
            ·
              refine ⟨7742796139799235227719435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10323728186398980303625913 7742796139799235227719435)
              ·
                refine ⟨11614194209698852841579153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7742796139799235227719435 11614194209698852841579153)
                ·
                  refine ⟨8710645657274139631184365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11614194209698852841579153 8710645657274139631184365)
                  ·
                    refine ⟨3266492121477802361694137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8710645657274139631184365 3266492121477802361694137)
                    ·
                      refine ⟨2449869091108351771270603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3266492121477802361694137 2449869091108351771270603)
                      ·
                        rfl

theorem cell23_4771103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_4771103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771103 prefixEnd_4771103 := by exact prefixLift 4771103
  have htrace : WordTrace (prefixWord ++ tailWord_4771103) baseStart_4771103 baseEnd_4771103 := by
    simpa [prefixWord, tailWord_4771103, baseEnd_4771103] using wordTrace_append hprefix tailTrace_4771103
  have hstable : (prefixWord ++ tailWord_4771103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771103).length < 2 ^ (prefixWord ++ tailWord_4771103).sum := by decide
  have hdescent : baseEnd_4771103 < baseStart_4771103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771109 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 1, 6]
def baseStart_4771109 : Nat := 118140960795 + 4771109 * 2 ^ 59
def prefixEnd_4771109 : Nat := 4983230072969 + 3 ^ 40 * 4771109 * 2
def baseEnd_4771109 : Nat := 816624057330759582598525

theorem tailTrace_4771109 : CollatzResearch.WordTrace tailWord_4771109 prefixEnd_4771109 816624057330759582598525 := by
  unfold tailWord_4771109
  simp only [CollatzResearch.WordTrace]
  refine ⟨174016641272094408389540381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116011094181396272259693587 174016641272094408389540381)
  ·
    refine ⟨65256240477035403146077643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174016641272094408389540381 65256240477035403146077643)
    ·
      refine ⟨97884360715553104719116465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65256240477035403146077643 97884360715553104719116465)
      ·
        refine ⟨73413270536664828539337349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97884360715553104719116465 73413270536664828539337349)
        ·
          refine ⟨13764988225624655351125753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73413270536664828539337349 13764988225624655351125753)
          ·
            refine ⟨10323741169218491513344315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13764988225624655351125753 10323741169218491513344315)
            ·
              refine ⟨15485611753827737270016473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10323741169218491513344315 15485611753827737270016473)
              ·
                refine ⟨11614208815370802952512355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15485611753827737270016473 11614208815370802952512355)
                ·
                  refine ⟨17421313223056204428768533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11614208815370802952512355 17421313223056204428768533)
                  ·
                    refine ⟨816624057330759582598525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17421313223056204428768533 816624057330759582598525)
                    ·
                      rfl

theorem cell23_4771109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_4771109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771109 prefixEnd_4771109 := by exact prefixLift 4771109
  have htrace : WordTrace (prefixWord ++ tailWord_4771109) baseStart_4771109 baseEnd_4771109 := by
    simpa [prefixWord, tailWord_4771109, baseEnd_4771109] using wordTrace_append hprefix tailTrace_4771109
  have hstable : (prefixWord ++ tailWord_4771109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771109).length < 2 ^ (prefixWord ++ tailWord_4771109).sum := by decide
  have hdescent : baseEnd_4771109 < baseStart_4771109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771122 : List Nat := [3, 2, 1, 1, 4, 12]
def baseStart_4771122 : Nat := 118140960795 + 4771122 * 2 ^ 59
def prefixEnd_4771122 : Nat := 4983230072969 + 3 ^ 40 * 4771122 * 2
def baseEnd_4771122 : Nat := 10081805955723404102605

theorem tailTrace_4771122 : CollatzResearch.WordTrace tailWord_4771122 prefixEnd_4771122 10081805955723404102605 := by
  unfold tailWord_4771122
  simp only [CollatzResearch.WordTrace]
  refine ⟨43504278855261827902440905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116011410280698207739842413 43504278855261827902440905)
  ·
    refine ⟨32628209141446370926830679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43504278855261827902440905 32628209141446370926830679)
    ·
      refine ⟨48942313712169556390246019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32628209141446370926830679 48942313712169556390246019)
      ·
        refine ⟨73413470568254334585369029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48942313712169556390246019 73413470568254334585369029)
        ·
          refine ⟨13765025731547687734756693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73413470568254334585369029 13765025731547687734756693)
          ·
            refine ⟨10081805955723404102605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13765025731547687734756693 10081805955723404102605)
            ·
              rfl

theorem cell23_4771122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 12].length) (baseStart_4771122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771122 prefixEnd_4771122 := by exact prefixLift 4771122
  have htrace : WordTrace (prefixWord ++ tailWord_4771122) baseStart_4771122 baseEnd_4771122 := by
    simpa [prefixWord, tailWord_4771122, baseEnd_4771122] using wordTrace_append hprefix tailTrace_4771122
  have hstable : (prefixWord ++ tailWord_4771122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771122).length < 2 ^ (prefixWord ++ tailWord_4771122).sum := by decide
  have hdescent : baseEnd_4771122 < baseStart_4771122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771152 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 2, 7]
def baseStart_4771152 : Nat := 118140960795 + 4771152 * 2 ^ 59
def prefixEnd_4771152 : Nat := 4983230072969 + 3 ^ 40 * 4771152 * 2
def baseEnd_4771152 : Nat := 816631417220140693185959

theorem tailTrace_4771152 : CollatzResearch.WordTrace tailWord_4771152 prefixEnd_4771152 816631417220140693185959 := by
  unfold tailWord_4771152
  simp only [CollatzResearch.WordTrace]
  refine ⟨87009104805469313366677855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116012139740625751155570473 87009104805469313366677855)
  ·
    refine ⟨130513657208203970050016783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87009104805469313366677855 130513657208203970050016783)
    ·
      refine ⟨195770485812305955075025175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130513657208203970050016783 195770485812305955075025175)
      ·
        refine ⟨293655728718458932612537763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195770485812305955075025175 293655728718458932612537763)
        ·
          refine ⟨440483593077688398918806645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293655728718458932612537763 440483593077688398918806645)
          ·
            refine ⟨41295336851033287398638123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 440483593077688398918806645 41295336851033287398638123)
            ·
              refine ⟨61943005276549931097957185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41295336851033287398638123 61943005276549931097957185)
              ·
                refine ⟨46457253957412448323467889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61943005276549931097957185 46457253957412448323467889)
                ·
                  refine ⟨34842940468059336242600917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46457253957412448323467889 34842940468059336242600917)
                  ·
                    refine ⟨816631417220140693185959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34842940468059336242600917 816631417220140693185959)
                    ·
                      rfl

theorem cell23_4771152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_4771152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771152 prefixEnd_4771152 := by exact prefixLift 4771152
  have htrace : WordTrace (prefixWord ++ tailWord_4771152) baseStart_4771152 baseEnd_4771152 := by
    simpa [prefixWord, tailWord_4771152, baseEnd_4771152] using wordTrace_append hprefix tailTrace_4771152
  have hstable : (prefixWord ++ tailWord_4771152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771152).length < 2 ^ (prefixWord ++ tailWord_4771152).sum := by decide
  have hdescent : baseEnd_4771152 < baseStart_4771152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771239 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_4771239 : Nat := 118140960795 + 4771239 * 2 ^ 59
def prefixEnd_4771239 : Nat := 4983230072969 + 3 ^ 40 * 4771239 * 2
def baseEnd_4771239 : Nat := 2449938924477363239169977

theorem tailTrace_4771239 : CollatzResearch.WordTrace tailWord_4771239 prefixEnd_4771239 2449938924477363239169977 := by
  unfold tailWord_4771239
  simp only [CollatzResearch.WordTrace]
  refine ⟨174021382761623440591772771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116014255174415627061181847 174021382761623440591772771)
  ·
    refine ⟨261032074142435160887659157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174021382761623440591772771 261032074142435160887659157)
    ·
      refine ⟨12235878475426648166609023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 261032074142435160887659157 12235878475426648166609023)
      ·
        refine ⟨18353817713139972249913535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12235878475426648166609023 18353817713139972249913535)
        ·
          refine ⟨27530726569709958374870303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18353817713139972249913535 27530726569709958374870303)
          ·
            refine ⟨41296089854564937562305455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27530726569709958374870303 41296089854564937562305455)
            ·
              refine ⟨61944134781847406343458183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41296089854564937562305455 61944134781847406343458183)
              ·
                refine ⟨92916202172771109515187275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61944134781847406343458183 92916202172771109515187275)
                ·
                  refine ⟨139374303259156664272780913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92916202172771109515187275 139374303259156664272780913)
                  ·
                    refine ⟨104530727444367498204585685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 139374303259156664272780913 104530727444367498204585685)
                    ·
                      refine ⟨2449938924477363239169977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104530727444367498204585685 2449938924477363239169977)
                      ·
                        rfl

theorem cell23_4771239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_4771239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771239 prefixEnd_4771239 := by exact prefixLift 4771239
  have htrace : WordTrace (prefixWord ++ tailWord_4771239) baseStart_4771239 baseEnd_4771239 := by
    simpa [prefixWord, tailWord_4771239, baseEnd_4771239] using wordTrace_append hprefix tailTrace_4771239
  have hstable : (prefixWord ++ tailWord_4771239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771239).length < 2 ^ (prefixWord ++ tailWord_4771239).sum := by decide
  have hdescent : baseEnd_4771239 < baseStart_4771239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771276 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 2, 5]
def baseStart_4771276 : Nat := 118140960795 + 4771276 * 2 ^ 59
def prefixEnd_4771276 : Nat := 4983230072969 + 3 ^ 40 * 4771276 * 2
def baseEnd_4771276 : Nat := 816652641087193198135769

theorem tailTrace_4771276 : CollatzResearch.WordTrace tailWord_4771276 prefixEnd_4771276 816652641087193198135769 := by
  unfold tailWord_4771276
  simp only [CollatzResearch.WordTrace]
  refine ⟨87011366131244697955434841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116015154841659597273913121 87011366131244697955434841)
  ·
    refine ⟨65258524598433523466576131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87011366131244697955434841 65258524598433523466576131)
    ·
      refine ⟨97887786897650285199864197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65258524598433523466576131 97887786897650285199864197)
      ·
        refine ⟨18353960043309428474974537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97887786897650285199864197 18353960043309428474974537)
        ·
          refine ⟨13765470032482071356230903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18353960043309428474974537 13765470032482071356230903)
          ·
            refine ⟨20648205048723107034346355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13765470032482071356230903 20648205048723107034346355)
            ·
              refine ⟨30972307573084660551519533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20648205048723107034346355 30972307573084660551519533)
              ·
                refine ⟨11614615339906747706819825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30972307573084660551519533 11614615339906747706819825)
                ·
                  refine ⟨8710961504930060780114869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11614615339906747706819825 8710961504930060780114869)
                  ·
                    refine ⟨816652641087193198135769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8710961504930060780114869 816652641087193198135769)
                    ·
                      rfl

theorem cell23_4771276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_4771276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771276 prefixEnd_4771276 := by exact prefixLift 4771276
  have htrace : WordTrace (prefixWord ++ tailWord_4771276) baseStart_4771276 baseEnd_4771276 := by
    simpa [prefixWord, tailWord_4771276, baseEnd_4771276] using wordTrace_append hprefix tailTrace_4771276
  have hstable : (prefixWord ++ tailWord_4771276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771276).length < 2 ^ (prefixWord ++ tailWord_4771276).sum := by decide
  have hdescent : baseEnd_4771276 < baseStart_4771276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771279 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 4]
def baseStart_4771279 : Nat := 118140960795 + 4771279 * 2 ^ 59
def prefixEnd_4771279 : Nat := 4983230072969 + 3 ^ 40 * 4771279 * 2
def baseEnd_4771279 : Nat := 2449959463703543082669793

theorem tailTrace_4771279 : CollatzResearch.WordTrace tailWord_4771279 prefixEnd_4771279 2449959463703543082669793 := by
  unfold tailWord_4771279
  simp only [CollatzResearch.WordTrace]
  refine ⟨174022841681478527423228891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116015227787652351615485927 174022841681478527423228891)
  ·
    refine ⟨261034262522217791134843337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174022841681478527423228891 261034262522217791134843337)
    ·
      refine ⟨195775696891663343351132503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261034262522217791134843337 195775696891663343351132503)
      ·
        refine ⟨293663545337495015026698755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195775696891663343351132503 293663545337495015026698755)
        ·
          refine ⟨440495318006242522540048133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293663545337495015026698755 440495318006242522540048133)
          ·
            refine ⟨82592872126170472976259025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 440495318006242522540048133 82592872126170472976259025)
            ·
              refine ⟨61944654094627854732194269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82592872126170472976259025 61944654094627854732194269)
              ·
                refine ⟨23229245285485445524572851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61944654094627854732194269 23229245285485445524572851)
                ·
                  refine ⟨34843867928228168286859277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23229245285485445524572851 34843867928228168286859277)
                  ·
                    refine ⟨13066450473085563107572229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34843867928228168286859277 13066450473085563107572229)
                    ·
                      refine ⟨2449959463703543082669793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13066450473085563107572229 2449959463703543082669793)
                      ·
                        rfl

theorem cell23_4771279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_4771279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771279 prefixEnd_4771279 := by exact prefixLift 4771279
  have htrace : WordTrace (prefixWord ++ tailWord_4771279) baseStart_4771279 baseEnd_4771279 := by
    simpa [prefixWord, tailWord_4771279, baseEnd_4771279] using wordTrace_append hprefix tailTrace_4771279
  have hstable : (prefixWord ++ tailWord_4771279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771279).length < 2 ^ (prefixWord ++ tailWord_4771279).sum := by decide
  have hdescent : baseEnd_4771279 < baseStart_4771279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771313 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 2, 4, 2]
def baseStart_4771313 : Nat := 118140960795 + 4771313 * 2 ^ 59
def prefixEnd_4771313 : Nat := 4983230072969 + 3 ^ 40 * 4771313 * 2
def baseEnd_4771313 : Nat := 2449976922045795949644637

theorem tailTrace_4771313 : CollatzResearch.WordTrace tailWord_4771313 prefixEnd_4771313 2449976922045795949644637 := by
  unfold tailWord_4771313
  simp only [CollatzResearch.WordTrace]
  refine ⟨174024081763355351229966593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116016054508903567486644395 174024081763355351229966593)
  ·
    refine ⟨130518061322516513422474945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174024081763355351229966593 130518061322516513422474945)
    ·
      refine ⟨97888545991887385066856209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130518061322516513422474945 97888545991887385066856209)
      ·
        refine ⟨73416409493915538800142157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97888545991887385066856209 73416409493915538800142157)
        ·
          refine ⟨27531153560218327050053309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73416409493915538800142157 27531153560218327050053309)
          ·
            refine ⟨10324182585081872643769991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27531153560218327050053309 10324182585081872643769991)
            ·
              refine ⟨15486273877622808965654987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10324182585081872643769991 15486273877622808965654987)
              ·
                refine ⟨23229410816434213448482481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15486273877622808965654987 23229410816434213448482481)
                ·
                  refine ⟨17422058112325660086361861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23229410816434213448482481 17422058112325660086361861)
                  ·
                    refine ⟨3266635896061061266192849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17422058112325660086361861 3266635896061061266192849)
                    ·
                      refine ⟨2449976922045795949644637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3266635896061061266192849 2449976922045795949644637)
                      ·
                        rfl

theorem cell23_4771313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_4771313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771313 prefixEnd_4771313 := by exact prefixLift 4771313
  have htrace : WordTrace (prefixWord ++ tailWord_4771313) baseStart_4771313 baseEnd_4771313 := by
    simpa [prefixWord, tailWord_4771313, baseEnd_4771313] using wordTrace_append hprefix tailTrace_4771313
  have hstable : (prefixWord ++ tailWord_4771313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771313).length < 2 ^ (prefixWord ++ tailWord_4771313).sum := by decide
  have hdescent : baseEnd_4771313 < baseStart_4771313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771330 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_4771330 : Nat := 118140960795 + 4771330 * 2 ^ 59
def prefixEnd_4771330 : Nat := 4983230072969 + 3 ^ 40 * 4771330 * 2
def baseEnd_4771330 : Nat := 2449985651216922383132059

theorem tailTrace_4771330 : CollatzResearch.WordTrace tailWord_4771330 prefixEnd_4771330 2449985651216922383132059 := by
  unfold tailWord_4771330
  simp only [CollatzResearch.WordTrace]
  refine ⟨43506175451073440783333861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116016467869529175422223629 43506175451073440783333861)
  ·
    refine ⟨8157407897076270146875099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43506175451073440783333861 8157407897076270146875099)
    ·
      refine ⟨12236111845614405220312649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8157407897076270146875099 12236111845614405220312649)
      ·
        refine ⟨9177083884210803915234487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12236111845614405220312649 9177083884210803915234487)
        ·
          refine ⟨13765625826316205872851731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9177083884210803915234487 13765625826316205872851731)
          ·
            refine ⟨20648438739474308809277597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13765625826316205872851731 20648438739474308809277597)
            ·
              refine ⟨7743164527302865803479099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20648438739474308809277597 7743164527302865803479099)
              ·
                refine ⟨11614746790954298705218649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7743164527302865803479099 11614746790954298705218649)
                ·
                  refine ⟨8711060093215724028913987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11614746790954298705218649 8711060093215724028913987)
                  ·
                    refine ⟨13066590139823586043370981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8711060093215724028913987 13066590139823586043370981)
                    ·
                      refine ⟨2449985651216922383132059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13066590139823586043370981 2449985651216922383132059)
                      ·
                        rfl

theorem cell23_4771330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_4771330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771330 prefixEnd_4771330 := by exact prefixLift 4771330
  have htrace : WordTrace (prefixWord ++ tailWord_4771330) baseStart_4771330 baseEnd_4771330 := by
    simpa [prefixWord, tailWord_4771330, baseEnd_4771330] using wordTrace_append hprefix tailTrace_4771330
  have hstable : (prefixWord ++ tailWord_4771330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771330).length < 2 ^ (prefixWord ++ tailWord_4771330).sum := by decide
  have hdescent : baseEnd_4771330 < baseStart_4771330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771383 : List Nat := [1, 1, 3, 1, 2, 5, 2, 2, 1, 5]
def baseStart_4771383 : Nat := 118140960795 + 4771383 * 2 ^ 59
def prefixEnd_4771383 : Nat := 4983230072969 + 3 ^ 40 * 4771383 * 2
def baseEnd_4771383 : Nat := 816670955230536891923105

theorem tailTrace_4771383 : CollatzResearch.WordTrace tailWord_4771383 prefixEnd_4771383 816670955230536891923105 := by
  unfold tailWord_4771383
  simp only [CollatzResearch.WordTrace]
  refine ⟨174026634873101753185014803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116017756582067835456676535 174026634873101753185014803)
  ·
    refine ⟨261039952309652629777522205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174026634873101753185014803 261039952309652629777522205)
    ·
      refine ⟨97889982116119736166570827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261039952309652629777522205 97889982116119736166570827)
      ·
        refine ⟨146834973174179604249856241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97889982116119736166570827 146834973174179604249856241)
        ·
          refine ⟨110126229880634703187392181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146834973174179604249856241 110126229880634703187392181)
          ·
            refine ⟨10324334051309503423818017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110126229880634703187392181 10324334051309503423818017)
            ·
              refine ⟨7743250538482127567863513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10324334051309503423818017 7743250538482127567863513)
              ·
                refine ⟨5807437903861595675897635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7743250538482127567863513 5807437903861595675897635)
                ·
                  refine ⟨8711156855792393513846453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5807437903861595675897635 8711156855792393513846453)
                  ·
                    refine ⟨816670955230536891923105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8711156855792393513846453 816670955230536891923105)
                    ·
                      rfl

theorem cell23_4771383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_4771383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771383 prefixEnd_4771383 := by exact prefixLift 4771383
  have htrace : WordTrace (prefixWord ++ tailWord_4771383) baseStart_4771383 baseEnd_4771383 := by
    simpa [prefixWord, tailWord_4771383, baseEnd_4771383] using wordTrace_append hprefix tailTrace_4771383
  have hstable : (prefixWord ++ tailWord_4771383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771383).length < 2 ^ (prefixWord ++ tailWord_4771383).sum := by decide
  have hdescent : baseEnd_4771383 < baseStart_4771383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771413 : List Nat := [1, 3, 2, 2, 1, 1, 1, 6, 2, 4]
def baseStart_4771413 : Nat := 118140960795 + 4771413 * 2 ^ 59
def prefixEnd_4771413 : Nat := 4983230072969 + 3 ^ 40 * 4771413 * 2
def baseEnd_4771413 : Nat := 816676090037081852798059

theorem tailTrace_4771413 : CollatzResearch.WordTrace tailWord_4771413 prefixEnd_4771413 816676090037081852798059 := by
  unfold tailWord_4771413
  simp only [CollatzResearch.WordTrace]
  refine ⟨174027729062993068308606893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116018486041995378872404595 174027729062993068308606893)
  ·
    refine ⟨65260398398622400615727585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174027729062993068308606893 65260398398622400615727585)
    ·
      refine ⟨48945298798966800461795689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65260398398622400615727585 48945298798966800461795689)
      ·
        refine ⟨36708974099225100346346767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48945298798966800461795689 36708974099225100346346767)
        ·
          refine ⟨55063461148837650519520151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36708974099225100346346767 55063461148837650519520151)
          ·
            refine ⟨82595191723256475779280227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55063461148837650519520151 82595191723256475779280227)
            ·
              refine ⟨123892787584884713668920341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82595191723256475779280227 123892787584884713668920341)
              ·
                refine ⟨5807474418041470953230641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 123892787584884713668920341 5807474418041470953230641)
                ·
                  refine ⟨4355605813531103214922981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5807474418041470953230641 4355605813531103214922981)
                  ·
                    refine ⟨816676090037081852798059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4355605813531103214922981 816676090037081852798059)
                    ·
                      rfl

theorem cell23_4771413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_4771413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771413 prefixEnd_4771413 := by exact prefixLift 4771413
  have htrace : WordTrace (prefixWord ++ tailWord_4771413) baseStart_4771413 baseEnd_4771413 := by
    simpa [prefixWord, tailWord_4771413, baseEnd_4771413] using wordTrace_append hprefix tailTrace_4771413
  have hstable : (prefixWord ++ tailWord_4771413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771413).length < 2 ^ (prefixWord ++ tailWord_4771413).sum := by decide
  have hdescent : baseEnd_4771413 < baseStart_4771413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771437 : List Nat := [1, 5, 1, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_4771437 : Nat := 118140960795 + 4771437 * 2 ^ 59
def prefixEnd_4771437 : Nat := 4983230072969 + 3 ^ 40 * 4771437 * 2
def baseEnd_4771437 : Nat := 2450040593646953464494067

theorem tailTrace_4771437 : CollatzResearch.WordTrace tailWord_4771437 prefixEnd_4771437 2450040593646953464494067 := by
  unfold tailWord_4771437
  simp only [CollatzResearch.WordTrace]
  refine ⟨174028604414906120407480565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116019069609937413604987043 174028604414906120407480565)
  ·
    refine ⟨16315181663897448788201303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174028604414906120407480565 16315181663897448788201303)
    ·
      refine ⟨24472772495846173182301955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16315181663897448788201303 24472772495846173182301955)
      ·
        refine ⟨36709158743769259773452933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24472772495846173182301955 36709158743769259773452933)
        ·
          refine ⟨6882967264456736207522425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36709158743769259773452933 6882967264456736207522425)
          ·
            refine ⟨5162225448342552155641819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6882967264456736207522425 5162225448342552155641819)
            ·
              refine ⟨7743338172513828233462729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5162225448342552155641819 7743338172513828233462729)
              ·
                refine ⟨5807503629385371175097047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7743338172513828233462729 5807503629385371175097047)
                ·
                  refine ⟨8711255444078056762645571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5807503629385371175097047 8711255444078056762645571)
                  ·
                    refine ⟨13066883166117085143968357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8711255444078056762645571 13066883166117085143968357)
                    ·
                      refine ⟨2450040593646953464494067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13066883166117085143968357 2450040593646953464494067)
                      ·
                        rfl

theorem cell23_4771437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_4771437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771437 prefixEnd_4771437 := by exact prefixLift 4771437
  have htrace : WordTrace (prefixWord ++ tailWord_4771437) baseStart_4771437 baseEnd_4771437 := by
    simpa [prefixWord, tailWord_4771437, baseEnd_4771437] using wordTrace_append hprefix tailTrace_4771437
  have hstable : (prefixWord ++ tailWord_4771437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771437).length < 2 ^ (prefixWord ++ tailWord_4771437).sum := by decide
  have hdescent : baseEnd_4771437 < baseStart_4771437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771440 : List Nat := [2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 3]
def baseStart_4771440 : Nat := 118140960795 + 4771440 * 2 ^ 59
def prefixEnd_4771440 : Nat := 4983230072969 + 3 ^ 40 * 4771440 * 2
def baseEnd_4771440 : Nat := 2450042134088916952756553

theorem tailTrace_4771440 : CollatzResearch.WordTrace tailWord_4771440 prefixEnd_4771440 2450042134088916952756553 := by
  unfold tailWord_4771440
  simp only [CollatzResearch.WordTrace]
  refine ⟨87014356916947625959919887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116019142555930167946559849 87014356916947625959919887)
  ·
    refine ⟨130521535375421438939879831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87014356916947625959919887 130521535375421438939879831)
    ·
      refine ⟨195782303063132158409819747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130521535375421438939879831 195782303063132158409819747)
      ·
        refine ⟨293673454594698237614729621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195782303063132158409819747 293673454594698237614729621)
        ·
          refine ⟨13765943184126479888190451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 293673454594698237614729621 13765943184126479888190451)
          ·
            refine ⟨20648914776189719832285677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13765943184126479888190451 20648914776189719832285677)
            ·
              refine ⟨7743343041071144937107129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20648914776189719832285677 7743343041071144937107129)
              ·
                refine ⟨5807507280803358702830347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7743343041071144937107129 5807507280803358702830347)
                ·
                  refine ⟨8711260921205038054245521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5807507280803358702830347 8711260921205038054245521)
                  ·
                    refine ⟨6533445690903778540684141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8711260921205038054245521 6533445690903778540684141)
                    ·
                      refine ⟨2450042134088916952756553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6533445690903778540684141 2450042134088916952756553)
                      ·
                        rfl

theorem cell23_4771440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 3].length) (baseStart_4771440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771440 prefixEnd_4771440 := by exact prefixLift 4771440
  have htrace : WordTrace (prefixWord ++ tailWord_4771440) baseStart_4771440 baseEnd_4771440 := by
    simpa [prefixWord, tailWord_4771440, baseEnd_4771440] using wordTrace_append hprefix tailTrace_4771440
  have hstable : (prefixWord ++ tailWord_4771440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771440).length < 2 ^ (prefixWord ++ tailWord_4771440).sum := by decide
  have hdescent : baseEnd_4771440 < baseStart_4771440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771453 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_4771453 : Nat := 118140960795 + 4771453 * 2 ^ 59
def prefixEnd_4771453 : Nat := 4983230072969 + 3 ^ 40 * 4771453 * 2
def baseEnd_4771453 : Nat := 2450048809337425401893993

theorem tailTrace_4771453 : CollatzResearch.WordTrace tailWord_4771453 prefixEnd_4771453 2450048809337425401893993 := by
  unfold tailWord_4771453
  simp only [CollatzResearch.WordTrace]
  refine ⟨174029187982848155140063013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116019458655232103426708675 174029187982848155140063013)
  ·
    refine ⟨32630472746784029088761815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174029187982848155140063013 32630472746784029088761815)
    ·
      refine ⟨48945709120176043633142723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32630472746784029088761815 48945709120176043633142723)
      ·
        refine ⟨73418563680264065449714085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48945709120176043633142723 73418563680264065449714085)
        ·
          refine ⟨13765980690049512271821391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73418563680264065449714085 13765980690049512271821391)
          ·
            refine ⟨20648971035074268407732087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13765980690049512271821391 20648971035074268407732087)
            ·
              refine ⟨30973456552611402611598131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20648971035074268407732087 30973456552611402611598131)
              ·
                refine ⟨46460184828917103917397197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30973456552611402611598131 46460184828917103917397197)
                ·
                  refine ⟨17422569310843913969023949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46460184828917103917397197 17422569310843913969023949)
                  ·
                    refine ⟨6533463491566467738383981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17422569310843913969023949 6533463491566467738383981)
                    ·
                      refine ⟨2450048809337425401893993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6533463491566467738383981 2450048809337425401893993)
                      ·
                        rfl

theorem cell23_4771453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_4771453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771453 prefixEnd_4771453 := by exact prefixLift 4771453
  have htrace : WordTrace (prefixWord ++ tailWord_4771453) baseStart_4771453 baseEnd_4771453 := by
    simpa [prefixWord, tailWord_4771453, baseEnd_4771453] using wordTrace_append hprefix tailTrace_4771453
  have hstable : (prefixWord ++ tailWord_4771453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771453).length < 2 ^ (prefixWord ++ tailWord_4771453).sum := by decide
  have hdescent : baseEnd_4771453 < baseStart_4771453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771457 : List Nat := [1, 2, 4, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_4771457 : Nat := 118140960795 + 4771457 * 2 ^ 59
def prefixEnd_4771457 : Nat := 4983230072969 + 3 ^ 40 * 4771457 * 2
def baseEnd_4771457 : Nat := 2450050863260043386243975

theorem tailTrace_4771457 : CollatzResearch.WordTrace tailWord_4771457 prefixEnd_4771457 2450050863260043386243975 := by
  unfold tailWord_4771457
  simp only [CollatzResearch.WordTrace]
  refine ⟨174029333874833663823208625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116019555916555775882139083 174029333874833663823208625)
  ·
    refine ⟨130522000406125247867406469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174029333874833663823208625 130522000406125247867406469)
    ·
      refine ⟨24472875076148483975138713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130522000406125247867406469 24472875076148483975138713)
      ·
        refine ⟨18354656307111362981354035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24472875076148483975138713 18354656307111362981354035)
        ·
          refine ⟨27531984460667044472031053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18354656307111362981354035 27531984460667044472031053)
          ·
            refine ⟨10324494172750141677011645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27531984460667044472031053 10324494172750141677011645)
            ·
              refine ⟨3871685314781303128879367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10324494172750141677011645 3871685314781303128879367)
              ·
                refine ⟨5807527972171954693319051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3871685314781303128879367 5807527972171954693319051)
                ·
                  refine ⟨8711291958257932039978577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5807527972171954693319051 8711291958257932039978577)
                  ·
                    refine ⟨6533468968693449029983933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8711291958257932039978577 6533468968693449029983933)
                    ·
                      refine ⟨2450050863260043386243975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6533468968693449029983933 2450050863260043386243975)
                      ·
                        rfl

theorem cell23_4771457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_4771457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771457 prefixEnd_4771457 := by exact prefixLift 4771457
  have htrace : WordTrace (prefixWord ++ tailWord_4771457) baseStart_4771457 baseEnd_4771457 := by
    simpa [prefixWord, tailWord_4771457, baseEnd_4771457] using wordTrace_append hprefix tailTrace_4771457
  have hstable : (prefixWord ++ tailWord_4771457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771457).length < 2 ^ (prefixWord ++ tailWord_4771457).sum := by decide
  have hdescent : baseEnd_4771457 < baseStart_4771457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771480 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 3, 3, 2]
def baseStart_4771480 : Nat := 118140960795 + 4771480 * 2 ^ 59
def prefixEnd_4771480 : Nat := 4983230072969 + 3 ^ 40 * 4771480 * 2
def baseEnd_4771480 : Nat := 2450062673315096796256369

theorem tailTrace_4771480 : CollatzResearch.WordTrace tailWord_4771480 prefixEnd_4771480 2450062673315096796256369 := by
  unfold tailWord_4771480
  simp only [CollatzResearch.WordTrace]
  refine ⟨87015086376875169375647947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116020115169166892500863929 87015086376875169375647947)
  ·
    refine ⟨130522629565312754063471921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87015086376875169375647947 130522629565312754063471921)
    ·
      refine ⟨97891972173984565547603941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130522629565312754063471921 97891972173984565547603941)
      ·
        refine ⟨18354744782622106040175739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97891972173984565547603941 18354744782622106040175739)
        ·
          refine ⟨27532117173933159060263609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18354744782622106040175739 27532117173933159060263609)
          ·
            refine ⟨20649087880449869295197707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27532117173933159060263609 20649087880449869295197707)
            ·
              refine ⟨30973631820674803942796561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20649087880449869295197707 30973631820674803942796561)
              ·
                refine ⟨23230223865506102957097421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30973631820674803942796561 23230223865506102957097421)
                ·
                  refine ⟨8711333949564788608911533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23230223865506102957097421 8711333949564788608911533)
                  ·
                    refine ⟨3266750231086795728341825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8711333949564788608911533 3266750231086795728341825)
                    ·
                      refine ⟨2450062673315096796256369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3266750231086795728341825 2450062673315096796256369)
                      ·
                        rfl

theorem cell23_4771480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_4771480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771480 prefixEnd_4771480 := by exact prefixLift 4771480
  have htrace : WordTrace (prefixWord ++ tailWord_4771480) baseStart_4771480 baseEnd_4771480 := by
    simpa [prefixWord, tailWord_4771480, baseEnd_4771480] using wordTrace_append hprefix tailTrace_4771480
  have hstable : (prefixWord ++ tailWord_4771480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771480).length < 2 ^ (prefixWord ++ tailWord_4771480).sum := by decide
  have hdescent : baseEnd_4771480 < baseStart_4771480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771487 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4771487 : Nat := 118140960795 + 4771487 * 2 ^ 59
def prefixEnd_4771487 : Nat := 4983230072969 + 3 ^ 40 * 4771487 * 2
def baseEnd_4771487 : Nat := 2450066267679678268868837

theorem tailTrace_4771487 : CollatzResearch.WordTrace tailWord_4771487 prefixEnd_4771487 2450066267679678268868837 := by
  unfold tailWord_4771487
  simp only [CollatzResearch.WordTrace]
  refine ⟨174030428064724978946800715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116020285376483319297867143 174030428064724978946800715)
  ·
    refine ⟨261045642097087468420201073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174030428064724978946800715 261045642097087468420201073)
    ·
      refine ⟨195784231572815601315150805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261045642097087468420201073 195784231572815601315150805)
      ·
        refine ⟨4588692927487865655823847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 195784231572815601315150805 4588692927487865655823847)
        ·
          refine ⟨6883039391231798483735771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4588692927487865655823847 6883039391231798483735771)
          ·
            refine ⟨10324559086847697725603657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6883039391231798483735771 10324559086847697725603657)
            ·
              refine ⟨7743419315135773294202743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10324559086847697725603657 7743419315135773294202743)
              ·
                refine ⟨11615128972703659941304115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7743419315135773294202743 11615128972703659941304115)
                ·
                  refine ⟨17422693459055489911956173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11615128972703659941304115 17422693459055489911956173)
                  ·
                    refine ⟨6533510047145808716983565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17422693459055489911956173 6533510047145808716983565)
                    ·
                      refine ⟨2450066267679678268868837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6533510047145808716983565 2450066267679678268868837)
                      ·
                        rfl

theorem cell23_4771487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4771487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771487 prefixEnd_4771487 := by exact prefixLift 4771487
  have htrace : WordTrace (prefixWord ++ tailWord_4771487) baseStart_4771487 baseEnd_4771487 := by
    simpa [prefixWord, tailWord_4771487, baseEnd_4771487] using wordTrace_append hprefix tailTrace_4771487
  have hstable : (prefixWord ++ tailWord_4771487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771487).length < 2 ^ (prefixWord ++ tailWord_4771487).sum := by decide
  have hdescent : baseEnd_4771487 < baseStart_4771487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771514 : List Nat := [3, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2]
def baseStart_4771514 : Nat := 118140960795 + 4771514 * 2 ^ 59
def prefixEnd_4771514 : Nat := 4983230072969 + 3 ^ 40 * 4771514 * 2
def baseEnd_4771514 : Nat := 2450080131657349663231213

theorem tailTrace_4771514 : CollatzResearch.WordTrace tailWord_4771514 prefixEnd_4771514 2450080131657349663231213 := by
  unfold tailWord_4771514
  simp only [CollatzResearch.WordTrace]
  refine ⟨43507853208906790639508399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116020941890418108372022397 43507853208906790639508399)
  ·
    refine ⟨65261779813360185959262599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43507853208906790639508399 65261779813360185959262599)
    ·
      refine ⟨97892669720040278938893899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65261779813360185959262599 97892669720040278938893899)
      ·
        refine ⟨146839004580060418408340849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97892669720040278938893899 146839004580060418408340849)
        ·
          refine ⟨110129253435045313806255637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146839004580060418408340849 110129253435045313806255637)
          ·
            refine ⟨5162308754767749084668233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110129253435045313806255637 5162308754767749084668233)
            ·
              refine ⟨3871731566075811813501175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5162308754767749084668233 3871731566075811813501175)
              ·
                refine ⟨5807597349113717720251763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3871731566075811813501175 5807597349113717720251763)
                ·
                  refine ⟨8711396023670576580377645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5807597349113717720251763 8711396023670576580377645)
                  ·
                    refine ⟨3266773508876466217641617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8711396023670576580377645 3266773508876466217641617)
                    ·
                      refine ⟨2450080131657349663231213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3266773508876466217641617 2450080131657349663231213)
                      ·
                        rfl

theorem cell23_4771514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2].length) (baseStart_4771514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771514 prefixEnd_4771514 := by exact prefixLift 4771514
  have htrace : WordTrace (prefixWord ++ tailWord_4771514) baseStart_4771514 baseEnd_4771514 := by
    simpa [prefixWord, tailWord_4771514, baseEnd_4771514] using wordTrace_append hprefix tailTrace_4771514
  have hstable : (prefixWord ++ tailWord_4771514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771514).length < 2 ^ (prefixWord ++ tailWord_4771514).sum := by decide
  have hdescent : baseEnd_4771514 < baseStart_4771514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771540 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4771540 : Nat := 118140960795 + 4771540 * 2 ^ 59
def prefixEnd_4771540 : Nat := 4983230072969 + 3 ^ 40 * 4771540 * 2
def baseEnd_4771540 : Nat := 2450093482154366561506093

theorem tailTrace_4771540 : CollatzResearch.WordTrace tailWord_4771540 prefixEnd_4771540 2450093482154366561506093 := by
  unfold tailWord_4771540
  simp only [CollatzResearch.WordTrace]
  refine ⟨87016180566766484499240037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116021574089021979332320049 87016180566766484499240037)
  ·
    refine ⟨16315533856268715843607507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87016180566766484499240037 16315533856268715843607507)
    ·
      refine ⟨24473300784403073765411261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16315533856268715843607507 24473300784403073765411261)
      ·
        refine ⟨9177487794151152662029223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24473300784403073765411261 9177487794151152662029223)
        ·
          refine ⟨13766231691226728993043835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9177487794151152662029223 13766231691226728993043835)
          ·
            refine ⟨20649347536840093489565753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13766231691226728993043835 20649347536840093489565753)
            ·
              refine ⟨15487010652630070117174315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20649347536840093489565753 15487010652630070117174315)
              ·
                refine ⟨23230515978945105175761473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15487010652630070117174315 23230515978945105175761473)
                ·
                  refine ⟨17422886984208828881821105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23230515978945105175761473 17422886984208828881821105)
                  ·
                    refine ⟨13067165238156621661365829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17422886984208828881821105 13067165238156621661365829)
                    ·
                      refine ⟨2450093482154366561506093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13067165238156621661365829 2450093482154366561506093)
                      ·
                        rfl

theorem cell23_4771540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4771540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771540 prefixEnd_4771540 := by exact prefixLift 4771540
  have htrace : WordTrace (prefixWord ++ tailWord_4771540) baseStart_4771540 baseEnd_4771540 := by
    simpa [prefixWord, tailWord_4771540, baseEnd_4771540] using wordTrace_append hprefix tailTrace_4771540
  have hstable : (prefixWord ++ tailWord_4771540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771540).length < 2 ^ (prefixWord ++ tailWord_4771540).sum := by decide
  have hdescent : baseEnd_4771540 < baseStart_4771540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771543 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 3]
def baseStart_4771543 : Nat := 118140960795 + 4771543 * 2 ^ 59
def prefixEnd_4771543 : Nat := 4983230072969 + 3 ^ 40 * 4771543 * 2
def baseEnd_4771543 : Nat := 2450095022596330049768579

theorem tailTrace_4771543 : CollatzResearch.WordTrace tailWord_4771543 prefixEnd_4771543 2450095022596330049768579 := by
  unfold tailWord_4771543
  simp only [CollatzResearch.WordTrace]
  refine ⟨174032470552522100510839283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116021647035014733673892855 174032470552522100510839283)
  ·
    refine ⟨261048705828783150766258925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174032470552522100510839283 261048705828783150766258925)
    ·
      refine ⟨97893264685793681537347097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261048705828783150766258925 97893264685793681537347097)
      ·
        refine ⟨73419948514345261153010323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97893264685793681537347097 73419948514345261153010323)
        ·
          refine ⟨110129922771517891729515485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73419948514345261153010323 110129922771517891729515485)
          ·
            refine ⟨41298721039319209398568307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110129922771517891729515485 41298721039319209398568307)
            ·
              refine ⟨61948081558978814097852461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41298721039319209398568307 61948081558978814097852461)
              ·
                refine ⟨23230530584617055286694673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61948081558978814097852461 23230530584617055286694673)
                ·
                  refine ⟨17422897938462791465021005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23230530584617055286694673 17422897938462791465021005)
                  ·
                    refine ⟨6533586726923546799382877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17422897938462791465021005 6533586726923546799382877)
                    ·
                      refine ⟨2450095022596330049768579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6533586726923546799382877 2450095022596330049768579)
                      ·
                        rfl

theorem cell23_4771543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_4771543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771543 prefixEnd_4771543 := by exact prefixLift 4771543
  have htrace : WordTrace (prefixWord ++ tailWord_4771543) baseStart_4771543 baseEnd_4771543 := by
    simpa [prefixWord, tailWord_4771543, baseEnd_4771543] using wordTrace_append hprefix tailTrace_4771543
  have hstable : (prefixWord ++ tailWord_4771543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771543).length < 2 ^ (prefixWord ++ tailWord_4771543).sum := by decide
  have hdescent : baseEnd_4771543 < baseStart_4771543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771544 : List Nat := [2, 1, 2, 2, 3, 1, 5, 1, 2, 2, 2]
def baseStart_4771544 : Nat := 118140960795 + 4771544 * 2 ^ 59
def prefixEnd_4771544 : Nat := 4983230072969 + 3 ^ 40 * 4771544 * 2
def baseEnd_4771544 : Nat := 2450095536076984545856075

theorem tailTrace_4771544 : CollatzResearch.WordTrace tailWord_4771544 prefixEnd_4771544 2450095536076984545856075 := by
  unfold tailWord_4771544
  simp only [CollatzResearch.WordTrace]
  refine ⟨87016253512759238840812843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116021671350345651787750457 87016253512759238840812843)
  ·
    refine ⟨130524380269138858261219265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87016253512759238840812843 130524380269138858261219265)
    ·
      refine ⟨97893285201854143695914449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130524380269138858261219265 97893285201854143695914449)
      ·
        refine ⟨73419963901390607771935837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97893285201854143695914449 73419963901390607771935837)
        ·
          refine ⟨27532486463021477914475939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73419963901390607771935837 27532486463021477914475939)
          ·
            refine ⟨41298729694532216871713909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27532486463021477914475939 41298729694532216871713909)
            ·
              refine ⟨3871755908862395331723179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41298729694532216871713909 3871755908862395331723179)
              ·
                refine ⟨5807633863293592997584769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3871755908862395331723179 5807633863293592997584769)
                ·
                  refine ⟨4355725397470194748188577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5807633863293592997584769 4355725397470194748188577)
                  ·
                    refine ⟨3266794048102646061141433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4355725397470194748188577 3266794048102646061141433)
                    ·
                      refine ⟨2450095536076984545856075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3266794048102646061141433 2450095536076984545856075)
                      ·
                        rfl

theorem cell23_4771544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_4771544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771544 prefixEnd_4771544 := by exact prefixLift 4771544
  have htrace : WordTrace (prefixWord ++ tailWord_4771544) baseStart_4771544 baseEnd_4771544 := by
    simpa [prefixWord, tailWord_4771544, baseEnd_4771544] using wordTrace_append hprefix tailTrace_4771544
  have hstable : (prefixWord ++ tailWord_4771544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771544).length < 2 ^ (prefixWord ++ tailWord_4771544).sum := by decide
  have hdescent : baseEnd_4771544 < baseStart_4771544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771583 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 4]
def baseStart_4771583 : Nat := 118140960795 + 4771583 * 2 ^ 59
def prefixEnd_4771583 : Nat := 4983230072969 + 3 ^ 40 * 4771583 * 2
def baseEnd_4771583 : Nat := 2450115561822509893268395

theorem tailTrace_4771583 : CollatzResearch.WordTrace tailWord_4771583 prefixEnd_4771583 2450115561822509893268395 := by
  unfold tailWord_4771583
  simp only [CollatzResearch.WordTrace]
  refine ⟨174033929472377187342295403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116022619648251458228196935 174033929472377187342295403)
  ·
    refine ⟨261050894208565781013443105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174033929472377187342295403 261050894208565781013443105)
    ·
      refine ⟨195788170656424335760082329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261050894208565781013443105 195788170656424335760082329)
      ·
        refine ⟨146841127992318251820061747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195788170656424335760082329 146841127992318251820061747)
        ·
          refine ⟨220261691988477377730092621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146841127992318251820061747 220261691988477377730092621)
          ·
            refine ⟨82598134495679016648784733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220261691988477377730092621 82598134495679016648784733)
            ·
              refine ⟨30974300435879631243294275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82598134495679016648784733 30974300435879631243294275)
              ·
                refine ⟨46461450653819446864941413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30974300435879631243294275 46461450653819446864941413)
                ·
                  refine ⟨8711521997591146287176515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46461450653819446864941413 8711521997591146287176515)
                  ·
                    refine ⟨13067282996386719430764773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8711521997591146287176515 13067282996386719430764773)
                    ·
                      refine ⟨2450115561822509893268395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13067282996386719430764773 2450115561822509893268395)
                      ·
                        rfl

theorem cell23_4771583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_4771583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771583 prefixEnd_4771583 := by exact prefixLift 4771583
  have htrace : WordTrace (prefixWord ++ tailWord_4771583) baseStart_4771583 baseEnd_4771583 := by
    simpa [prefixWord, tailWord_4771583, baseEnd_4771583] using wordTrace_append hprefix tailTrace_4771583
  have hstable : (prefixWord ++ tailWord_4771583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771583).length < 2 ^ (prefixWord ++ tailWord_4771583).sum := by decide
  have hdescent : baseEnd_4771583 < baseStart_4771583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771603 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 3]
def baseStart_4771603 : Nat := 118140960795 + 4771603 * 2 ^ 59
def prefixEnd_4771603 : Nat := 4983230072969 + 3 ^ 40 * 4771603 * 2
def baseEnd_4771603 : Nat := 2450125831435599815018303

theorem tailTrace_4771603 : CollatzResearch.WordTrace tailWord_4771603 prefixEnd_4771603 2450125831435599815018303 := by
  unfold tailWord_4771603
  simp only [CollatzResearch.WordTrace]
  refine ⟨174034658932304730758023463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116023105954869820505348975 174034658932304730758023463)
  ·
    refine ⟨261051988398457096137035195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174034658932304730758023463 261051988398457096137035195)
    ·
      refine ⟨391577982597685644205552793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261051988398457096137035195 391577982597685644205552793)
      ·
        refine ⟨293683486948264233154164595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391577982597685644205552793 293683486948264233154164595)
        ·
          refine ⟨440525230422396349731246893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293683486948264233154164595 440525230422396349731246893)
          ·
            refine ⟨165196961408398631149217585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 440525230422396349731246893 165196961408398631149217585)
            ·
              refine ⟨123897721056298973361913189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165196961408398631149217585 123897721056298973361913189)
              ·
                refine ⟨23230822698056057505358723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123897721056298973361913189 23230822698056057505358723)
                ·
                  refine ⟨34846234047084086258038085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23230822698056057505358723 34846234047084086258038085)
                  ·
                    refine ⟨6533668883828266173382141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34846234047084086258038085 6533668883828266173382141)
                    ·
                      refine ⟨2450125831435599815018303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6533668883828266173382141 2450125831435599815018303)
                      ·
                        rfl

theorem cell23_4771603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 3].length) (baseStart_4771603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771603 prefixEnd_4771603 := by exact prefixLift 4771603
  have htrace : WordTrace (prefixWord ++ tailWord_4771603) baseStart_4771603 baseEnd_4771603 := by
    simpa [prefixWord, tailWord_4771603, baseEnd_4771603] using wordTrace_append hprefix tailTrace_4771603
  have hstable : (prefixWord ++ tailWord_4771603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771603).length < 2 ^ (prefixWord ++ tailWord_4771603).sum := by decide
  have hdescent : baseEnd_4771603 < baseStart_4771603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771640 : List Nat := [2, 1, 2, 1, 3, 4, 2, 2, 6]
def baseStart_4771640 : Nat := 118140960795 + 4771640 * 2 ^ 59
def prefixEnd_4771640 : Nat := 4983230072969 + 3 ^ 40 * 4771640 * 2
def baseEnd_4771640 : Nat := 272238314468868463361737

theorem tailTrace_4771640 : CollatzResearch.WordTrace tailWord_4771640 prefixEnd_4771640 272238314468868463361737 := by
  unfold tailWord_4771640
  simp only [CollatzResearch.WordTrace]
  refine ⟨87018004216585343038560187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116024005622113790718080249 87018004216585343038560187)
  ·
    refine ⟨130527006324878014557840281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87018004216585343038560187 130527006324878014557840281)
    ·
      refine ⟨97895254743658510918380211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130527006324878014557840281 97895254743658510918380211)
      ·
        refine ⟨146842882115487766377570317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97895254743658510918380211 146842882115487766377570317)
        ·
          refine ⟨55066080793307912391588869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146842882115487766377570317 55066080793307912391588869)
          ·
            refine ⟨10324890148745233573422913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55066080793307912391588869 10324890148745233573422913)
            ·
              refine ⟨7743667611558925180067185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10324890148745233573422913 7743667611558925180067185)
              ·
                refine ⟨5807750708669193885050389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7743667611558925180067185 5807750708669193885050389)
                ·
                  refine ⟨272238314468868463361737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5807750708669193885050389 272238314468868463361737)
                  ·
                    rfl

theorem cell23_4771640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 6].length) (baseStart_4771640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771640 prefixEnd_4771640 := by exact prefixLift 4771640
  have htrace : WordTrace (prefixWord ++ tailWord_4771640) baseStart_4771640 baseEnd_4771640 := by
    simpa [prefixWord, tailWord_4771640, baseEnd_4771640] using wordTrace_append hprefix tailTrace_4771640
  have hstable : (prefixWord ++ tailWord_4771640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771640).length < 2 ^ (prefixWord ++ tailWord_4771640).sum := by decide
  have hdescent : baseEnd_4771640 < baseStart_4771640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771644 : List Nat := [2, 2, 2, 2, 1, 1, 6, 2, 1, 4]
def baseStart_4771644 : Nat := 118140960795 + 4771644 * 2 ^ 59
def prefixEnd_4771644 : Nat := 4983230072969 + 3 ^ 40 * 4771644 * 2
def baseEnd_4771644 : Nat := 816715628047478051535205

theorem tailTrace_4771644 : CollatzResearch.WordTrace tailWord_4771644 prefixEnd_4771644 816715628047478051535205 := by
  unfold tailWord_4771644
  simp only [CollatzResearch.WordTrace]
  refine ⟨87018077162578097380132993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116024102883437463173510657 87018077162578097380132993)
  ·
    refine ⟨65263557871933573035099745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87018077162578097380132993 65263557871933573035099745)
    ·
      refine ⟨48947668403950179776324809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65263557871933573035099745 48947668403950179776324809)
      ·
        refine ⟨36710751302962634832243607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48947668403950179776324809 36710751302962634832243607)
        ·
          refine ⟨55066126954443952248365411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36710751302962634832243607 55066126954443952248365411)
          ·
            refine ⟨82599190431665928372548117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55066126954443952248365411 82599190431665928372548117)
            ·
              refine ⟨3871837051484340392463193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82599190431665928372548117 3871837051484340392463193)
              ·
                refine ⟨2903877788613255294347395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3871837051484340392463193 2903877788613255294347395)
                ·
                  refine ⟨4355816682919882941521093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2903877788613255294347395 4355816682919882941521093)
                  ·
                    refine ⟨816715628047478051535205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4355816682919882941521093 816715628047478051535205)
                    ·
                      rfl

theorem cell23_4771644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_4771644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771644 prefixEnd_4771644 := by exact prefixLift 4771644
  have htrace : WordTrace (prefixWord ++ tailWord_4771644) baseStart_4771644 baseEnd_4771644 := by
    simpa [prefixWord, tailWord_4771644, baseEnd_4771644] using wordTrace_append hprefix tailTrace_4771644
  have hstable : (prefixWord ++ tailWord_4771644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771644).length < 2 ^ (prefixWord ++ tailWord_4771644).sum := by decide
  have hdescent : baseEnd_4771644 < baseStart_4771644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771653 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 5, 5]
def baseStart_4771653 : Nat := 118140960795 + 4771653 * 2 ^ 59
def prefixEnd_4771653 : Nat := 4983230072969 + 3 ^ 40 * 4771653 * 2
def baseEnd_4771653 : Nat := 816717168489441539797691

theorem tailTrace_4771653 : CollatzResearch.WordTrace tailWord_4771653 prefixEnd_4771653 816717168489441539797691 := by
  unfold tailWord_4771653
  simp only [CollatzResearch.WordTrace]
  refine ⟨174036482582123589297343613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116024321721415726198229075 174036482582123589297343613)
  ·
    refine ⟨65263680968296345986503855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174036482582123589297343613 65263680968296345986503855)
    ·
      refine ⟨97895521452444518979755783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65263680968296345986503855 97895521452444518979755783)
      ·
        refine ⟨146843282178666778469633675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97895521452444518979755783 146843282178666778469633675)
        ·
          refine ⟨220264923268000167704450513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146843282178666778469633675 220264923268000167704450513)
          ·
            refine ⟨165198692451000125778337885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220264923268000167704450513 165198692451000125778337885)
            ·
              refine ⟨61949509669125047166876707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165198692451000125778337885 61949509669125047166876707)
              ·
                refine ⟨92924264503687570750315061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61949509669125047166876707 92924264503687570750315061)
                ·
                  refine ⟨8711649797220709757842037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92924264503687570750315061 8711649797220709757842037)
                  ·
                    refine ⟨816717168489441539797691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8711649797220709757842037 816717168489441539797691)
                    ·
                      rfl

theorem cell23_4771653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_4771653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771653 prefixEnd_4771653 := by exact prefixLift 4771653
  have htrace : WordTrace (prefixWord ++ tailWord_4771653) baseStart_4771653 baseEnd_4771653 := by
    simpa [prefixWord, tailWord_4771653, baseEnd_4771653] using wordTrace_append hprefix tailTrace_4771653
  have hstable : (prefixWord ++ tailWord_4771653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771653).length < 2 ^ (prefixWord ++ tailWord_4771653).sum := by decide
  have hdescent : baseEnd_4771653 < baseStart_4771653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771703 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_4771703 : Nat := 118140960795 + 4771703 * 2 ^ 59
def prefixEnd_4771703 : Nat := 4983230072969 + 3 ^ 40 * 4771703 * 2
def baseEnd_4771703 : Nat := 2450177179501049423767843

theorem tailTrace_4771703 : CollatzResearch.WordTrace tailWord_4771703 prefixEnd_4771703 2450177179501049423767843 := by
  unfold tailWord_4771703
  simp only [CollatzResearch.WordTrace]
  refine ⟨174038306231942447836663763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116025537487961631891109175 174038306231942447836663763)
  ·
    refine ⟨261057459347913671754995645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174038306231942447836663763 261057459347913671754995645)
    ·
      refine ⟨97896547255467626908123367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261057459347913671754995645 97896547255467626908123367)
      ·
        refine ⟨146844820883201440362185051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97896547255467626908123367 146844820883201440362185051)
        ·
          refine ⟨220267231324802160543277577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146844820883201440362185051 220267231324802160543277577)
          ·
            refine ⟨165200423493601620407458183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220267231324802160543277577 165200423493601620407458183)
            ·
              refine ⟨247800635240402430611187275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165200423493601620407458183 247800635240402430611187275)
              ·
                refine ⟨371700952860603645916780913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247800635240402430611187275 371700952860603645916780913)
                ·
                  refine ⟨278775714645452734437585685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371700952860603645916780913 278775714645452734437585685)
                  ·
                    refine ⟨13067611624005596926761829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 278775714645452734437585685 13067611624005596926761829)
                    ·
                      refine ⟨2450177179501049423767843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13067611624005596926761829 2450177179501049423767843)
                      ·
                        rfl

theorem cell23_4771703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_4771703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771703 prefixEnd_4771703 := by exact prefixLift 4771703
  have htrace : WordTrace (prefixWord ++ tailWord_4771703) baseStart_4771703 baseEnd_4771703 := by
    simpa [prefixWord, tailWord_4771703, baseEnd_4771703] using wordTrace_append hprefix tailTrace_4771703
  have hstable : (prefixWord ++ tailWord_4771703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771703).length < 2 ^ (prefixWord ++ tailWord_4771703).sum := by decide
  have hdescent : baseEnd_4771703 < baseStart_4771703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771764 : List Nat := [2, 5, 2, 1, 2, 1, 2, 8]
def baseStart_4771764 : Nat := 118140960795 + 4771764 * 2 ^ 59
def prefixEnd_4771764 : Nat := 4983230072969 + 3 ^ 40 * 4771764 * 2
def baseEnd_4771764 : Nat := 90748463030406432781669

theorem tailTrace_4771764 : CollatzResearch.WordTrace tailWord_4771764 prefixEnd_4771764 90748463030406432781669 := by
  unfold tailWord_4771764
  simp only [CollatzResearch.WordTrace]
  refine ⟨87020265542360727627317173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116027020723147636836422897 87020265542360727627317173)
  ·
    refine ⟨8158149894596318215060985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87020265542360727627317173 8158149894596318215060985)
    ·
      refine ⟨6118612420947238661295739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8158149894596318215060985 6118612420947238661295739)
      ·
        refine ⟨9177918631420857991943609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6118612420947238661295739 9177918631420857991943609)
        ·
          refine ⟨6883438973565643493957707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9177918631420857991943609 6883438973565643493957707)
          ·
            refine ⟨10325158460348465240936561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6883438973565643493957707 10325158460348465240936561)
            ·
              refine ⟨7743868845261348930702421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10325158460348465240936561 7743868845261348930702421)
              ·
                refine ⟨90748463030406432781669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7743868845261348930702421 90748463030406432781669)
                ·
                  rfl

theorem cell23_4771764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 8].length) (baseStart_4771764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771764 prefixEnd_4771764 := by exact prefixLift 4771764
  have htrace : WordTrace (prefixWord ++ tailWord_4771764) baseStart_4771764 baseEnd_4771764 := by
    simpa [prefixWord, tailWord_4771764, baseEnd_4771764] using wordTrace_append hprefix tailTrace_4771764
  have hstable : (prefixWord ++ tailWord_4771764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771764).length < 2 ^ (prefixWord ++ tailWord_4771764).sum := by decide
  have hdescent : baseEnd_4771764 < baseStart_4771764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771767 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 3, 3, 2]
def baseStart_4771767 : Nat := 118140960795 + 4771767 * 2 ^ 59
def prefixEnd_4771767 : Nat := 4983230072969 + 3 ^ 40 * 4771767 * 2
def baseEnd_4771767 : Nat := 2450210042262937173367549

theorem tailTrace_4771767 : CollatzResearch.WordTrace tailWord_4771767 prefixEnd_4771767 2450210042262937173367549 := by
  unfold tailWord_4771767
  simp only [CollatzResearch.WordTrace]
  refine ⟨174040640503710586766993555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116027093669140391177995703 174040640503710586766993555)
  ·
    refine ⟨261060960755565880150490333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174040640503710586766993555 261060960755565880150490333)
    ·
      refine ⟨97897860283337205056433875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261060960755565880150490333 97897860283337205056433875)
      ·
        refine ⟨146846790425005807584650813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97897860283337205056433875 146846790425005807584650813)
        ·
          refine ⟨55067546409377177844244055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146846790425005807584650813 55067546409377177844244055)
          ·
            refine ⟨82601319614065766766366083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55067546409377177844244055 82601319614065766766366083)
            ·
              refine ⟨123901979421098650149549125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82601319614065766766366083 123901979421098650149549125)
              ·
                refine ⟨23231621141455996903040461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123901979421098650149549125 23231621141455996903040461)
                ·
                  refine ⟨8711857928045998838640173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23231621141455996903040461 8711857928045998838640173)
                  ·
                    refine ⟨3266946723017249564490065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8711857928045998838640173 3266946723017249564490065)
                    ·
                      refine ⟨2450210042262937173367549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3266946723017249564490065 2450210042262937173367549)
                      ·
                        rfl

theorem cell23_4771767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 3, 2].length) (baseStart_4771767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771767 prefixEnd_4771767 := by exact prefixLift 4771767
  have htrace : WordTrace (prefixWord ++ tailWord_4771767) baseStart_4771767 baseEnd_4771767 := by
    simpa [prefixWord, tailWord_4771767, baseEnd_4771767] using wordTrace_append hprefix tailTrace_4771767
  have hstable : (prefixWord ++ tailWord_4771767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771767).length < 2 ^ (prefixWord ++ tailWord_4771767).sum := by decide
  have hdescent : baseEnd_4771767 < baseStart_4771767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771784 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 3, 3, 2]
def baseStart_4771784 : Nat := 118140960795 + 4771784 * 2 ^ 59
def prefixEnd_4771784 : Nat := 4983230072969 + 3 ^ 40 * 4771784 * 2
def baseEnd_4771784 : Nat := 2450218771434063606854971

theorem tailTrace_4771784 : CollatzResearch.WordTrace tailWord_4771784 prefixEnd_4771784 2450218771434063606854971 := by
  unfold tailWord_4771784
  simp only [CollatzResearch.WordTrace]
  refine ⟨87020630272324499335181203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116027507029765999113574937 87020630272324499335181203)
  ·
    refine ⟨130530945408486749002771805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87020630272324499335181203 130530945408486749002771805)
    ·
      refine ⟨48949104528182530876039427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130530945408486749002771805 48949104528182530876039427)
      ·
        refine ⟨73423656792273796314059141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48949104528182530876039427 73423656792273796314059141)
        ·
          refine ⟨13766935648551336808886089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73423656792273796314059141 13766935648551336808886089)
          ·
            refine ⟨10325201736413502606664567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13766935648551336808886089 10325201736413502606664567)
            ·
              refine ⟨15487802604620253909996851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10325201736413502606664567 15487802604620253909996851)
              ·
                refine ⟨23231703906930380864995277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15487802604620253909996851 23231703906930380864995277)
                ·
                  refine ⟨8711888965098892824373229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23231703906930380864995277 8711888965098892824373229)
                  ·
                    refine ⟨3266958361912084809139961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8711888965098892824373229 3266958361912084809139961)
                    ·
                      refine ⟨2450218771434063606854971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3266958361912084809139961 2450218771434063606854971)
                      ·
                        rfl

theorem cell23_4771784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_4771784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771784 prefixEnd_4771784 := by exact prefixLift 4771784
  have htrace : WordTrace (prefixWord ++ tailWord_4771784) baseStart_4771784 baseEnd_4771784 := by
    simpa [prefixWord, tailWord_4771784, baseEnd_4771784] using wordTrace_append hprefix tailTrace_4771784
  have hstable : (prefixWord ++ tailWord_4771784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771784).length < 2 ^ (prefixWord ++ tailWord_4771784).sum := by decide
  have hdescent : baseEnd_4771784 < baseStart_4771784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771800 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_4771800 : Nat := 118140960795 + 4771800 * 2 ^ 59
def prefixEnd_4771800 : Nat := 4983230072969 + 3 ^ 40 * 4771800 * 2
def baseEnd_4771800 : Nat := 2450226987124535544254897

theorem tailTrace_4771800 : CollatzResearch.WordTrace tailWord_4771800 prefixEnd_4771800 2450226987124535544254897 := by
  unfold tailWord_4771800
  simp only [CollatzResearch.WordTrace]
  refine ⟨87020922056295516701472427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116027896075060688935296569 87020922056295516701472427)
  ·
    refine ⟨130531383084443275052208641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87020922056295516701472427 130531383084443275052208641)
    ·
      refine ⟨97898537313332456289156481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130531383084443275052208641 97898537313332456289156481)
      ·
        refine ⟨73423902984999342216867361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97898537313332456289156481 73423902984999342216867361)
        ·
          refine ⟨55067927238749506662650521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73423902984999342216867361 55067927238749506662650521)
          ·
            refine ⟨41300945429062129996987891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55067927238749506662650521 41300945429062129996987891)
            ·
              refine ⟨61951418143593194995481837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41300945429062129996987891 61951418143593194995481837)
              ·
                refine ⟨23231781803847448123305689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61951418143593194995481837 23231781803847448123305689)
                ·
                  refine ⟨17423836352885586092479267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23231781803847448123305689 17423836352885586092479267)
                  ·
                    refine ⟨26135754529328379138718901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17423836352885586092479267 26135754529328379138718901)
                    ·
                      refine ⟨2450226987124535544254897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26135754529328379138718901 2450226987124535544254897)
                      ·
                        rfl

theorem cell23_4771800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_4771800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771800 prefixEnd_4771800 := by exact prefixLift 4771800
  have htrace : WordTrace (prefixWord ++ tailWord_4771800) baseStart_4771800 baseEnd_4771800 := by
    simpa [prefixWord, tailWord_4771800, baseEnd_4771800] using wordTrace_append hprefix tailTrace_4771800
  have hstable : (prefixWord ++ tailWord_4771800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771800).length < 2 ^ (prefixWord ++ tailWord_4771800).sum := by decide
  have hdescent : baseEnd_4771800 < baseStart_4771800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771854 : List Nat := [4, 1, 1, 2, 2, 1, 4, 3, 5]
def baseStart_4771854 : Nat := 118140960795 + 4771854 * 2 ^ 59
def prefixEnd_4771854 : Nat := 4983230072969 + 3 ^ 40 * 4771854 * 2
def baseEnd_4771854 : Nat := 272250523897764259219961

theorem tailTrace_4771854 : CollatzResearch.WordTrace tailWord_4771854 prefixEnd_4771854 272250523897764259219961 := by
  unfold tailWord_4771854
  simp only [CollatzResearch.WordTrace]
  refine ⟨21755476706799425078176327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116029209102930267083607077 21755476706799425078176327)
  ·
    refine ⟨32633215060199137617264491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21755476706799425078176327 32633215060199137617264491)
    ·
      refine ⟨48949822590298706425896737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32633215060199137617264491 48949822590298706425896737)
      ·
        refine ⟨36712366942724029819422553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48949822590298706425896737 36712366942724029819422553)
        ·
          refine ⟨27534275207043022364566915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36712366942724029819422553 27534275207043022364566915)
          ·
            refine ⟨41301412810564533546850373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27534275207043022364566915 41301412810564533546850373)
            ·
              refine ⟨7744014901980850040034445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41301412810564533546850373 7744014901980850040034445)
              ·
                refine ⟨2904005588242818765012917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7744014901980850040034445 2904005588242818765012917)
                ·
                  refine ⟨272250523897764259219961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2904005588242818765012917 272250523897764259219961)
                  ·
                    rfl

theorem cell23_4771854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_4771854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771854 prefixEnd_4771854 := by exact prefixLift 4771854
  have htrace : WordTrace (prefixWord ++ tailWord_4771854) baseStart_4771854 baseEnd_4771854 := by
    simpa [prefixWord, tailWord_4771854, baseEnd_4771854] using wordTrace_append hprefix tailTrace_4771854
  have hstable : (prefixWord ++ tailWord_4771854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771854).length < 2 ^ (prefixWord ++ tailWord_4771854).sum := by decide
  have hdescent : baseEnd_4771854 < baseStart_4771854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771887 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 1, 6, 2]
def baseStart_4771887 : Nat := 118140960795 + 4771887 * 2 ^ 59
def prefixEnd_4771887 : Nat := 4983230072969 + 3 ^ 40 * 4771887 * 2
def baseEnd_4771887 : Nat := 2450271659941476703866997

theorem tailTrace_4771887 : CollatzResearch.WordTrace tailWord_4771887 prefixEnd_4771887 2450271659941476703866997 := by
  unfold tailWord_4771887
  simp only [CollatzResearch.WordTrace]
  refine ⟨174045017263275847261361915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116030011508850564840907943 174045017263275847261361915)
  ·
    refine ⟨261067525894913770892042873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174045017263275847261361915 261067525894913770892042873)
    ·
      refine ⟨195800644421185328169032155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261067525894913770892042873 195800644421185328169032155)
      ·
        refine ⟨293700966631777992253548233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195800644421185328169032155 293700966631777992253548233)
        ·
          refine ⟨220275724973833494190161175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293700966631777992253548233 220275724973833494190161175)
          ·
            refine ⟨330413587460750241285241763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220275724973833494190161175 330413587460750241285241763)
            ·
              refine ⟨495620381191125361927862645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330413587460750241285241763 495620381191125361927862645)
              ·
                refine ⟨46464410736668002680737123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 495620381191125361927862645 46464410736668002680737123)
                ·
                  refine ⟨69696616105002004021105685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46464410736668002680737123 69696616105002004021105685)
                  ·
                    refine ⟨3267028879921968938489329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69696616105002004021105685 3267028879921968938489329)
                    ·
                      refine ⟨2450271659941476703866997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267028879921968938489329 2450271659941476703866997)
                      ·
                        rfl

theorem cell23_4771887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 6, 2].length) (baseStart_4771887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771887 prefixEnd_4771887 := by exact prefixLift 4771887
  have htrace : WordTrace (prefixWord ++ tailWord_4771887) baseStart_4771887 baseEnd_4771887 := by
    simpa [prefixWord, tailWord_4771887, baseEnd_4771887] using wordTrace_append hprefix tailTrace_4771887
  have hstable : (prefixWord ++ tailWord_4771887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771887).length < 2 ^ (prefixWord ++ tailWord_4771887).sum := by decide
  have hdescent : baseEnd_4771887 < baseStart_4771887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4771982 : List Nat := [4, 1, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_4771982 : Nat := 118140960795 + 4771982 * 2 ^ 59
def prefixEnd_4771982 : Nat := 4983230072969 + 3 ^ 40 * 4771982 * 2
def baseEnd_4771982 : Nat := 816773480201217944059687

theorem tailTrace_4771982 : CollatzResearch.WordTrace tailWord_4771982 prefixEnd_4771982 816773480201217944059687 := by
  unfold tailWord_4771982
  simp only [CollatzResearch.WordTrace]
  refine ⟨21756060274741459810758775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116032321465287785657380133 21756060274741459810758775)
  ·
    refine ⟨32634090412112189716138163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21756060274741459810758775 32634090412112189716138163)
    ·
      refine ⟨48951135618168284574207245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32634090412112189716138163 48951135618168284574207245)
      ·
        refine ⟨18356675856813106715327717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48951135618168284574207245 18356675856813106715327717)
        ·
          refine ⟨3441876723152457509123947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18356675856813106715327717 3441876723152457509123947)
          ·
            refine ⟨5162815084728686263685921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441876723152457509123947 5162815084728686263685921)
            ·
              refine ⟨3872111313546514697764441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5162815084728686263685921 3872111313546514697764441)
              ·
                refine ⟨2904083485159886023323331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3872111313546514697764441 2904083485159886023323331)
                ·
                  refine ⟨4356125227739829034984997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2904083485159886023323331 4356125227739829034984997)
                  ·
                    refine ⟨816773480201217944059687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4356125227739829034984997 816773480201217944059687)
                    ·
                      rfl

theorem cell23_4771982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_4771982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4771982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4771982 prefixEnd_4771982 := by exact prefixLift 4771982
  have htrace : WordTrace (prefixWord ++ tailWord_4771982) baseStart_4771982 baseEnd_4771982 := by
    simpa [prefixWord, tailWord_4771982, baseEnd_4771982] using wordTrace_append hprefix tailTrace_4771982
  have hstable : (prefixWord ++ tailWord_4771982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4771982).length < 2 ^ (prefixWord ++ tailWord_4771982).sum := by decide
  have hdescent : baseEnd_4771982 < baseStart_4771982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4771982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772122 : List Nat := [3, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2]
def baseStart_4772122 : Nat := 118140960795 + 4772122 * 2 ^ 59
def prefixEnd_4772122 : Nat := 4983230072969 + 3 ^ 40 * 4772122 * 2
def baseEnd_4772122 : Nat := 2450392327895283284428417

theorem tailTrace_4772122 : CollatzResearch.WordTrace tailWord_4772122 prefixEnd_4772122 2450392327895283284428417 := by
  unfold tailWord_4772122
  simp only [CollatzResearch.WordTrace]
  refine ⟨43513397104356120599041655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116035725611616321597444413 43513397104356120599041655)
  ·
    refine ⟨65270095656534180898562483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43513397104356120599041655 65270095656534180898562483)
    ·
      refine ⟨97905143484801271347843725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65270095656534180898562483 97905143484801271347843725)
      ·
        refine ⟨36714428806800476755441397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97905143484801271347843725 36714428806800476755441397)
        ·
          refine ⟨3441977700637544695822631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36714428806800476755441397 3441977700637544695822631)
          ·
            refine ⟨5162966550956317043733947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441977700637544695822631 5162966550956317043733947)
            ·
              refine ⟨7744449826434475565600921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5162966550956317043733947 7744449826434475565600921)
              ·
                refine ⟨5808337369825856674200691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7744449826434475565600921 5808337369825856674200691)
                ·
                  refine ⟨8712506054738785011301037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5808337369825856674200691 8712506054738785011301037)
                  ·
                    refine ⟨3267189770527044379237889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8712506054738785011301037 3267189770527044379237889)
                    ·
                      refine ⟨2450392327895283284428417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267189770527044379237889 2450392327895283284428417)
                      ·
                        rfl

theorem cell23_4772122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_4772122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772122 prefixEnd_4772122 := by exact prefixLift 4772122
  have htrace : WordTrace (prefixWord ++ tailWord_4772122) baseStart_4772122 baseEnd_4772122 := by
    simpa [prefixWord, tailWord_4772122, baseEnd_4772122] using wordTrace_append hprefix tailTrace_4772122
  have hstable : (prefixWord ++ tailWord_4772122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772122).length < 2 ^ (prefixWord ++ tailWord_4772122).sum := by decide
  have hdescent : baseEnd_4772122 < baseStart_4772122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772158 : List Nat := [4, 2, 1, 2, 1, 3, 1, 4, 5]
def baseStart_4772158 : Nat := 118140960795 + 4772158 * 2 ^ 59
def prefixEnd_4772158 : Nat := 4983230072969 + 3 ^ 40 * 4772158 * 2
def baseEnd_4772158 : Nat := 272267868133205015953139

theorem tailTrace_4772158 : CollatzResearch.WordTrace tailWord_4772158 prefixEnd_4772158 272267868133205015953139 := by
  unfold tailWord_4772158
  simp only [CollatzResearch.WordTrace]
  refine ⟨21756862680661757568059641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116036600963529373696318085 21756862680661757568059641)
  ·
    refine ⟨16317647010496318176044731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21756862680661757568059641 16317647010496318176044731)
    ·
      refine ⟨24476470515744477264067097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16317647010496318176044731 24476470515744477264067097)
      ·
        refine ⟨18357352886808357948050323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24476470515744477264067097 18357352886808357948050323)
        ·
          refine ⟨27536029330212536922075485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18357352886808357948050323 27536029330212536922075485)
          ·
            refine ⟨10326010998829701345778307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27536029330212536922075485 10326010998829701345778307)
            ·
              refine ⟨15489016498244552018667461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10326010998829701345778307 15489016498244552018667461)
              ·
                refine ⟨2904190593420853503500149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15489016498244552018667461 2904190593420853503500149)
                ·
                  refine ⟨272267868133205015953139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2904190593420853503500149 272267868133205015953139)
                  ·
                    rfl

theorem cell23_4772158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_4772158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772158 prefixEnd_4772158 := by exact prefixLift 4772158
  have htrace : WordTrace (prefixWord ++ tailWord_4772158) baseStart_4772158 baseEnd_4772158 := by
    simpa [prefixWord, tailWord_4772158, baseEnd_4772158] using wordTrace_append hprefix tailTrace_4772158
  have hstable : (prefixWord ++ tailWord_4772158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772158).length < 2 ^ (prefixWord ++ tailWord_4772158).sum := by decide
  have hdescent : baseEnd_4772158 < baseStart_4772158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772188 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 1, 7]
def baseStart_4772188 : Nat := 118140960795 + 4772188 * 2 ^ 59
def prefixEnd_4772188 : Nat := 4983230072969 + 3 ^ 40 * 4772188 * 2
def baseEnd_4772188 : Nat := 816808739206160008734371

theorem tailTrace_4772188 : CollatzResearch.WordTrace tailWord_4772188 prefixEnd_4772188 816808739206160008734371 := by
  unfold tailWord_4772188
  simp only [CollatzResearch.WordTrace]
  refine ⟨87027997817592687834034609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116037330423456917112046145 87027997817592687834034609)
  ·
    refine ⟨65270998363194515875525957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87027997817592687834034609 65270998363194515875525957)
    ·
      refine ⟨12238312193098971726661117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65270998363194515875525957 12238312193098971726661117)
      ·
        refine ⟨4589367072412114397497919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12238312193098971726661117 4589367072412114397497919)
        ·
          refine ⟨6884050608618171596246879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4589367072412114397497919 6884050608618171596246879)
          ·
            refine ⟨10326075912927257394370319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6884050608618171596246879 10326075912927257394370319)
            ·
              refine ⟨15489113869390886091555479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10326075912927257394370319 15489113869390886091555479)
              ·
                refine ⟨23233670804086329137333219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15489113869390886091555479 23233670804086329137333219)
                ·
                  refine ⟨34850506206129493705999829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23233670804086329137333219 34850506206129493705999829)
                  ·
                    refine ⟨816808739206160008734371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34850506206129493705999829 816808739206160008734371)
                    ·
                      rfl

theorem cell23_4772188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_4772188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772188 prefixEnd_4772188 := by exact prefixLift 4772188
  have htrace : WordTrace (prefixWord ++ tailWord_4772188) baseStart_4772188 baseEnd_4772188 := by
    simpa [prefixWord, tailWord_4772188, baseEnd_4772188] using wordTrace_append hprefix tailTrace_4772188
  have hstable : (prefixWord ++ tailWord_4772188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772188).length < 2 ^ (prefixWord ++ tailWord_4772188).sum := by decide
  have hdescent : baseEnd_4772188 < baseStart_4772188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772190 : List Nat := [4, 4, 2, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_4772190 : Nat := 118140960795 + 4772190 * 2 ^ 59
def prefixEnd_4772190 : Nat := 4983230072969 + 3 ^ 40 * 4772190 * 2
def baseEnd_4772190 : Nat := 2450427244579789018378105

theorem tailTrace_4772190 : CollatzResearch.WordTrace tailWord_4772190 prefixEnd_4772190 2450427244579789018378105 := by
  unfold tailWord_4772190
  simp only [CollatzResearch.WordTrace]
  refine ⟨21757008572647266251205253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116037379054118753339761349 21757008572647266251205253)
  ·
    refine ⟨4079439107371362422100985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21757008572647266251205253 4079439107371362422100985)
    ·
      refine ⟨3059579330528521816575739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4079439107371362422100985 3059579330528521816575739)
      ·
        refine ⟨4589368995792782724863609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3059579330528521816575739 4589368995792782724863609)
        ·
          refine ⟨3442026746844587043647707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4589368995792782724863609 3442026746844587043647707)
          ·
            refine ⟨5163040120266880565471561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442026746844587043647707 5163040120266880565471561)
            ·
              refine ⟨3872280090200160424103671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5163040120266880565471561 3872280090200160424103671)
              ·
                refine ⟨5808420135300240636155507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3872280090200160424103671 5808420135300240636155507)
                ·
                  refine ⟨8712630202950360954233261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5808420135300240636155507 8712630202950360954233261)
                  ·
                    refine ⟨3267236326106385357837473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8712630202950360954233261 3267236326106385357837473)
                    ·
                      refine ⟨2450427244579789018378105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267236326106385357837473 2450427244579789018378105)
                      ·
                        rfl

theorem cell23_4772190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_4772190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772190 prefixEnd_4772190 := by exact prefixLift 4772190
  have htrace : WordTrace (prefixWord ++ tailWord_4772190) baseStart_4772190 baseEnd_4772190 := by
    simpa [prefixWord, tailWord_4772190, baseEnd_4772190] using wordTrace_append hprefix tailTrace_4772190
  have hstable : (prefixWord ++ tailWord_4772190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772190).length < 2 ^ (prefixWord ++ tailWord_4772190).sum := by decide
  have hdescent : baseEnd_4772190 < baseStart_4772190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772191 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 4]
def baseStart_4772191 : Nat := 118140960795 + 4772191 * 2 ^ 59
def prefixEnd_4772191 : Nat := 4983230072969 + 3 ^ 40 * 4772191 * 2
def baseEnd_4772191 : Nat := 2450427758060443514465599

theorem tailTrace_4772191 : CollatzResearch.WordTrace tailWord_4772191 prefixEnd_4772191 2450427758060443514465599 := by
  unfold tailWord_4772191
  simp only [CollatzResearch.WordTrace]
  refine ⟨174056105054174507180428427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116037403369449671453618951 174056105054174507180428427)
  ·
    refine ⟨261084157581261760770642641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174056105054174507180428427 261084157581261760770642641)
    ·
      refine ⟨195813118185946320577981981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261084157581261760770642641 195813118185946320577981981)
      ·
        refine ⟨73429919319729870216743243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195813118185946320577981981 73429919319729870216743243)
        ·
          refine ⟨110144878979594805325114865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73429919319729870216743243 110144878979594805325114865)
          ·
            refine ⟨82608659234696103993836149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110144878979594805325114865 82608659234696103993836149)
            ·
              refine ⟨7744561803252759749422139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82608659234696103993836149 7744561803252759749422139)
              ·
                refine ⟨11616842704879139624133209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7744561803252759749422139 11616842704879139624133209)
                ·
                  refine ⟨8712632028659354718099907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11616842704879139624133209 8712632028659354718099907)
                  ·
                    refine ⟨13068948042989032077149861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8712632028659354718099907 13068948042989032077149861)
                    ·
                      refine ⟨2450427758060443514465599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13068948042989032077149861 2450427758060443514465599)
                      ·
                        rfl

theorem cell23_4772191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_4772191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772191 prefixEnd_4772191 := by exact prefixLift 4772191
  have htrace : WordTrace (prefixWord ++ tailWord_4772191) baseStart_4772191 baseEnd_4772191 := by
    simpa [prefixWord, tailWord_4772191, baseEnd_4772191] using wordTrace_append hprefix tailTrace_4772191
  have hstable : (prefixWord ++ tailWord_4772191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772191).length < 2 ^ (prefixWord ++ tailWord_4772191).sum := by decide
  have hdescent : baseEnd_4772191 < baseStart_4772191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772261 : List Nat := [1, 3, 1, 2, 1, 1, 3, 5, 1, 5]
def baseStart_4772261 : Nat := 118140960795 + 4772261 * 2 ^ 59
def prefixEnd_4772261 : Nat := 4983230072969 + 3 ^ 40 * 4772261 * 2
def baseEnd_4772261 : Nat := 816821233902086080196759

theorem tailTrace_4772261 : CollatzResearch.WordTrace tailWord_4772261 prefixEnd_4772261 816821233902086080196759 := by
  unfold tailWord_4772261
  simp only [CollatzResearch.WordTrace]
  refine ⟨174058658163920909135476637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116039105442613939423651091 174058658163920909135476637)
  ·
    refine ⟨65271996811470340925803739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174058658163920909135476637 65271996811470340925803739)
    ·
      refine ⟨97907995217205511388705609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65271996811470340925803739 97907995217205511388705609)
      ·
        refine ⟨73430996412904133541529207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97907995217205511388705609 73430996412904133541529207)
        ·
          refine ⟨110146494619356200312293811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73430996412904133541529207 110146494619356200312293811)
          ·
            refine ⟨165219741929034300468440717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110146494619356200312293811 165219741929034300468440717)
            ·
              refine ⟨61957403223387862675665269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165219741929034300468440717 61957403223387862675665269)
              ·
                refine ⟨5808506552192612125843619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61957403223387862675665269 5808506552192612125843619)
                ·
                  refine ⟨8712759828288918188765429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5808506552192612125843619 8712759828288918188765429)
                  ·
                    refine ⟨816821233902086080196759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8712759828288918188765429 816821233902086080196759)
                    ·
                      rfl

theorem cell23_4772261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_4772261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772261 prefixEnd_4772261 := by exact prefixLift 4772261
  have htrace : WordTrace (prefixWord ++ tailWord_4772261) baseStart_4772261 baseEnd_4772261 := by
    simpa [prefixWord, tailWord_4772261, baseEnd_4772261] using wordTrace_append hprefix tailTrace_4772261
  have hstable : (prefixWord ++ tailWord_4772261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772261).length < 2 ^ (prefixWord ++ tailWord_4772261).sum := by decide
  have hdescent : baseEnd_4772261 < baseStart_4772261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772269 : List Nat := [1, 5, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_4772269 : Nat := 118140960795 + 4772269 * 2 ^ 59
def prefixEnd_4772269 : Nat := 4983230072969 + 3 ^ 40 * 4772269 * 2
def baseEnd_4772269 : Nat := 816822603183831403096747

theorem tailTrace_4772269 : CollatzResearch.WordTrace tailWord_4772269 prefixEnd_4772269 816822603183831403096747 := by
  unfold tailWord_4772269
  simp only [CollatzResearch.WordTrace]
  refine ⟨174058949947891926501767861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116039299965261284334511907 174058949947891926501767861)
  ·
    refine ⟨16318026557614868109540737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174058949947891926501767861 16318026557614868109540737)
    ·
      refine ⟨12238519918211151082155553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16318026557614868109540737 12238519918211151082155553)
      ·
        refine ⟨9178889938658363311616665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12238519918211151082155553 9178889938658363311616665)
        ·
          refine ⟨6884167453993772483712499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9178889938658363311616665 6884167453993772483712499)
          ·
            refine ⟨10326251180990658725568749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6884167453993772483712499 10326251180990658725568749)
            ·
              refine ⟨3872344192871497022088281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10326251180990658725568749 3872344192871497022088281)
              ·
                refine ⟨2904258144653622766566211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3872344192871497022088281 2904258144653622766566211)
                ·
                  refine ⟨4356387216980434149849317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2904258144653622766566211 4356387216980434149849317)
                  ·
                    refine ⟨816822603183831403096747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4356387216980434149849317 816822603183831403096747)
                    ·
                      rfl

theorem cell23_4772269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_4772269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772269 prefixEnd_4772269 := by exact prefixLift 4772269
  have htrace : WordTrace (prefixWord ++ tailWord_4772269) baseStart_4772269 baseEnd_4772269 := by
    simpa [prefixWord, tailWord_4772269, baseEnd_4772269] using wordTrace_append hprefix tailTrace_4772269
  have hstable : (prefixWord ++ tailWord_4772269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772269).length < 2 ^ (prefixWord ++ tailWord_4772269).sum := by decide
  have hdescent : baseEnd_4772269 < baseStart_4772269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772308 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_4772308 : Nat := 118140960795 + 4772308 * 2 ^ 59
def prefixEnd_4772308 : Nat := 4983230072969 + 3 ^ 40 * 4772308 * 2
def baseEnd_4772308 : Nat := 816829278432339852234187

theorem tailTrace_4772308 : CollatzResearch.WordTrace tailWord_4772308 prefixEnd_4772308 816829278432339852234187 := by
  unfold tailWord_4772308
  simp only [CollatzResearch.WordTrace]
  refine ⟨87030186197375318081218789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116040248263167090774958385 87030186197375318081218789)
  ·
    refine ⟨16318159912007872140228523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87030186197375318081218789 16318159912007872140228523)
    ·
      refine ⟨24477239868011808210342785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16318159912007872140228523 24477239868011808210342785)
      ·
        refine ⟨18357929901008856157757089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24477239868011808210342785 18357929901008856157757089)
        ·
          refine ⟨13768447425756642118317817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18357929901008856157757089 13768447425756642118317817)
          ·
            refine ⟨10326335569317481588738363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13768447425756642118317817 10326335569317481588738363)
            ·
              refine ⟨15489503353976222383107545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10326335569317481588738363 15489503353976222383107545)
              ·
                refine ⟨11617127515482166787330659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15489503353976222383107545 11617127515482166787330659)
                ·
                  refine ⟨17425691273223250180995989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11617127515482166787330659 17425691273223250180995989)
                  ·
                    refine ⟨816829278432339852234187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17425691273223250180995989 816829278432339852234187)
                    ·
                      rfl

theorem cell23_4772308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_4772308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772308 prefixEnd_4772308 := by exact prefixLift 4772308
  have htrace : WordTrace (prefixWord ++ tailWord_4772308) baseStart_4772308 baseEnd_4772308 := by
    simpa [prefixWord, tailWord_4772308, baseEnd_4772308] using wordTrace_append hprefix tailTrace_4772308
  have hstable : (prefixWord ++ tailWord_4772308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772308).length < 2 ^ (prefixWord ++ tailWord_4772308).sum := by decide
  have hdescent : baseEnd_4772308 < baseStart_4772308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772331 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 3]
def baseStart_4772331 : Nat := 118140960795 + 4772331 * 2 ^ 59
def prefixEnd_4772331 : Nat := 4983230072969 + 3 ^ 40 * 4772331 * 2
def baseEnd_4772331 : Nat := 2450499645352072966714955

theorem tailTrace_4772331 : CollatzResearch.WordTrace tailWord_4772331 prefixEnd_4772331 2450499645352072966714955 := by
  unfold tailWord_4772331
  simp only [CollatzResearch.WordTrace]
  refine ⟨174061211273667311090524847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116040807515778207393683231 174061211273667311090524847)
  ·
    refine ⟨261091816910500966635787271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174061211273667311090524847 261091816910500966635787271)
    ·
      refine ⟨391637725365751449953680907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261091816910500966635787271 391637725365751449953680907)
      ·
        refine ⟨587456588048627174930521361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391637725365751449953680907 587456588048627174930521361)
        ·
          refine ⟨440592441036470381197891021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587456588048627174930521361 440592441036470381197891021)
          ·
            refine ⟨165222165388676392949209133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 440592441036470381197891021 165222165388676392949209133)
            ·
              refine ⟨61958312020753647355953425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165222165388676392949209133 61958312020753647355953425)
              ·
                refine ⟨46468734015565235516965069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61958312020753647355953425 46468734015565235516965069)
                ·
                  refine ⟨17425775255836963318861901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46468734015565235516965069 17425775255836963318861901)
                  ·
                    refine ⟨6534665720938861244573213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17425775255836963318861901 6534665720938861244573213)
                    ·
                      refine ⟨2450499645352072966714955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6534665720938861244573213 2450499645352072966714955)
                      ·
                        rfl

theorem cell23_4772331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 3].length) (baseStart_4772331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772331 prefixEnd_4772331 := by exact prefixLift 4772331
  have htrace : WordTrace (prefixWord ++ tailWord_4772331) baseStart_4772331 baseEnd_4772331 := by
    simpa [prefixWord, tailWord_4772331, baseEnd_4772331] using wordTrace_append hprefix tailTrace_4772331
  have hstable : (prefixWord ++ tailWord_4772331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772331).length < 2 ^ (prefixWord ++ tailWord_4772331).sum := by decide
  have hdescent : baseEnd_4772331 < baseStart_4772331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772332 : List Nat := [2, 2, 1, 1, 2, 1, 5, 4, 1, 2, 2]
def baseStart_4772332 : Nat := 118140960795 + 4772332 * 2 ^ 59
def prefixEnd_4772332 : Nat := 4983230072969 + 3 ^ 40 * 4772332 * 2
def baseEnd_4772332 : Nat := 2450500158832727462802451

theorem tailTrace_4772332 : CollatzResearch.WordTrace tailWord_4772332 prefixEnd_4772332 2450500158832727462802451 := by
  unfold tailWord_4772332
  simp only [CollatzResearch.WordTrace]
  refine ⟨87030623873331844130655625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116040831831109125507540833 87030623873331844130655625)
  ·
    refine ⟨65272967904998883097991719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87030623873331844130655625 65272967904998883097991719)
    ·
      refine ⟨97909451857498324646987579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65272967904998883097991719 97909451857498324646987579)
      ·
        refine ⟨146864177786247486970481369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97909451857498324646987579 146864177786247486970481369)
        ·
          refine ⟨110148133339685615227861027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146864177786247486970481369 110148133339685615227861027)
          ·
            refine ⟨165222200009528422841791541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110148133339685615227861027 165222200009528422841791541)
            ·
              refine ⟨15489581250893289641417957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165222200009528422841791541 15489581250893289641417957)
              ·
                refine ⟨2904296484542491807765867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15489581250893289641417957 2904296484542491807765867)
                ·
                  refine ⟨4356444726813737711648801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2904296484542491807765867 4356444726813737711648801)
                  ·
                    refine ⟨3267333545110303283736601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4356444726813737711648801 3267333545110303283736601)
                    ·
                      refine ⟨2450500158832727462802451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267333545110303283736601 2450500158832727462802451)
                      ·
                        rfl

theorem cell23_4772332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 1, 2, 2].length) (baseStart_4772332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772332 prefixEnd_4772332 := by exact prefixLift 4772332
  have htrace : WordTrace (prefixWord ++ tailWord_4772332) baseStart_4772332 baseEnd_4772332 := by
    simpa [prefixWord, tailWord_4772332, baseEnd_4772332] using wordTrace_append hprefix tailTrace_4772332
  have hstable : (prefixWord ++ tailWord_4772332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772332).length < 2 ^ (prefixWord ++ tailWord_4772332).sum := by decide
  have hdescent : baseEnd_4772332 < baseStart_4772332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772348 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_4772348 : Nat := 118140960795 + 4772348 * 2 ^ 59
def prefixEnd_4772348 : Nat := 4983230072969 + 3 ^ 40 * 4772348 * 2
def baseEnd_4772348 : Nat := 2450508374523199400202377

theorem tailTrace_4772348 : CollatzResearch.WordTrace tailWord_4772348 prefixEnd_4772348 2450508374523199400202377 := by
  unfold tailWord_4772348
  simp only [CollatzResearch.WordTrace]
  refine ⟨87030915657302861496946849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116041220876403815329262465 87030915657302861496946849)
  ·
    refine ⟨65273186742977146122710137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87030915657302861496946849 65273186742977146122710137)
    ·
      refine ⟨48954890057232859592032603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65273186742977146122710137 48954890057232859592032603)
      ·
        refine ⟨73432335085849289388048905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48954890057232859592032603 73432335085849289388048905)
        ·
          refine ⟨55074251314386967041036679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73432335085849289388048905 55074251314386967041036679)
          ·
            refine ⟨82611376971580450561555019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55074251314386967041036679 82611376971580450561555019)
            ·
              refine ⟨123917065457370675842332529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82611376971580450561555019 123917065457370675842332529)
              ·
                refine ⟨92937799093028006881749397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123917065457370675842332529 92937799093028006881749397)
                ·
                  refine ⟨4356459332485687822582003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92937799093028006881749397 4356459332485687822582003)
                  ·
                    refine ⟨6534688998728531733873005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4356459332485687822582003 6534688998728531733873005)
                    ·
                      refine ⟨2450508374523199400202377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6534688998728531733873005 2450508374523199400202377)
                      ·
                        rfl

theorem cell23_4772348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_4772348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772348 prefixEnd_4772348 := by exact prefixLift 4772348
  have htrace : WordTrace (prefixWord ++ tailWord_4772348) baseStart_4772348 baseEnd_4772348 := by
    simpa [prefixWord, tailWord_4772348, baseEnd_4772348] using wordTrace_append hprefix tailTrace_4772348
  have hstable : (prefixWord ++ tailWord_4772348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772348).length < 2 ^ (prefixWord ++ tailWord_4772348).sum := by decide
  have hdescent : baseEnd_4772348 < baseStart_4772348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772458 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 4, 5]
def baseStart_4772458 : Nat := 118140960795 + 4772458 * 2 ^ 59
def prefixEnd_4772458 : Nat := 4983230072969 + 3 ^ 40 * 4772458 * 2
def baseEnd_4772458 : Nat := 816854952465064656608957

theorem tailTrace_4772458 : CollatzResearch.WordTrace tailWord_4772458 prefixEnd_4772458 816854952465064656608957 := by
  unfold tailWord_4772458
  simp only [CollatzResearch.WordTrace]
  refine ⟨43516460836051802945099507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116043895562804807853598685 43516460836051802945099507)
  ·
    refine ⟨65274691254077704417649261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43516460836051802945099507 65274691254077704417649261)
    ·
      refine ⟨24478009220279139156618473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65274691254077704417649261 24478009220279139156618473)
      ·
        refine ⟨18358506915209354367463855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24478009220279139156618473 18358506915209354367463855)
        ·
          refine ⟨27537760372814031551195783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18358506915209354367463855 27537760372814031551195783)
          ·
            refine ⟨41306640559221047326793675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27537760372814031551195783 41306640559221047326793675)
            ·
              refine ⟨61959960838831570990190513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41306640559221047326793675 61959960838831570990190513)
              ·
                refine ⟨46469970629123678242642885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61959960838831570990190513 46469970629123678242642885)
                ·
                  refine ⟨8713119492960689670495541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46469970629123678242642885 8713119492960689670495541)
                  ·
                    refine ⟨816854952465064656608957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8713119492960689670495541 816854952465064656608957)
                    ·
                      rfl

theorem cell23_4772458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_4772458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772458 prefixEnd_4772458 := by exact prefixLift 4772458
  have htrace : WordTrace (prefixWord ++ tailWord_4772458) baseStart_4772458 baseEnd_4772458 := by
    simpa [prefixWord, tailWord_4772458, baseEnd_4772458] using wordTrace_append hprefix tailTrace_4772458
  have hstable : (prefixWord ++ tailWord_4772458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772458).length < 2 ^ (prefixWord ++ tailWord_4772458).sum := by decide
  have hdescent : baseEnd_4772458 < baseStart_4772458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772471 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 2, 8]
def baseStart_4772471 : Nat := 118140960795 + 4772471 * 2 ^ 59
def prefixEnd_4772471 : Nat := 4983230072969 + 3 ^ 40 * 4772471 * 2
def baseEnd_4772471 : Nat := 816857177547900806321437

theorem tailTrace_4772471 : CollatzResearch.WordTrace tailWord_4772471 prefixEnd_4772471 816857177547900806321437 := by
  unfold tailWord_4772471
  simp only [CollatzResearch.WordTrace]
  refine ⟨174066317493160115000621267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116044211662106743333747511 174066317493160115000621267)
  ·
    refine ⟨261099476239740172500931901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174066317493160115000621267 261099476239740172500931901)
    ·
      refine ⟨97912303589902564687849463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261099476239740172500931901 97912303589902564687849463)
      ·
        refine ⟨146868455384853847031774195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97912303589902564687849463 146868455384853847031774195)
        ·
          refine ⟨220302683077280770547661293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146868455384853847031774195 220302683077280770547661293)
          ·
            refine ⟨82613506153980288955372985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220302683077280770547661293 82613506153980288955372985)
            ·
              refine ⟨61960129615485216716529739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82613506153980288955372985 61960129615485216716529739)
              ·
                refine ⟨92940194423227825074794609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61960129615485216716529739 92940194423227825074794609)
                ·
                  refine ⟨69705145817420868806095957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92940194423227825074794609 69705145817420868806095957)
                  ·
                    refine ⟨816857177547900806321437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69705145817420868806095957 816857177547900806321437)
                    ·
                      rfl

theorem cell23_4772471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_4772471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772471 prefixEnd_4772471 := by exact prefixLift 4772471
  have htrace : WordTrace (prefixWord ++ tailWord_4772471) baseStart_4772471 baseEnd_4772471 := by
    simpa [prefixWord, tailWord_4772471, baseEnd_4772471] using wordTrace_append hprefix tailTrace_4772471
  have hstable : (prefixWord ++ tailWord_4772471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772471).length < 2 ^ (prefixWord ++ tailWord_4772471).sum := by decide
  have hdescent : baseEnd_4772471 < baseStart_4772471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772512 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 2, 4, 2]
def baseStart_4772512 : Nat := 118140960795 + 4772512 * 2 ^ 59
def prefixEnd_4772512 : Nat := 4983230072969 + 3 ^ 40 * 4772512 * 2
def baseEnd_4772512 : Nat := 2450592585350536758551623

theorem tailTrace_4772512 : CollatzResearch.WordTrace tailWord_4772512 prefixEnd_4772512 2450592585350536758551623 := by
  unfold tailWord_4772512
  simp only [CollatzResearch.WordTrace]
  refine ⟨87033906443005789501431895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116045208590674386001909193 87033906443005789501431895)
  ·
    refine ⟨130550859664508684252147843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87033906443005789501431895 130550859664508684252147843)
    ·
      refine ⟨195826289496763026378221765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130550859664508684252147843 195826289496763026378221765)
      ·
        refine ⟨36717429280643067445916581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195826289496763026378221765 36717429280643067445916581)
        ·
          refine ⟨6884517990120575146109359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36717429280643067445916581 6884517990120575146109359)
          ·
            refine ⟨10326776985180862719164039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6884517990120575146109359 10326776985180862719164039)
            ·
              refine ⟨15490165477771294078746059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10326776985180862719164039 15490165477771294078746059)
              ·
                refine ⟨23235248216656941118119089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15490165477771294078746059 23235248216656941118119089)
                ·
                  refine ⟨17426436162492705838589317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23235248216656941118119089 17426436162492705838589317)
                  ·
                    refine ⟨3267456780467382344735497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17426436162492705838589317 3267456780467382344735497)
                    ·
                      refine ⟨2450592585350536758551623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267456780467382344735497 2450592585350536758551623)
                      ·
                        rfl

theorem cell23_4772512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_4772512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772512 prefixEnd_4772512 := by exact prefixLift 4772512
  have htrace : WordTrace (prefixWord ++ tailWord_4772512) baseStart_4772512 baseEnd_4772512 := by
    simpa [prefixWord, tailWord_4772512, baseEnd_4772512] using wordTrace_append hprefix tailTrace_4772512
  have hstable : (prefixWord ++ tailWord_4772512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772512).length < 2 ^ (prefixWord ++ tailWord_4772512).sum := by decide
  have hdescent : baseEnd_4772512 < baseStart_4772512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772529 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 2, 1, 4]
def baseStart_4772529 : Nat := 118140960795 + 4772529 * 2 ^ 59
def prefixEnd_4772529 : Nat := 4983230072969 + 3 ^ 40 * 4772529 * 2
def baseEnd_4772529 : Nat := 2450601314521663192039045

theorem tailTrace_4772529 : CollatzResearch.WordTrace tailWord_4772529 prefixEnd_4772529 2450601314521663192039045 := by
  unfold tailWord_4772529
  simp only [CollatzResearch.WordTrace]
  refine ⟨174068432926949990906232641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116045621951299993937488427 174068432926949990906232641)
  ·
    refine ⟨130551324695212493179674481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174068432926949990906232641 130551324695212493179674481)
    ·
      refine ⟨97913493521409369884755861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130551324695212493179674481 97913493521409369884755861)
      ·
        refine ⟨4589695008816064213347931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 97913493521409369884755861 4589695008816064213347931)
        ·
          refine ⟨6884542513224096320021897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4589695008816064213347931 6884542513224096320021897)
          ·
            refine ⟨5163406884918072240016423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6884542513224096320021897 5163406884918072240016423)
            ·
              refine ⟨7745110327377108360024635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5163406884918072240016423 7745110327377108360024635)
              ·
                refine ⟨11617665491065662540036953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7745110327377108360024635 11617665491065662540036953)
                ·
                  refine ⟨8713249118299246905027715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11617665491065662540036953 8713249118299246905027715)
                  ·
                    refine ⟨13069873677448870357541573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8713249118299246905027715 13069873677448870357541573)
                    ·
                      refine ⟨2450601314521663192039045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13069873677448870357541573 2450601314521663192039045)
                      ·
                        rfl

theorem cell23_4772529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_4772529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772529 prefixEnd_4772529 := by exact prefixLift 4772529
  have htrace : WordTrace (prefixWord ++ tailWord_4772529) baseStart_4772529 baseEnd_4772529 := by
    simpa [prefixWord, tailWord_4772529, baseEnd_4772529] using wordTrace_append hprefix tailTrace_4772529
  have hstable : (prefixWord ++ tailWord_4772529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772529).length < 2 ^ (prefixWord ++ tailWord_4772529).sum := by decide
  have hdescent : baseEnd_4772529 < baseStart_4772529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772585 : List Nat := [1, 2, 1, 1, 1, 2, 5, 4, 1, 1, 4]
def baseStart_4772585 : Nat := 118140960795 + 4772585 * 2 ^ 59
def prefixEnd_4772585 : Nat := 4983230072969 + 3 ^ 40 * 4772585 * 2
def baseEnd_4772585 : Nat := 2450630069438314972938787

theorem tailTrace_4772585 : CollatzResearch.WordTrace tailWord_4772585 prefixEnd_4772585 2450630069438314972938787 := by
  unfold tailWord_4772585
  simp only [CollatzResearch.WordTrace]
  refine ⟨174070475414747112470271209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116046983609831408313514139 174070475414747112470271209)
  ·
    refine ⟨130552856561060334352703407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174070475414747112470271209 130552856561060334352703407)
    ·
      refine ⟨195829284841590501529055111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130552856561060334352703407 195829284841590501529055111)
      ·
        refine ⟨293743927262385752293582667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195829284841590501529055111 293743927262385752293582667)
        ·
          refine ⟨440615890893578628440374001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293743927262385752293582667 440615890893578628440374001)
          ·
            refine ⟨330461918170183971330280501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440615890893578628440374001 330461918170183971330280501)
            ·
              refine ⟨30980804828454747312213797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 330461918170183971330280501 30980804828454747312213797)
              ·
                refine ⟨5808900905335265121040087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30980804828454747312213797 5808900905335265121040087)
                ·
                  refine ⟨8713351358002897681560131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5808900905335265121040087 8713351358002897681560131)
                  ·
                    refine ⟨13070027037004346522340197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8713351358002897681560131 13070027037004346522340197)
                    ·
                      refine ⟨2450630069438314972938787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13070027037004346522340197 2450630069438314972938787)
                      ·
                        rfl

theorem cell23_4772585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 1, 4].length) (baseStart_4772585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772585 prefixEnd_4772585 := by exact prefixLift 4772585
  have htrace : WordTrace (prefixWord ++ tailWord_4772585) baseStart_4772585 baseEnd_4772585 := by
    simpa [prefixWord, tailWord_4772585, baseEnd_4772585] using wordTrace_append hprefix tailTrace_4772585
  have hstable : (prefixWord ++ tailWord_4772585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772585).length < 2 ^ (prefixWord ++ tailWord_4772585).sum := by decide
  have hdescent : baseEnd_4772585 < baseStart_4772585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772588 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_4772588 : Nat := 118140960795 + 4772588 * 2 ^ 59
def prefixEnd_4772588 : Nat := 4983230072969 + 3 ^ 40 * 4772588 * 2
def baseEnd_4772588 : Nat := 2450631609880278461201273

theorem tailTrace_4772588 : CollatzResearch.WordTrace tailWord_4772588 prefixEnd_4772588 2450631609880278461201273 := by
  unfold tailWord_4772588
  simp only [CollatzResearch.WordTrace]
  refine ⟨87035292416868121991315209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116047056555824162655086945 87035292416868121991315209)
  ·
    refine ⟨65276469312651091493486407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87035292416868121991315209 65276469312651091493486407)
    ·
      refine ⟨97914703968976637240229611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65276469312651091493486407 97914703968976637240229611)
      ·
        refine ⟨146872055953464955860344417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97914703968976637240229611 146872055953464955860344417)
        ·
          refine ⟨110154041965098716895258313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146872055953464955860344417 110154041965098716895258313)
          ·
            refine ⟨82615531473824037671443735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110154041965098716895258313 82615531473824037671443735)
            ·
              refine ⟨123923297210736056507165603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82615531473824037671443735 123923297210736056507165603)
              ·
                refine ⟨185884945816104084760748405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123923297210736056507165603 185884945816104084760748405)
                ·
                  refine ⟨17426713670259757946320163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 185884945816104084760748405 17426713670259757946320163)
                  ·
                    refine ⟨26140070505389636919480245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17426713670259757946320163 26140070505389636919480245)
                    ·
                      refine ⟨2450631609880278461201273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26140070505389636919480245 2450631609880278461201273)
                      ·
                        rfl

theorem cell23_4772588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_4772588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772588 prefixEnd_4772588 := by exact prefixLift 4772588
  have htrace : WordTrace (prefixWord ++ tailWord_4772588) baseStart_4772588 baseEnd_4772588 := by
    simpa [prefixWord, tailWord_4772588, baseEnd_4772588] using wordTrace_append hprefix tailTrace_4772588
  have hstable : (prefixWord ++ tailWord_4772588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772588).length < 2 ^ (prefixWord ++ tailWord_4772588).sum := by decide
  have hdescent : baseEnd_4772588 < baseStart_4772588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772602 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2]
def baseStart_4772602 : Nat := 118140960795 + 4772602 * 2 ^ 59
def prefixEnd_4772602 : Nat := 4983230072969 + 3 ^ 40 * 4772602 * 2
def baseEnd_4772602 : Nat := 2450638798609441406426209

theorem tailTrace_4772602 : CollatzResearch.WordTrace tailWord_4772602 prefixEnd_4772602 2450638798609441406426209 := by
  unfold tailWord_4772602
  simp only [CollatzResearch.WordTrace]
  refine ⟨43517773863921381093410015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116047396970457016249093373 43517773863921381093410015)
  ·
    refine ⟨65276660795882071640115023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43517773863921381093410015 65276660795882071640115023)
    ·
      refine ⟨97914991193823107460172535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65276660795882071640115023 97914991193823107460172535)
      ·
        refine ⟨146872486790734661190258803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97914991193823107460172535 146872486790734661190258803)
        ·
          refine ⟨220308730186101991785388205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146872486790734661190258803 220308730186101991785388205)
          ·
            refine ⟨82615773819788246919520577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220308730186101991785388205 82615773819788246919520577)
            ·
              refine ⟨61961830364841185189640433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82615773819788246919520577 61961830364841185189640433)
              ·
                refine ⟨46471372773630888892230325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61961830364841185189640433 46471372773630888892230325)
                ·
                  refine ⟨4356691197527895833646593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46471372773630888892230325 4356691197527895833646593)
                  ·
                    refine ⟨3267518398145921875234945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4356691197527895833646593 3267518398145921875234945)
                    ·
                      refine ⟨2450638798609441406426209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267518398145921875234945 2450638798609441406426209)
                      ·
                        rfl

theorem cell23_4772602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2].length) (baseStart_4772602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772602 prefixEnd_4772602 := by exact prefixLift 4772602
  have htrace : WordTrace (prefixWord ++ tailWord_4772602) baseStart_4772602 baseEnd_4772602 := by
    simpa [prefixWord, tailWord_4772602, baseEnd_4772602] using wordTrace_append hprefix tailTrace_4772602
  have hstable : (prefixWord ++ tailWord_4772602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772602).length < 2 ^ (prefixWord ++ tailWord_4772602).sum := by decide
  have hdescent : baseEnd_4772602 < baseStart_4772602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772605 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_4772605 : Nat := 118140960795 + 4772605 * 2 ^ 59
def prefixEnd_4772605 : Nat := 4983230072969 + 3 ^ 40 * 4772605 * 2
def baseEnd_4772605 : Nat := 2450640339051404894688695

theorem tailTrace_4772605 : CollatzResearch.WordTrace tailWord_4772605 prefixEnd_4772605 2450640339051404894688695 := by
  unfold tailWord_4772605
  simp only [CollatzResearch.WordTrace]
  refine ⟨174071204874674655885999269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116047469916449770590666179 174071204874674655885999269)
  ·
    refine ⟨32638350914001497978624863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174071204874674655885999269 32638350914001497978624863)
    ·
      refine ⟨48957526371002246967937295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32638350914001497978624863 48957526371002246967937295)
      ·
        refine ⟨73436289556503370451905943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48957526371002246967937295 73436289556503370451905943)
        ·
          refine ⟨110154434334755055677858915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73436289556503370451905943 110154434334755055677858915)
          ·
            refine ⟨165231651502132583516788373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110154434334755055677858915 165231651502132583516788373)
            ·
              refine ⟨7745233664162464852349455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 165231651502132583516788373 7745233664162464852349455)
              ·
                refine ⟨11617850496243697278524183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7745233664162464852349455 11617850496243697278524183)
                ·
                  refine ⟨17426775744365545917786275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11617850496243697278524183 17426775744365545917786275)
                  ·
                    refine ⟨26140163616548318876679413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17426775744365545917786275 26140163616548318876679413)
                    ·
                      refine ⟨2450640339051404894688695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26140163616548318876679413 2450640339051404894688695)
                      ·
                        rfl

theorem cell23_4772605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_4772605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772605 prefixEnd_4772605 := by exact prefixLift 4772605
  have htrace : WordTrace (prefixWord ++ tailWord_4772605) baseStart_4772605 baseEnd_4772605 := by
    simpa [prefixWord, tailWord_4772605, baseEnd_4772605] using wordTrace_append hprefix tailTrace_4772605
  have hstable : (prefixWord ++ tailWord_4772605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772605).length < 2 ^ (prefixWord ++ tailWord_4772605).sum := by decide
  have hdescent : baseEnd_4772605 < baseStart_4772605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772612 : List Nat := [2, 3, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_4772612 : Nat := 118140960795 + 4772612 * 2 ^ 59
def prefixEnd_4772612 : Nat := 4983230072969 + 3 ^ 40 * 4772612 * 2
def baseEnd_4772612 : Nat := 816881311138662122433721

theorem tailTrace_4772612 : CollatzResearch.WordTrace tailWord_4772612 prefixEnd_4772612 816881311138662122433721 := by
  unfold tailWord_4772612
  simp only [CollatzResearch.WordTrace]
  refine ⟨87035730092824648040752045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116047640123766197387669393 87035730092824648040752045)
  ·
    refine ⟨32638398784809243015282017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87035730092824648040752045 32638398784809243015282017)
    ·
      refine ⟨24478799088606932261461513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32638398784809243015282017 24478799088606932261461513)
      ·
        refine ⟨18359099316455199196096135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24478799088606932261461513 18359099316455199196096135)
        ·
          refine ⟨27538648974682798794144203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18359099316455199196096135 27538648974682798794144203)
          ·
            refine ⟨41307973462024198191216305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27538648974682798794144203 41307973462024198191216305)
            ·
              refine ⟨30980980096518148643412229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41307973462024198191216305 30980980096518148643412229)
              ·
                refine ⟨5808933768097152870639793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30980980096518148643412229 5808933768097152870639793)
                ·
                  refine ⟨4356700326072864652979845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5808933768097152870639793 4356700326072864652979845)
                  ·
                    refine ⟨816881311138662122433721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4356700326072864652979845 816881311138662122433721)
                    ·
                      rfl

theorem cell23_4772612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_4772612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772612 prefixEnd_4772612 := by exact prefixLift 4772612
  have htrace : WordTrace (prefixWord ++ tailWord_4772612) baseStart_4772612 baseEnd_4772612 := by
    simpa [prefixWord, tailWord_4772612, baseEnd_4772612] using wordTrace_append hprefix tailTrace_4772612
  have hstable : (prefixWord ++ tailWord_4772612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772612).length < 2 ^ (prefixWord ++ tailWord_4772612).sum := by decide
  have hdescent : baseEnd_4772612 < baseStart_4772612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772615 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4772615 : Nat := 118140960795 + 4772615 * 2 ^ 59
def prefixEnd_4772615 : Nat := 4983230072969 + 3 ^ 40 * 4772615 * 2
def baseEnd_4772615 : Nat := 2450645473857949855563649

theorem tailTrace_4772615 : CollatzResearch.WordTrace tailWord_4772615 prefixEnd_4772615 2450645473857949855563649 := by
  unfold tailWord_4772615
  simp only [CollatzResearch.WordTrace]
  refine ⟨174071569604638427593863299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116047713069758951729242199 174071569604638427593863299)
  ·
    refine ⟨261107354406957641390794949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174071569604638427593863299 261107354406957641390794949)
    ·
      refine ⟨48957628951304557760774053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 261107354406957641390794949 48957628951304557760774053)
      ·
        refine ⟨9179555428369604580145135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48957628951304557760774053 9179555428369604580145135)
        ·
          refine ⟨13769333142554406870217703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9179555428369604580145135 13769333142554406870217703)
          ·
            refine ⟨20653999713831610305326555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13769333142554406870217703 20653999713831610305326555)
            ·
              refine ⟨30980999570747415457989833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20653999713831610305326555 30980999570747415457989833)
              ·
                refine ⟨23235749678060561593492375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30980999570747415457989833 23235749678060561593492375)
                ·
                  refine ⟨34853624517090842390238563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23235749678060561593492375 34853624517090842390238563)
                  ·
                    refine ⟨52280436775636263585357845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34853624517090842390238563 52280436775636263585357845)
                    ·
                      refine ⟨2450645473857949855563649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52280436775636263585357845 2450645473857949855563649)
                      ·
                        rfl

theorem cell23_4772615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4772615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772615 prefixEnd_4772615 := by exact prefixLift 4772615
  have htrace : WordTrace (prefixWord ++ tailWord_4772615) baseStart_4772615 baseEnd_4772615 := by
    simpa [prefixWord, tailWord_4772615, baseEnd_4772615] using wordTrace_append hprefix tailTrace_4772615
  have hstable : (prefixWord ++ tailWord_4772615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772615).length < 2 ^ (prefixWord ++ tailWord_4772615).sum := by decide
  have hdescent : baseEnd_4772615 < baseStart_4772615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772639 : List Nat := [1, 1, 2, 4, 2, 4, 1, 2, 1, 2, 3]
def baseStart_4772639 : Nat := 118140960795 + 4772639 * 2 ^ 59
def prefixEnd_4772639 : Nat := 4983230072969 + 3 ^ 40 * 4772639 * 2
def baseEnd_4772639 : Nat := 2450657797393657761663539

theorem tailTrace_4772639 : CollatzResearch.WordTrace tailWord_4772639 prefixEnd_4772639 2450657797393657761663539 := by
  unfold tailWord_4772639
  simp only [CollatzResearch.WordTrace]
  refine ⟨174072444956551479692736971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116048296637700986461824647 174072444956551479692736971)
  ·
    refine ⟨261108667434827219539105457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174072444956551479692736971 261108667434827219539105457)
    ·
      refine ⟨195831500576120414654329093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261108667434827219539105457 195831500576120414654329093)
      ·
        refine ⟨36718406358022577747686705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195831500576120414654329093 36718406358022577747686705)
        ·
          refine ⟨27538804768516933310765029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36718406358022577747686705 27538804768516933310765029)
          ·
            refine ⟨5163525894096924995768443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27538804768516933310765029 5163525894096924995768443)
            ·
              refine ⟨7745288841145387493652665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5163525894096924995768443 7745288841145387493652665)
              ·
                refine ⟨5808966630859040620239499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7745288841145387493652665 5808966630859040620239499)
                ·
                  refine ⟨8713449946288560930359249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5808966630859040620239499 8713449946288560930359249)
                  ·
                    refine ⟨6535087459716420697769437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8713449946288560930359249 6535087459716420697769437)
                    ·
                      refine ⟨2450657797393657761663539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6535087459716420697769437 2450657797393657761663539)
                      ·
                        rfl

theorem cell23_4772639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_4772639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772639 prefixEnd_4772639 := by exact prefixLift 4772639
  have htrace : WordTrace (prefixWord ++ tailWord_4772639) baseStart_4772639 baseEnd_4772639 := by
    simpa [prefixWord, tailWord_4772639, baseEnd_4772639] using wordTrace_append hprefix tailTrace_4772639
  have hstable : (prefixWord ++ tailWord_4772639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772639).length < 2 ^ (prefixWord ++ tailWord_4772639).sum := by decide
  have hdescent : baseEnd_4772639 < baseStart_4772639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772653 : List Nat := [1, 5, 3, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_4772653 : Nat := 118140960795 + 4772653 * 2 ^ 59
def prefixEnd_4772653 : Nat := 4983230072969 + 3 ^ 40 * 4772653 * 2
def baseEnd_4772653 : Nat := 2450664986122820706888475

theorem tailTrace_4772653 : CollatzResearch.WordTrace tailWord_4772653 prefixEnd_4772653 2450664986122820706888475 := by
  unfold tailWord_4772653
  simp only [CollatzResearch.WordTrace]
  refine ⟨174072955578500760083746613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116048637052333840055831075 174072955578500760083746613)
  ·
    refine ⟨16319339585484446257851245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174072955578500760083746613 16319339585484446257851245)
    ·
      refine ⟨6119752344556667346694217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16319339585484446257851245 6119752344556667346694217)
      ·
        refine ⟨4589814258417500510020663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6119752344556667346694217 4589814258417500510020663)
        ·
          refine ⟨6884721387626250765030995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4589814258417500510020663 6884721387626250765030995)
          ·
            refine ⟨10327082081439376147546493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6884721387626250765030995 10327082081439376147546493)
            ·
              refine ⟨3872655780539766055329935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10327082081439376147546493 3872655780539766055329935)
              ·
                refine ⟨5808983670809649082994903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3872655780539766055329935 5808983670809649082994903)
                ·
                  refine ⟨8713475506214473624492355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5808983670809649082994903 8713475506214473624492355)
                  ·
                    refine ⟨13070213259321710436738533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8713475506214473624492355 13070213259321710436738533)
                    ·
                      refine ⟨2450664986122820706888475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13070213259321710436738533 2450664986122820706888475)
                      ·
                        rfl

theorem cell23_4772653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_4772653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772653 prefixEnd_4772653 := by exact prefixLift 4772653
  have htrace : WordTrace (prefixWord ++ tailWord_4772653) baseStart_4772653 baseEnd_4772653 := by
    simpa [prefixWord, tailWord_4772653, baseEnd_4772653] using wordTrace_append hprefix tailTrace_4772653
  have hstable : (prefixWord ++ tailWord_4772653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772653).length < 2 ^ (prefixWord ++ tailWord_4772653).sum := by decide
  have hdescent : baseEnd_4772653 < baseStart_4772653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772676 : List Nat := [2, 3, 4, 2, 2, 1, 1, 8]
def baseStart_4772676 : Nat := 118140960795 + 4772676 * 2 ^ 59
def prefixEnd_4772676 : Nat := 4983230072969 + 3 ^ 40 * 4772676 * 2
def baseEnd_4772676 : Nat := 90765807265847189514847

theorem tailTrace_4772676 : CollatzResearch.WordTrace tailWord_4772676 prefixEnd_4772676 90765807265847189514847 := by
  unfold tailWord_4772676
  simp only [CollatzResearch.WordTrace]
  refine ⟨87036897228708717505916941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116049196304944956674555921 87036897228708717505916941)
  ·
    refine ⟨32638836460765769064718853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87036897228708717505916941 32638836460765769064718853)
    ·
      refine ⟨6119781836393581699634785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32638836460765769064718853 6119781836393581699634785)
      ·
        refine ⟨4589836377295186274726089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6119781836393581699634785 4589836377295186274726089)
        ·
          refine ⟨3442377282971389706044567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4589836377295186274726089 3442377282971389706044567)
          ·
            refine ⟨5163565924457084559066851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442377282971389706044567 5163565924457084559066851)
            ·
              refine ⟨7745348886685626838600277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5163565924457084559066851 7745348886685626838600277)
              ·
                refine ⟨90765807265847189514847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7745348886685626838600277 90765807265847189514847)
                ·
                  rfl

theorem cell23_4772676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 8].length) (baseStart_4772676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772676 prefixEnd_4772676 := by exact prefixLift 4772676
  have htrace : WordTrace (prefixWord ++ tailWord_4772676) baseStart_4772676 baseEnd_4772676 := by
    simpa [prefixWord, tailWord_4772676, baseEnd_4772676] using wordTrace_append hprefix tailTrace_4772676
  have hstable : (prefixWord ++ tailWord_4772676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772676).length < 2 ^ (prefixWord ++ tailWord_4772676).sum := by decide
  have hdescent : baseEnd_4772676 < baseStart_4772676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772743 : List Nat := [1, 1, 4, 2, 3, 2, 3, 1, 2, 2, 2]
def baseStart_4772743 : Nat := 118140960795 + 4772743 * 2 ^ 59
def prefixEnd_4772743 : Nat := 4983230072969 + 3 ^ 40 * 4772743 * 2
def baseEnd_4772743 : Nat := 2450711199381725354763061

theorem tailTrace_4772743 : CollatzResearch.WordTrace tailWord_4772743 prefixEnd_4772743 2450711199381725354763061 := by
  unfold tailWord_4772743
  simp only [CollatzResearch.WordTrace]
  refine ⟨174076238148174705454522883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116050825432116470303015255 174076238148174705454522883)
  ·
    refine ⟨261114357222262058181784325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174076238148174705454522883 261114357222262058181784325)
    ·
      refine ⟨48958941979174135909084561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 261114357222262058181784325 48958941979174135909084561)
      ·
        refine ⟨36719206484380601931813421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48958941979174135909084561 36719206484380601931813421)
        ·
          refine ⟨13769702431642725724430033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36719206484380601931813421 13769702431642725724430033)
          ·
            refine ⟨10327276823732044293322525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13769702431642725724430033 10327276823732044293322525)
            ·
              refine ⟨3872728808899516609995947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10327276823732044293322525 3872728808899516609995947)
              ·
                refine ⟨5809093213349274914993921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3872728808899516609995947 5809093213349274914993921)
                ·
                  refine ⟨4356819910011956186245441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5809093213349274914993921 4356819910011956186245441)
                  ·
                    refine ⟨3267614932508967139684081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4356819910011956186245441 3267614932508967139684081)
                    ·
                      refine ⟨2450711199381725354763061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267614932508967139684081 2450711199381725354763061)
                      ·
                        rfl

theorem cell23_4772743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_4772743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772743 prefixEnd_4772743 := by exact prefixLift 4772743
  have htrace : WordTrace (prefixWord ++ tailWord_4772743) baseStart_4772743 baseEnd_4772743 := by
    simpa [prefixWord, tailWord_4772743, baseEnd_4772743] using wordTrace_append hprefix tailTrace_4772743
  have hstable : (prefixWord ++ tailWord_4772743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772743).length < 2 ^ (prefixWord ++ tailWord_4772743).sum := by decide
  have hdescent : baseEnd_4772743 < baseStart_4772743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772745 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 1, 7]
def baseStart_4772745 : Nat := 118140960795 + 4772745 * 2 ^ 59
def prefixEnd_4772745 : Nat := 4983230072969 + 3 ^ 40 * 4772745 * 2
def baseEnd_4772745 : Nat := 816904075447678115646017

theorem tailTrace_4772745 : CollatzResearch.WordTrace tailWord_4772745 prefixEnd_4772745 816904075447678115646017 := by
  unfold tailWord_4772745
  simp only [CollatzResearch.WordTrace]
  refine ⟨174076311094167459796095689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116050874062778306530730459 174076311094167459796095689)
  ·
    refine ⟨130557233320625594847071767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174076311094167459796095689 130557233320625594847071767)
    ·
      refine ⟨195835849980938392270607651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130557233320625594847071767 195835849980938392270607651)
      ·
        refine ⟨293753774971407588405911477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195835849980938392270607651 293753774971407588405911477)
        ·
          refine ⟨27539416403569461413054201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 293753774971407588405911477 27539416403569461413054201)
          ·
            refine ⟨20654562302677096059790651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27539416403569461413054201 20654562302677096059790651)
            ·
              refine ⟨30981843454015644089685977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20654562302677096059790651 30981843454015644089685977)
              ·
                refine ⟨23236382590511733067264483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30981843454015644089685977 23236382590511733067264483)
                ·
                  refine ⟨34854573885767599600896725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23236382590511733067264483 34854573885767599600896725)
                  ·
                    refine ⟨816904075447678115646017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34854573885767599600896725 816904075447678115646017)
                    ·
                      rfl

theorem cell23_4772745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_4772745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772745 prefixEnd_4772745 := by exact prefixLift 4772745
  have htrace : WordTrace (prefixWord ++ tailWord_4772745) baseStart_4772745 baseEnd_4772745 := by
    simpa [prefixWord, tailWord_4772745, baseEnd_4772745] using wordTrace_append hprefix tailTrace_4772745
  have hstable : (prefixWord ++ tailWord_4772745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772745).length < 2 ^ (prefixWord ++ tailWord_4772745).sum := by decide
  have hdescent : baseEnd_4772745 < baseStart_4772745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772839 : List Nat := [1, 1, 5, 2, 2, 2, 2, 2, 6]
def baseStart_4772839 : Nat := 118140960795 + 4772839 * 2 ^ 59
def prefixEnd_4772839 : Nat := 4983230072969 + 3 ^ 40 * 4772839 * 2
def baseEnd_4772839 : Nat := 272306721502728553240291

theorem tailTrace_4772839 : CollatzResearch.WordTrace tailWord_4772839 prefixEnd_4772839 272306721502728553240291 := by
  unfold tailWord_4772839
  simp only [CollatzResearch.WordTrace]
  refine ⟨174079739555826913850017571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116053159703884609233345047 174079739555826913850017571)
  ·
    refine ⟨261119609333740370775026357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174079739555826913850017571 261119609333740370775026357)
    ·
      refine ⟨24479963375038159760158721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 261119609333740370775026357 24479963375038159760158721)
      ·
        refine ⟨18359972531278619820119041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24479963375038159760158721 18359972531278619820119041)
        ·
          refine ⟨13769979398458964865089281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18359972531278619820119041 13769979398458964865089281)
          ·
            refine ⟨10327484548844223648816961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13769979398458964865089281 10327484548844223648816961)
            ·
              refine ⟨7745613411633167736612721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10327484548844223648816961 7745613411633167736612721)
              ·
                refine ⟨5809210058724875802459541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7745613411633167736612721 5809210058724875802459541)
                ·
                  refine ⟨272306721502728553240291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5809210058724875802459541 272306721502728553240291)
                  ·
                    rfl

theorem cell23_4772839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 6].length) (baseStart_4772839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772839 prefixEnd_4772839 := by exact prefixLift 4772839
  have htrace : WordTrace (prefixWord ++ tailWord_4772839) baseStart_4772839 baseEnd_4772839 := by
    simpa [prefixWord, tailWord_4772839, baseEnd_4772839] using wordTrace_append hprefix tailTrace_4772839
  have hstable : (prefixWord ++ tailWord_4772839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772839).length < 2 ^ (prefixWord ++ tailWord_4772839).sum := by decide
  have hdescent : baseEnd_4772839 < baseStart_4772839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772876 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 2, 3, 2]
def baseStart_4772876 : Nat := 118140960795 + 4772876 * 2 ^ 59
def prefixEnd_4772876 : Nat := 4983230072969 + 3 ^ 40 * 4772876 * 2
def baseEnd_4772876 : Nat := 2450779492308773334399949

theorem tailTrace_4772876 : CollatzResearch.WordTrace tailWord_4772876 prefixEnd_4772876 2450779492308773334399949 := by
  unfold tailWord_4772876
  simp only [CollatzResearch.WordTrace]
  refine ⟨87040544528346434584557241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116054059371128579446076321 87040544528346434584557241)
  ·
    refine ⟨65280408396259825938417931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87040544528346434584557241 65280408396259825938417931)
    ·
      refine ⟨97920612594389738907626897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65280408396259825938417931 97920612594389738907626897)
      ·
        refine ⟨73440459445792304180720173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97920612594389738907626897 73440459445792304180720173)
        ·
          refine ⟨27540172292172114067770065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73440459445792304180720173 27540172292172114067770065)
          ·
            refine ⟨20655129219129085550827549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27540172292172114067770065 20655129219129085550827549)
            ·
              refine ⟨7745673457173407081560331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20655129219129085550827549 7745673457173407081560331)
              ·
                refine ⟨11618510185760110622340497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7745673457173407081560331 11618510185760110622340497)
                ·
                  refine ⟨8713882639320082966755373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11618510185760110622340497 8713882639320082966755373)
                  ·
                    refine ⟨3267705989745031112533265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8713882639320082966755373 3267705989745031112533265)
                    ·
                      refine ⟨2450779492308773334399949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267705989745031112533265 2450779492308773334399949)
                      ·
                        rfl

theorem cell23_4772876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_4772876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772876 prefixEnd_4772876 := by exact prefixLift 4772876
  have htrace : WordTrace (prefixWord ++ tailWord_4772876) baseStart_4772876 baseEnd_4772876 := by
    simpa [prefixWord, tailWord_4772876, baseEnd_4772876] using wordTrace_append hprefix tailTrace_4772876
  have hstable : (prefixWord ++ tailWord_4772876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772876).length < 2 ^ (prefixWord ++ tailWord_4772876).sum := by decide
  have hdescent : baseEnd_4772876 < baseStart_4772876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772899 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 4, 4]
def baseStart_4772899 : Nat := 118140960795 + 4772899 * 2 ^ 59
def prefixEnd_4772899 : Nat := 4983230072969 + 3 ^ 40 * 4772899 * 2
def baseEnd_4772899 : Nat := 816930434121275581470781

theorem tailTrace_4772899 : CollatzResearch.WordTrace tailWord_4772899 prefixEnd_4772899 816930434121275581470781 := by
  unfold tailWord_4772899
  simp only [CollatzResearch.WordTrace]
  refine ⟨174081927935609544097201751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116054618623739696064801167 174081927935609544097201751)
  ·
    refine ⟨261122891903414316145802627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174081927935609544097201751 261122891903414316145802627)
    ·
      refine ⟨391684337855121474218703941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261122891903414316145802627 391684337855121474218703941)
      ·
        refine ⟨73440813347835276416006989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 391684337855121474218703941 73440813347835276416006989)
        ·
          refine ⟨27540305005438228656002621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73440813347835276416006989 27540305005438228656002621)
          ·
            refine ⟨10327614377039335746000983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27540305005438228656002621 10327614377039335746000983)
            ·
              refine ⟨15491421565559003619001475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10327614377039335746000983 15491421565559003619001475)
              ·
                refine ⟨23237132348338505428502213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15491421565559003619001475 23237132348338505428502213)
                ·
                  refine ⟨4356962315313469767844165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23237132348338505428502213 4356962315313469767844165)
                  ·
                    refine ⟨816930434121275581470781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4356962315313469767844165 816930434121275581470781)
                    ·
                      rfl

theorem cell23_4772899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 4].length) (baseStart_4772899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772899 prefixEnd_4772899 := by exact prefixLift 4772899
  have htrace : WordTrace (prefixWord ++ tailWord_4772899) baseStart_4772899 baseEnd_4772899 := by
    simpa [prefixWord, tailWord_4772899, baseEnd_4772899] using wordTrace_append hprefix tailTrace_4772899
  have hstable : (prefixWord ++ tailWord_4772899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772899).length < 2 ^ (prefixWord ++ tailWord_4772899).sum := by decide
  have hdescent : baseEnd_4772899 < baseStart_4772899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772916 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_4772916 : Nat := 118140960795 + 4772916 * 2 ^ 59
def prefixEnd_4772916 : Nat := 4983230072969 + 3 ^ 40 * 4772916 * 2
def baseEnd_4772916 : Nat := 816933343844984392633255

theorem tailTrace_4772916 : CollatzResearch.WordTrace tailWord_4772916 prefixEnd_4772916 816933343844984392633255 := by
  unfold tailWord_4772916
  simp only [CollatzResearch.WordTrace]
  refine ⟨87041273988273978000285301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116055031984365304000380401 87041273988273978000285301)
  ·
    refine ⟨8160119436400685437526747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87041273988273978000285301 8160119436400685437526747)
    ·
      refine ⟨12240179154601028156290121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8160119436400685437526747 12240179154601028156290121)
      ·
        refine ⟨9180134365950771117217591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12240179154601028156290121 9180134365950771117217591)
        ·
          refine ⟨13770201548926156675826387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9180134365950771117217591 13770201548926156675826387)
          ·
            refine ⟨20655302323389235013739581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13770201548926156675826387 20655302323389235013739581)
            ·
              refine ⟨7745738371270963130152343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20655302323389235013739581 7745738371270963130152343)
              ·
                refine ⟨11618607556906444695228515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7745738371270963130152343 11618607556906444695228515)
                ·
                  refine ⟨17427911335359667042842773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11618607556906444695228515 17427911335359667042842773)
                  ·
                    refine ⟨816933343844984392633255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17427911335359667042842773 816933343844984392633255)
                    ·
                      rfl

theorem cell23_4772916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_4772916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772916 prefixEnd_4772916 := by exact prefixLift 4772916
  have htrace : WordTrace (prefixWord ++ tailWord_4772916) baseStart_4772916 baseEnd_4772916 := by
    simpa [prefixWord, tailWord_4772916, baseEnd_4772916] using wordTrace_append hprefix tailTrace_4772916
  have hstable : (prefixWord ++ tailWord_4772916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772916).length < 2 ^ (prefixWord ++ tailWord_4772916).sum := by decide
  have hdescent : baseEnd_4772916 < baseStart_4772916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772929 : List Nat := [1, 2, 5, 1, 3, 1, 1, 9]
def baseStart_4772929 : Nat := 118140960795 + 4772929 * 2 ^ 59
def prefixEnd_4772929 : Nat := 4983230072969 + 3 ^ 40 * 4772929 * 2
def baseEnd_4772929 : Nat := 90770618769757838038415

theorem tailTrace_4772929 : CollatzResearch.WordTrace tailWord_4772929 prefixEnd_4772929 90770618769757838038415 := by
  unfold tailWord_4772929
  simp only [CollatzResearch.WordTrace]
  refine ⟨174083022125500859220793841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116055348083667239480529227 174083022125500859220793841)
  ·
    refine ⟨130562266594125644415595381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174083022125500859220793841 130562266594125644415595381)
    ·
      refine ⟨12240212493199279163962067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130562266594125644415595381 12240212493199279163962067)
      ·
        refine ⟨18360318739798918745943101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12240212493199279163962067 18360318739798918745943101)
        ·
          refine ⟨6885119527424594529728663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18360318739798918745943101 6885119527424594529728663)
          ·
            refine ⟨10327679291136891794592995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6885119527424594529728663 10327679291136891794592995)
            ·
              refine ⟨15491518936705337691889493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10327679291136891794592995 15491518936705337691889493)
              ·
                refine ⟨90770618769757838038415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15491518936705337691889493 90770618769757838038415)
                ·
                  rfl

theorem cell23_4772929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 9].length) (baseStart_4772929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772929 prefixEnd_4772929 := by exact prefixLift 4772929
  have htrace : WordTrace (prefixWord ++ tailWord_4772929) baseStart_4772929 baseEnd_4772929 := by
    simpa [prefixWord, tailWord_4772929, baseEnd_4772929] using wordTrace_append hprefix tailTrace_4772929
  have hstable : (prefixWord ++ tailWord_4772929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772929).length < 2 ^ (prefixWord ++ tailWord_4772929).sum := by decide
  have hdescent : baseEnd_4772929 < baseStart_4772929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772952 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_4772952 : Nat := 118140960795 + 4772952 * 2 ^ 59
def prefixEnd_4772952 : Nat := 4983230072969 + 3 ^ 40 * 4772952 * 2
def baseEnd_4772952 : Nat := 2450818516838515037049599

theorem tailTrace_4772952 : CollatzResearch.WordTrace tailWord_4772952 prefixEnd_4772952 2450818516838515037049599 := by
  unfold tailWord_4772952
  simp only [CollatzResearch.WordTrace]
  refine ⟨87041930502208767074440555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116055907336278356099254073 87041930502208767074440555)
  ·
    refine ⟨130562895753313150611660833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87041930502208767074440555 130562895753313150611660833)
    ·
      refine ⟨97922171814984862958745625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130562895753313150611660833 97922171814984862958745625)
      ·
        refine ⟨73441628861238647219059219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97922171814984862958745625 73441628861238647219059219)
        ·
          refine ⟨110162443291857970828588829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73441628861238647219059219 110162443291857970828588829)
          ·
            refine ⟨41310916234446739060720811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110162443291857970828588829 41310916234446739060720811)
            ·
              refine ⟨61966374351670108591081217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41310916234446739060720811 61966374351670108591081217)
              ·
                refine ⟨46474780763752581443310913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61966374351670108591081217 46474780763752581443310913)
                ·
                  refine ⟨34856085572814436082483185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46474780763752581443310913 34856085572814436082483185)
                  ·
                    refine ⟨26142064179610827061862389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34856085572814436082483185 26142064179610827061862389)
                    ·
                      refine ⟨2450818516838515037049599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26142064179610827061862389 2450818516838515037049599)
                      ·
                        rfl

theorem cell23_4772952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_4772952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772952 prefixEnd_4772952 := by exact prefixLift 4772952
  have htrace : WordTrace (prefixWord ++ tailWord_4772952) baseStart_4772952 baseEnd_4772952 := by
    simpa [prefixWord, tailWord_4772952, baseEnd_4772952] using wordTrace_append hprefix tailTrace_4772952
  have hstable : (prefixWord ++ tailWord_4772952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772952).length < 2 ^ (prefixWord ++ tailWord_4772952).sum := by decide
  have hdescent : baseEnd_4772952 < baseStart_4772952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772956 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_4772956 : Nat := 118140960795 + 4772956 * 2 ^ 59
def prefixEnd_4772956 : Nat := 4983230072969 + 3 ^ 40 * 4772956 * 2
def baseEnd_4772956 : Nat := 2450820570761133021399581

theorem tailTrace_4772956 : CollatzResearch.WordTrace tailWord_4772956 prefixEnd_4772956 2450820570761133021399581 := by
  unfold tailWord_4772956
  simp only [CollatzResearch.WordTrace]
  refine ⟨87042003448201521416013361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116056004597602028554684481 87042003448201521416013361)
  ·
    refine ⟨65281502586151141062010021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87042003448201521416013361 65281502586151141062010021)
    ·
      refine ⟨12240281734903338949126879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65281502586151141062010021 12240281734903338949126879)
      ·
        refine ⟨18360422602355008423690319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12240281734903338949126879 18360422602355008423690319)
        ·
          refine ⟨27540633903532512635535479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18360422602355008423690319 27540633903532512635535479)
          ·
            refine ⟨41310950855298768953303219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27540633903532512635535479 41310950855298768953303219)
            ·
              refine ⟨61966426282948153429954829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41310950855298768953303219 61966426282948153429954829)
              ·
                refine ⟨23237409856105557536233061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61966426282948153429954829 23237409856105557536233061)
                ·
                  refine ⟨4357014348019792038043699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23237409856105557536233061 4357014348019792038043699)
                  ·
                    refine ⟨6535521522029688057065549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4357014348019792038043699 6535521522029688057065549)
                    ·
                      refine ⟨2450820570761133021399581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6535521522029688057065549 2450820570761133021399581)
                      ·
                        rfl

theorem cell23_4772956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_4772956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772956 prefixEnd_4772956 := by exact prefixLift 4772956
  have htrace : WordTrace (prefixWord ++ tailWord_4772956) baseStart_4772956 baseEnd_4772956 := by
    simpa [prefixWord, tailWord_4772956, baseEnd_4772956] using wordTrace_append hprefix tailTrace_4772956
  have hstable : (prefixWord ++ tailWord_4772956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772956).length < 2 ^ (prefixWord ++ tailWord_4772956).sum := by decide
  have hdescent : baseEnd_4772956 < baseStart_4772956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772957 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_4772957 : Nat := 118140960795 + 4772957 * 2 ^ 59
def prefixEnd_4772957 : Nat := 4983230072969 + 3 ^ 40 * 4772957 * 2
def baseEnd_4772957 : Nat := 2450821084241787517487077

theorem tailTrace_4772957 : CollatzResearch.WordTrace tailWord_4772957 prefixEnd_4772957 2450821084241787517487077 := by
  unfold tailWord_4772957
  simp only [CollatzResearch.WordTrace]
  refine ⟨174084043369399420002813125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116056028912932946668542083 174084043369399420002813125)
  ·
    refine ⟨32640758131762391250527461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174084043369399420002813125 32640758131762391250527461)
    ·
      refine ⟨6120142149705448359473899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32640758131762391250527461 6120142149705448359473899)
      ·
        refine ⟨9180213224558172539210849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6120142149705448359473899 9180213224558172539210849)
        ·
          refine ⟨6885159918418629404408137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9180213224558172539210849 6885159918418629404408137)
          ·
            refine ⟨5163869938813972053306103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6885159918418629404408137 5163869938813972053306103)
            ·
              refine ⟨7745804908220958079959155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5163869938813972053306103 7745804908220958079959155)
              ·
                refine ⟨11618707362331437119938733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7745804908220958079959155 11618707362331437119938733)
                ·
                  refine ⟨4357015260874288919977025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11618707362331437119938733 4357015260874288919977025)
                  ·
                    refine ⟨3267761445655716689982769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4357015260874288919977025 3267761445655716689982769)
                    ·
                      refine ⟨2450821084241787517487077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267761445655716689982769 2450821084241787517487077)
                      ·
                        rfl

theorem cell23_4772957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_4772957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772957 prefixEnd_4772957 := by exact prefixLift 4772957
  have htrace : WordTrace (prefixWord ++ tailWord_4772957) baseStart_4772957 baseEnd_4772957 := by
    simpa [prefixWord, tailWord_4772957, baseEnd_4772957] using wordTrace_append hprefix tailTrace_4772957
  have hstable : (prefixWord ++ tailWord_4772957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772957).length < 2 ^ (prefixWord ++ tailWord_4772957).sum := by decide
  have hdescent : baseEnd_4772957 < baseStart_4772957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772972 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 1, 8]
def baseStart_4772972 : Nat := 118140960795 + 4772972 * 2 ^ 59
def prefixEnd_4772972 : Nat := 4983230072969 + 3 ^ 40 * 4772972 * 2
def baseEnd_4772972 : Nat := 816942928817201652933169

theorem tailTrace_4772972 : CollatzResearch.WordTrace tailWord_4772972 prefixEnd_4772972 816942928817201652933169 := by
  unfold tailWord_4772972
  simp only [CollatzResearch.WordTrace]
  refine ⟨87042295232172538782304585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116056393642896718376406113 87042295232172538782304585)
  ·
    refine ⟨65281721424129404086728439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87042295232172538782304585 65281721424129404086728439)
    ·
      refine ⟨97922582136194106130092659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65281721424129404086728439 97922582136194106130092659)
      ·
        refine ⟨146883873204291159195138989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97922582136194106130092659 146883873204291159195138989)
        ·
          refine ⟨55081452451609184698177121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146883873204291159195138989 55081452451609184698177121)
          ·
            refine ⟨41311089338706888523632841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55081452451609184698177121 41311089338706888523632841)
            ·
              refine ⟨30983317004030166392724631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41311089338706888523632841 30983317004030166392724631)
              ·
                refine ⟨46474975506045249589086947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30983317004030166392724631 46474975506045249589086947)
                ·
                  refine ⟨69712463259067874383630421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46474975506045249589086947 69712463259067874383630421)
                  ·
                    refine ⟨816942928817201652933169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69712463259067874383630421 816942928817201652933169)
                    ·
                      rfl

theorem cell23_4772972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_4772972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772972 prefixEnd_4772972 := by exact prefixLift 4772972
  have htrace : WordTrace (prefixWord ++ tailWord_4772972) baseStart_4772972 baseEnd_4772972 := by
    simpa [prefixWord, tailWord_4772972, baseEnd_4772972] using wordTrace_append hprefix tailTrace_4772972
  have hstable : (prefixWord ++ tailWord_4772972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772972).length < 2 ^ (prefixWord ++ tailWord_4772972).sum := by decide
  have hdescent : baseEnd_4772972 < baseStart_4772972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772973 : List Nat := [1, 5, 1, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_4772973 : Nat := 118140960795 + 4772973 * 2 ^ 59
def prefixEnd_4772973 : Nat := 4983230072969 + 3 ^ 40 * 4772973 * 2
def baseEnd_4772973 : Nat := 2450829299932259454887003

theorem tailTrace_4772973 : CollatzResearch.WordTrace tailWord_4772973 prefixEnd_4772973 2450829299932259454887003 := by
  unfold tailWord_4772973
  simp only [CollatzResearch.WordTrace]
  refine ⟨174084626937341454735395573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116056417958227636490263715 174084626937341454735395573)
  ·
    refine ⟨16320433775375761381443335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174084626937341454735395573 16320433775375761381443335)
    ·
      refine ⟨24480650663063642072165003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16320433775375761381443335 24480650663063642072165003)
      ·
        refine ⟨36720975994595463108247505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24480650663063642072165003 36720975994595463108247505)
        ·
          refine ⟨27540731995946597331185629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36720975994595463108247505 27540731995946597331185629)
          ·
            refine ⟨10327774498479973999194611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27540731995946597331185629 10327774498479973999194611)
            ·
              refine ⟨15491661747719960998791917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10327774498479973999194611 15491661747719960998791917)
              ·
                refine ⟨5809373155394985374546969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15491661747719960998791917 5809373155394985374546969)
                ·
                  refine ⟨4357029866546239030910227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5809373155394985374546969 4357029866546239030910227)
                  ·
                    refine ⟨6535544799819358546365341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4357029866546239030910227 6535544799819358546365341)
                    ·
                      refine ⟨2450829299932259454887003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6535544799819358546365341 2450829299932259454887003)
                      ·
                        rfl

theorem cell23_4772973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_4772973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772973 prefixEnd_4772973 := by exact prefixLift 4772973
  have htrace : WordTrace (prefixWord ++ tailWord_4772973) baseStart_4772973 baseEnd_4772973 := by
    simpa [prefixWord, tailWord_4772973, baseEnd_4772973] using wordTrace_append hprefix tailTrace_4772973
  have hstable : (prefixWord ++ tailWord_4772973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772973).length < 2 ^ (prefixWord ++ tailWord_4772973).sum := by decide
  have hdescent : baseEnd_4772973 < baseStart_4772973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772979 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 7, 4, 2]
def baseStart_4772979 : Nat := 118140960795 + 4772979 * 2 ^ 59
def prefixEnd_4772979 : Nat := 4983230072969 + 3 ^ 40 * 4772979 * 2
def baseEnd_4772979 : Nat := 2450832380816186431411975

theorem tailTrace_4772979 : CollatzResearch.WordTrace tailWord_4772979 prefixEnd_4772979 2450832380816186431411975 := by
  unfold tailWord_4772979
  simp only [CollatzResearch.WordTrace]
  refine ⟨174084845775319717760113991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116056563850213145173409327 174084845775319717760113991)
  ·
    refine ⟨261127268662979576640170987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174084845775319717760113991 261127268662979576640170987)
    ·
      refine ⟨391690902994469364960256481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261127268662979576640170987 391690902994469364960256481)
      ·
        refine ⟨293768177245852023720192361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391690902994469364960256481 293768177245852023720192361)
        ·
          refine ⟨220326132934389017790144271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293768177245852023720192361 220326132934389017790144271)
          ·
            refine ⟨330489199401583526685216407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220326132934389017790144271 330489199401583526685216407)
            ·
              refine ⟨495733799102375290027824611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330489199401583526685216407 495733799102375290027824611)
              ·
                refine ⟨743600698653562935041736917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495733799102375290027824611 743600698653562935041736917)
                ·
                  refine ⟨17428141374692881290040709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 743600698653562935041736917 17428141374692881290040709)
                  ·
                    refine ⟨3267776507754915241882633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17428141374692881290040709 3267776507754915241882633)
                    ·
                      refine ⟨2450832380816186431411975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267776507754915241882633 2450832380816186431411975)
                      ·
                        rfl

theorem cell23_4772979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 4, 2].length) (baseStart_4772979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772979 prefixEnd_4772979 := by exact prefixLift 4772979
  have htrace : WordTrace (prefixWord ++ tailWord_4772979) baseStart_4772979 baseEnd_4772979 := by
    simpa [prefixWord, tailWord_4772979, baseEnd_4772979] using wordTrace_append hprefix tailTrace_4772979
  have hstable : (prefixWord ++ tailWord_4772979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772979).length < 2 ^ (prefixWord ++ tailWord_4772979).sum := by decide
  have hdescent : baseEnd_4772979 < baseStart_4772979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772996 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_4772996 : Nat := 118140960795 + 4772996 * 2 ^ 59
def prefixEnd_4772996 : Nat := 4983230072969 + 3 ^ 40 * 4772996 * 2
def baseEnd_4772996 : Nat := 2450841109987312864899397

theorem tailTrace_4772996 : CollatzResearch.WordTrace tailWord_4772996 prefixEnd_4772996 2450841109987312864899397 := by
  unfold tailWord_4772996
  simp only [CollatzResearch.WordTrace]
  refine ⟨87042732908129064831741421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116056977210838753108988561 87042732908129064831741421)
  ·
    refine ⟨32641024840548399311903033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87042732908129064831741421 32641024840548399311903033)
    ·
      refine ⟨24480768630411299483927275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32641024840548399311903033 24480768630411299483927275)
      ·
        refine ⟨36721152945616949225890913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24480768630411299483927275 36721152945616949225890913)
        ·
          refine ⟨27540864709212711919418185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36721152945616949225890913 27540864709212711919418185)
          ·
            refine ⟨20655648531909533939563639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27540864709212711919418185 20655648531909533939563639)
            ·
              refine ⟨30983472797864300909345459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20655648531909533939563639 30983472797864300909345459)
              ·
                refine ⟨46475209196796451364018189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30983472797864300909345459 46475209196796451364018189)
                ·
                  refine ⟨17428203448798669261506821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46475209196796451364018189 17428203448798669261506821)
                  ·
                    refine ⟨3267788146649750486532529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17428203448798669261506821 3267788146649750486532529)
                    ·
                      refine ⟨2450841109987312864899397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267788146649750486532529 2450841109987312864899397)
                      ·
                        rfl

theorem cell23_4772996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_4772996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4772996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4772996 prefixEnd_4772996 := by exact prefixLift 4772996
  have htrace : WordTrace (prefixWord ++ tailWord_4772996) baseStart_4772996 baseEnd_4772996 := by
    simpa [prefixWord, tailWord_4772996, baseEnd_4772996] using wordTrace_append hprefix tailTrace_4772996
  have hstable : (prefixWord ++ tailWord_4772996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772996).length < 2 ^ (prefixWord ++ tailWord_4772996).sum := by decide
  have hdescent : baseEnd_4772996 < baseStart_4772996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773029 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 1, 5, 3]
def baseStart_4773029 : Nat := 118140960795 + 4773029 * 2 ^ 59
def prefixEnd_4773029 : Nat := 4983230072969 + 3 ^ 40 * 4773029 * 2
def baseEnd_4773029 : Nat := 2450858054848911235786745

theorem tailTrace_4773029 : CollatzResearch.WordTrace tailWord_4773029 prefixEnd_4773029 2450858054848911235786745 := by
  unfold tailWord_4773029
  simp only [CollatzResearch.WordTrace]
  refine ⟨174086669425138576299434141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116057779616759050866289427 174086669425138576299434141)
  ·
    refine ⟨65282501034426966112287803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174086669425138576299434141 65282501034426966112287803)
    ·
      refine ⟨97923751551640449168431705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65282501034426966112287803 97923751551640449168431705)
      ·
        refine ⟨73442813663730336876323779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97923751551640449168431705 73442813663730336876323779)
        ·
          refine ⟨110164220495595505314485669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73442813663730336876323779 110164220495595505314485669)
          ·
            refine ⟨20655791342924157246466063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110164220495595505314485669 20655791342924157246466063)
            ·
              refine ⟨30983687014386235869699095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20655791342924157246466063 30983687014386235869699095)
              ·
                refine ⟨46475530521579353804548643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30983687014386235869699095 46475530521579353804548643)
                ·
                  refine ⟨69713295782369030706822965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46475530521579353804548643 69713295782369030706822965)
                  ·
                    refine ⟨6535621479597096628764653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69713295782369030706822965 6535621479597096628764653)
                    ·
                      refine ⟨2450858054848911235786745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6535621479597096628764653 2450858054848911235786745)
                      ·
                        rfl

theorem cell23_4773029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_4773029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773029 prefixEnd_4773029 := by exact prefixLift 4773029
  have htrace : WordTrace (prefixWord ++ tailWord_4773029) baseStart_4773029 baseEnd_4773029 := by
    simpa [prefixWord, tailWord_4773029, baseEnd_4773029] using wordTrace_append hprefix tailTrace_4773029
  have hstable : (prefixWord ++ tailWord_4773029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773029).length < 2 ^ (prefixWord ++ tailWord_4773029).sum := by decide
  have hdescent : baseEnd_4773029 < baseStart_4773029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773049 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 1, 7]
def baseStart_4773049 : Nat := 118140960795 + 4773049 * 2 ^ 59
def prefixEnd_4773049 : Nat := 4983230072969 + 3 ^ 40 * 4773049 * 2
def baseEnd_4773049 : Nat := 816956108154000385845551

theorem tailTrace_4773049 : CollatzResearch.WordTrace tailWord_4773049 prefixEnd_4773049 816956108154000385845551 := by
  unfold tailWord_4773049
  simp only [CollatzResearch.WordTrace]
  refine ⟨174087398885066119715162201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116058265923377413143441467 174087398885066119715162201)
  ·
    refine ⟨130565549163799589786371651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174087398885066119715162201 130565549163799589786371651)
    ·
      refine ⟨195848323745699384679557477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130565549163799589786371651 195848323745699384679557477)
      ·
        refine ⟨36721560702318634627417027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195848323745699384679557477 36721560702318634627417027)
        ·
          refine ⟨55082341053477951941125541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36721560702318634627417027 55082341053477951941125541)
          ·
            refine ⟨10327938947527115988961039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55082341053477951941125541 10327938947527115988961039)
            ·
              refine ⟨15491908421290673983441559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10327938947527115988961039 15491908421290673983441559)
              ·
                refine ⟨23237862631936010975162339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15491908421290673983441559 23237862631936010975162339)
                ·
                  refine ⟨34856793947904016462743509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23237862631936010975162339 34856793947904016462743509)
                  ·
                    refine ⟨816956108154000385845551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34856793947904016462743509 816956108154000385845551)
                    ·
                      rfl

theorem cell23_4773049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_4773049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773049 prefixEnd_4773049 := by exact prefixLift 4773049
  have htrace : WordTrace (prefixWord ++ tailWord_4773049) baseStart_4773049 baseEnd_4773049 := by
    simpa [prefixWord, tailWord_4773049, baseEnd_4773049] using wordTrace_append hprefix tailTrace_4773049
  have hstable : (prefixWord ++ tailWord_4773049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773049).length < 2 ^ (prefixWord ++ tailWord_4773049).sum := by decide
  have hdescent : baseEnd_4773049 < baseStart_4773049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773096 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 3, 4]
def baseStart_4773096 : Nat := 118140960795 + 4773096 * 2 ^ 59
def prefixEnd_4773096 : Nat := 4983230072969 + 3 ^ 40 * 4773096 * 2
def baseEnd_4773096 : Nat := 816964152684254157882979

theorem tailTrace_4773096 : CollatzResearch.WordTrace tailWord_4773096 prefixEnd_4773096 816964152684254157882979 := by
  unfold tailWord_4773096
  simp only [CollatzResearch.WordTrace]
  refine ⟨87044556557947923371061571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116059408743930564494748761 87044556557947923371061571)
  ·
    refine ⟨130566834836921885056592357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87044556557947923371061571 130566834836921885056592357)
    ·
      refine ⟨24481281531922853448111067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130566834836921885056592357 24481281531922853448111067)
      ·
        refine ⟨36721922297884280172166601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24481281531922853448111067 36721922297884280172166601)
        ·
          refine ⟨27541441723413210129124951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36721922297884280172166601 27541441723413210129124951)
          ·
            refine ⟨41312162585119815193687427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27541441723413210129124951 41312162585119815193687427)
            ·
              refine ⟨61968243877679722790531141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41312162585119815193687427 61968243877679722790531141)
              ·
                refine ⟨11619045727064948023224589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61968243877679722790531141 11619045727064948023224589)
                ·
                  refine ⟨4357142147649355508709221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11619045727064948023224589 4357142147649355508709221)
                  ·
                    refine ⟨816964152684254157882979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4357142147649355508709221 816964152684254157882979)
                    ·
                      rfl

theorem cell23_4773096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_4773096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773096 prefixEnd_4773096 := by exact prefixLift 4773096
  have htrace : WordTrace (prefixWord ++ tailWord_4773096) baseStart_4773096 baseEnd_4773096 := by
    simpa [prefixWord, tailWord_4773096, baseEnd_4773096] using wordTrace_append hprefix tailTrace_4773096
  have hstable : (prefixWord ++ tailWord_4773096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773096).length < 2 ^ (prefixWord ++ tailWord_4773096).sum := by decide
  have hdescent : baseEnd_4773096 < baseStart_4773096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773156 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_4773156 : Nat := 118140960795 + 4773156 * 2 ^ 59
def prefixEnd_4773156 : Nat := 4983230072969 + 3 ^ 40 * 4773156 * 2
def baseEnd_4773156 : Nat := 816974422297344079632887

theorem tailTrace_4773156 : CollatzResearch.WordTrace tailWord_4773156 prefixEnd_4773156 816974422297344079632887 := by
  unfold tailWord_4773156
  simp only [CollatzResearch.WordTrace]
  refine ⟨87045650747839238494653661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116060867663785651326204881 87045650747839238494653661)
  ·
    refine ⟨32642119030439714435495123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87045650747839238494653661 32642119030439714435495123)
    ·
      refine ⟨48963178545659571653242685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32642119030439714435495123 48963178545659571653242685)
      ·
        refine ⟨18361191954622339369966007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48963178545659571653242685 18361191954622339369966007)
        ·
          refine ⟨27541787931933509054949011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18361191954622339369966007 27541787931933509054949011)
          ·
            refine ⟨41312681897900263582423517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27541787931933509054949011 41312681897900263582423517)
            ·
              refine ⟨15492255711712598843408819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41312681897900263582423517 15492255711712598843408819)
              ·
                refine ⟨23238383567568898265113229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15492255711712598843408819 23238383567568898265113229)
                ·
                  refine ⟨8714393837838336849417461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23238383567568898265113229 8714393837838336849417461)
                  ·
                    refine ⟨816974422297344079632887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8714393837838336849417461 816974422297344079632887)
                    ·
                      rfl

theorem cell23_4773156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_4773156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773156 prefixEnd_4773156 := by exact prefixLift 4773156
  have htrace : WordTrace (prefixWord ++ tailWord_4773156) baseStart_4773156 baseEnd_4773156 := by
    simpa [prefixWord, tailWord_4773156, baseEnd_4773156] using wordTrace_append hprefix tailTrace_4773156
  have hstable : (prefixWord ++ tailWord_4773156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773156).length < 2 ^ (prefixWord ++ tailWord_4773156).sum := by decide
  have hdescent : baseEnd_4773156 < baseStart_4773156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773181 : List Nat := [1, 4, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_4773181 : Nat := 118140960795 + 4773181 * 2 ^ 59
def prefixEnd_4773181 : Nat := 4983230072969 + 3 ^ 40 * 4773181 * 2
def baseEnd_4773181 : Nat := 816978701302798213695349

theorem tailTrace_4773181 : CollatzResearch.WordTrace tailWord_4773181 prefixEnd_4773181 816978701302798213695349 := by
  unfold tailWord_4773181
  simp only [CollatzResearch.WordTrace]
  refine ⟨174092213320587906258967397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116061475547058604172644931 174092213320587906258967397)
  ·
    refine ⟨32642289997610232423556387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174092213320587906258967397 32642289997610232423556387)
    ·
      refine ⟨48963434996415348635334581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32642289997610232423556387 48963434996415348635334581)
      ·
        refine ⟨4590322030913938934562617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48963434996415348635334581 4590322030913938934562617)
        ·
          refine ⟨3442741523185454200921963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4590322030913938934562617 3442741523185454200921963)
          ·
            refine ⟨5164112284778181301382945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442741523185454200921963 5164112284778181301382945)
            ·
              refine ⟨3873084213583635976037209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5164112284778181301382945 3873084213583635976037209)
              ·
                refine ⟨2904813160187726982027907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3873084213583635976037209 2904813160187726982027907)
                ·
                  refine ⟨4357219740281590473041861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2904813160187726982027907 4357219740281590473041861)
                  ·
                    refine ⟨816978701302798213695349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4357219740281590473041861 816978701302798213695349)
                    ·
                      rfl

theorem cell23_4773181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_4773181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773181 prefixEnd_4773181 := by exact prefixLift 4773181
  have htrace : WordTrace (prefixWord ++ tailWord_4773181) baseStart_4773181 baseEnd_4773181 := by
    simpa [prefixWord, tailWord_4773181, baseEnd_4773181] using wordTrace_append hprefix tailTrace_4773181
  have hstable : (prefixWord ++ tailWord_4773181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773181).length < 2 ^ (prefixWord ++ tailWord_4773181).sum := by decide
  have hdescent : baseEnd_4773181 < baseStart_4773181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773189 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_4773189 : Nat := 118140960795 + 4773189 * 2 ^ 59
def prefixEnd_4773189 : Nat := 4983230072969 + 3 ^ 40 * 4773189 * 2
def baseEnd_4773189 : Nat := 2450940211753630609786009

theorem tailTrace_4773189 : CollatzResearch.WordTrace tailWord_4773189 prefixEnd_4773189 2450940211753630609786009 := by
  unfold tailWord_4773189
  simp only [CollatzResearch.WordTrace]
  refine ⟨174092505104558923625258621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116061670069705949083505747 174092505104558923625258621)
  ·
    refine ⟨65284689414209596359471983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174092505104558923625258621 65284689414209596359471983)
    ·
      refine ⟨97927034121314394539207975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65284689414209596359471983 97927034121314394539207975)
      ·
        refine ⟨146890551181971591808811963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97927034121314394539207975 146890551181971591808811963)
        ·
          refine ⟨220335826772957387713217945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146890551181971591808811963 220335826772957387713217945)
          ·
            refine ⟨165251870079718040784913459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220335826772957387713217945 165251870079718040784913459)
            ·
              refine ⟨247877805119577061177370189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165251870079718040784913459 247877805119577061177370189)
              ·
                refine ⟨92954176919841397941513821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247877805119577061177370189 92954176919841397941513821)
                ·
                  refine ⟨34857816344940524228067683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92954176919841397941513821 34857816344940524228067683)
                  ·
                    refine ⟨52286724517410786342101525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34857816344940524228067683 52286724517410786342101525)
                    ·
                      refine ⟨2450940211753630609786009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52286724517410786342101525 2450940211753630609786009)
                      ·
                        rfl

theorem cell23_4773189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_4773189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773189 prefixEnd_4773189 := by exact prefixLift 4773189
  have htrace : WordTrace (prefixWord ++ tailWord_4773189) baseStart_4773189 baseEnd_4773189 := by
    simpa [prefixWord, tailWord_4773189, baseEnd_4773189] using wordTrace_append hprefix tailTrace_4773189
  have hstable : (prefixWord ++ tailWord_4773189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773189).length < 2 ^ (prefixWord ++ tailWord_4773189).sum := by decide
  have hdescent : baseEnd_4773189 < baseStart_4773189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773237 : List Nat := [1, 3, 4, 1, 3, 2, 1, 2, 2, 4]
def baseStart_4773237 : Nat := 118140960795 + 4773237 * 2 ^ 59
def prefixEnd_4773237 : Nat := 4983230072969 + 3 ^ 40 * 4773237 * 2
def baseEnd_4773237 : Nat := 816988286275015473995263

theorem tailTrace_4773237 : CollatzResearch.WordTrace tailWord_4773237 prefixEnd_4773237 816988286275015473995263 := by
  unfold tailWord_4773237
  simp only [CollatzResearch.WordTrace]
  refine ⟨174094255808385027823005965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116062837205590018548670643 174094255808385027823005965)
  ·
    refine ⟨65285345928144385433627237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174094255808385027823005965 65285345928144385433627237)
    ·
      refine ⟨12241002361527072268805107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65285345928144385433627237 12241002361527072268805107)
      ·
        refine ⟨18361503542290608403207661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12241002361527072268805107 18361503542290608403207661)
        ·
          refine ⟨6885563828358978151202873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18361503542290608403207661 6885563828358978151202873)
          ·
            refine ⟨5164172871269233613402155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6885563828358978151202873 5164172871269233613402155)
            ·
              refine ⟨7746259306903850420103233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5164172871269233613402155 7746259306903850420103233)
              ·
                refine ⟨5809694480177887815077425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7746259306903850420103233 5809694480177887815077425)
                ·
                  refine ⟨4357270860133415861308069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5809694480177887815077425 4357270860133415861308069)
                  ·
                    refine ⟨816988286275015473995263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4357270860133415861308069 816988286275015473995263)
                    ·
                      rfl

theorem cell23_4773237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_4773237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773237 prefixEnd_4773237 := by exact prefixLift 4773237
  have htrace : WordTrace (prefixWord ++ tailWord_4773237) baseStart_4773237 baseEnd_4773237 := by
    simpa [prefixWord, tailWord_4773237, baseEnd_4773237] using wordTrace_append hprefix tailTrace_4773237
  have hstable : (prefixWord ++ tailWord_4773237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773237).length < 2 ^ (prefixWord ++ tailWord_4773237).sum := by decide
  have hdescent : baseEnd_4773237 < baseStart_4773237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773243 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 4, 1, 3]
def baseStart_4773243 : Nat := 118140960795 + 4773243 * 2 ^ 59
def prefixEnd_4773243 : Nat := 4983230072969 + 3 ^ 40 * 4773243 * 2
def baseEnd_4773243 : Nat := 2450967939708973398510761

theorem tailTrace_4773243 : CollatzResearch.WordTrace tailWord_4773243 prefixEnd_4773243 2450967939708973398510761 := by
  unfold tailWord_4773243
  simp only [CollatzResearch.WordTrace]
  refine ⟨174094474646363290847724383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116062983097575527231816255 174094474646363290847724383)
  ·
    refine ⟨261141711969544936271586575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174094474646363290847724383 261141711969544936271586575)
    ·
      refine ⟨391712567954317404407379863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261141711969544936271586575 391712567954317404407379863)
      ·
        refine ⟨587568851931476106611069795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391712567954317404407379863 587568851931476106611069795)
        ·
          refine ⟨881353277897214159916604693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587568851931476106611069795 881353277897214159916604693)
          ·
            refine ⟨41313434901431913746090845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 881353277897214159916604693 41313434901431913746090845)
            ·
              refine ⟨15492538088036967654784067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41313434901431913746090845 15492538088036967654784067)
              ·
                refine ⟨23238807132055451482176101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15492538088036967654784067 23238807132055451482176101)
                ·
                  refine ⟨4357276337260397152908019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23238807132055451482176101 4357276337260397152908019)
                  ·
                    refine ⟨6535914505890595729362029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4357276337260397152908019 6535914505890595729362029)
                    ·
                      refine ⟨2450967939708973398510761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6535914505890595729362029 2450967939708973398510761)
                      ·
                        rfl

theorem cell23_4773243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 1, 3].length) (baseStart_4773243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773243 prefixEnd_4773243 := by exact prefixLift 4773243
  have htrace : WordTrace (prefixWord ++ tailWord_4773243) baseStart_4773243 baseEnd_4773243 := by
    simpa [prefixWord, tailWord_4773243, baseEnd_4773243] using wordTrace_append hprefix tailTrace_4773243
  have hstable : (prefixWord ++ tailWord_4773243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773243).length < 2 ^ (prefixWord ++ tailWord_4773243).sum := by decide
  have hdescent : baseEnd_4773243 < baseStart_4773243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773253 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 5, 3, 2]
def baseStart_4773253 : Nat := 118140960795 + 4773253 * 2 ^ 59
def prefixEnd_4773253 : Nat := 4983230072969 + 3 ^ 40 * 4773253 * 2
def baseEnd_4773253 : Nat := 2450973074515518359385715

theorem tailTrace_4773253 : CollatzResearch.WordTrace tailWord_4773253 prefixEnd_4773253 2450973074515518359385715 := by
  unfold tailWord_4773253
  simp only [CollatzResearch.WordTrace]
  refine ⟨174094839376327062555588413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116063226250884708370392275 174094839376327062555588413)
  ·
    refine ⟨65285564766122648458345655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174094839376327062555588413 65285564766122648458345655)
    ·
      refine ⟨97928347149183972687518483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65285564766122648458345655 97928347149183972687518483)
      ·
        refine ⟨146892520723775959031277725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97928347149183972687518483 146892520723775959031277725)
        ·
          refine ⟨55084695271415984636729147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146892520723775959031277725 55084695271415984636729147)
          ·
            refine ⟨82627042907123976955093721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55084695271415984636729147 82627042907123976955093721)
            ·
              refine ⟨61970282180342982716320291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82627042907123976955093721 61970282180342982716320291)
              ·
                refine ⟨92955423270514474074480437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61970282180342982716320291 92955423270514474074480437)
                ·
                  refine ⟨8714570931610731944482541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92955423270514474074480437 8714570931610731944482541)
                  ·
                    refine ⟨3267964099354024479180953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8714570931610731944482541 3267964099354024479180953)
                    ·
                      refine ⟨2450973074515518359385715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267964099354024479180953 2450973074515518359385715)
                      ·
                        rfl

theorem cell23_4773253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 3, 2].length) (baseStart_4773253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773253 prefixEnd_4773253 := by exact prefixLift 4773253
  have htrace : WordTrace (prefixWord ++ tailWord_4773253) baseStart_4773253 baseEnd_4773253 := by
    simpa [prefixWord, tailWord_4773253, baseEnd_4773253] using wordTrace_append hprefix tailTrace_4773253
  have hstable : (prefixWord ++ tailWord_4773253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773253).length < 2 ^ (prefixWord ++ tailWord_4773253).sum := by decide
  have hdescent : baseEnd_4773253 < baseStart_4773253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773278 : List Nat := [4, 3, 1, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_4773278 : Nat := 118140960795 + 4773278 * 2 ^ 59
def prefixEnd_4773278 : Nat := 4983230072969 + 3 ^ 40 * 4773278 * 2
def baseEnd_4773278 : Nat := 2450985911531880761573101

theorem tailTrace_4773278 : CollatzResearch.WordTrace tailWord_4773278 prefixEnd_4773278 2450985911531880761573101 := by
  unfold tailWord_4773278
  simp only [CollatzResearch.WordTrace]
  refine ⟨21761968900154561478156061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116063834134157661216832325 21761968900154561478156061)
  ·
    refine ⟨8160738337557960554308523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21761968900154561478156061 8160738337557960554308523)
    ·
      refine ⟨12241107506336940831462785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8160738337557960554308523 12241107506336940831462785)
      ·
        refine ⟨9180830629752705623597089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12241107506336940831462785 9180830629752705623597089)
        ·
          refine ⟨6885622972314529217697817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9180830629752705623597089 6885622972314529217697817)
          ·
            refine ⟨5164217229235896913273363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6885622972314529217697817 5164217229235896913273363)
            ·
              refine ⟨7746325843853845369910045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5164217229235896913273363 7746325843853845369910045)
              ·
                refine ⟨2904872191445192013716267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7746325843853845369910045 2904872191445192013716267)
                ·
                  refine ⟨4357308287167788020574401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2904872191445192013716267 4357308287167788020574401)
                  ·
                    refine ⟨3267981215375841015430801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4357308287167788020574401 3267981215375841015430801)
                    ·
                      refine ⟨2450985911531880761573101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267981215375841015430801 2450985911531880761573101)
                      ·
                        rfl

theorem cell23_4773278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_4773278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773278 prefixEnd_4773278 := by exact prefixLift 4773278
  have htrace : WordTrace (prefixWord ++ tailWord_4773278) baseStart_4773278 baseEnd_4773278 := by
    simpa [prefixWord, tailWord_4773278, baseEnd_4773278] using wordTrace_append hprefix tailTrace_4773278
  have hstable : (prefixWord ++ tailWord_4773278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773278).length < 2 ^ (prefixWord ++ tailWord_4773278).sum := by decide
  have hdescent : baseEnd_4773278 < baseStart_4773278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773283 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 3, 4, 2]
def baseStart_4773283 : Nat := 118140960795 + 4773283 * 2 ^ 59
def prefixEnd_4773283 : Nat := 4983230072969 + 3 ^ 40 * 4773283 * 2
def baseEnd_4773283 : Nat := 2450988478935153242010577

theorem tailTrace_4773283 : CollatzResearch.WordTrace tailWord_4773283 prefixEnd_4773283 2450988478935153242010577 := by
  unfold tailWord_4773283
  simp only [CollatzResearch.WordTrace]
  refine ⟨174095933566218377679180503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116063955710812251786120335 174095933566218377679180503)
  ·
    refine ⟨261143900349327566518770755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174095933566218377679180503 261143900349327566518770755)
    ·
      refine ⟨391715850523991349778156133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261143900349327566518770755 391715850523991349778156133)
      ·
        refine ⟨73446721973248378083404275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 391715850523991349778156133 73446721973248378083404275)
        ·
          refine ⟨110170082959872567125106413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73446721973248378083404275 110170082959872567125106413)
          ·
            refine ⟨41313781109952212671914905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110170082959872567125106413 41313781109952212671914905)
            ·
              refine ⟨30985335832464159503936179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41313781109952212671914905 30985335832464159503936179)
              ·
                refine ⟨46478003748696239255904269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30985335832464159503936179 46478003748696239255904269)
                ·
                  refine ⟨17429251405761089720964101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46478003748696239255904269 17429251405761089720964101)
                  ·
                    refine ⟨3267984638580204322680769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17429251405761089720964101 3267984638580204322680769)
                    ·
                      refine ⟨2450988478935153242010577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3267984638580204322680769 2450988478935153242010577)
                      ·
                        rfl

theorem cell23_4773283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_4773283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773283 prefixEnd_4773283 := by exact prefixLift 4773283
  have htrace : WordTrace (prefixWord ++ tailWord_4773283) baseStart_4773283 baseEnd_4773283 := by
    simpa [prefixWord, tailWord_4773283, baseEnd_4773283] using wordTrace_append hprefix tailTrace_4773283
  have hstable : (prefixWord ++ tailWord_4773283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773283).length < 2 ^ (prefixWord ++ tailWord_4773283).sum := by decide
  have hdescent : baseEnd_4773283 < baseStart_4773283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773296 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 4]
def baseStart_4773296 : Nat := 118140960795 + 4773296 * 2 ^ 59
def prefixEnd_4773296 : Nat := 4983230072969 + 3 ^ 40 * 4773296 * 2
def baseEnd_4773296 : Nat := 2450995154183661691148017

theorem tailTrace_4773296 : CollatzResearch.WordTrace tailWord_4773296 prefixEnd_4773296 2450995154183661691148017 := by
  unfold tailWord_4773296
  simp only [CollatzResearch.WordTrace]
  refine ⟨87048203857585640449701871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116064271810114187266269161 87048203857585640449701871)
  ·
    refine ⟨130572305786378460674552807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87048203857585640449701871 130572305786378460674552807)
    ·
      refine ⟨195858458679567691011829211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130572305786378460674552807 195858458679567691011829211)
      ·
        refine ⟨293787688019351536517743817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195858458679567691011829211 293787688019351536517743817)
        ·
          refine ⟨220340766014513652388307863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293787688019351536517743817 220340766014513652388307863)
          ·
            refine ⟨330511149021770478582461795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220340766014513652388307863 330511149021770478582461795)
            ·
              refine ⟨495766723532655717873692693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330511149021770478582461795 495766723532655717873692693)
              ·
                refine ⟨23239065165593236775329345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 495766723532655717873692693 23239065165593236775329345)
                ·
                  refine ⟨17429298874194927581497009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23239065165593236775329345 17429298874194927581497009)
                  ·
                    refine ⟨13071974155646195686122757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17429298874194927581497009 13071974155646195686122757)
                    ·
                      refine ⟨2450995154183661691148017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13071974155646195686122757 2450995154183661691148017)
                      ·
                        rfl

theorem cell23_4773296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_4773296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773296 prefixEnd_4773296 := by exact prefixLift 4773296
  have htrace : WordTrace (prefixWord ++ tailWord_4773296) baseStart_4773296 baseEnd_4773296 := by
    simpa [prefixWord, tailWord_4773296, baseEnd_4773296] using wordTrace_append hprefix tailTrace_4773296
  have hstable : (prefixWord ++ tailWord_4773296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773296).length < 2 ^ (prefixWord ++ tailWord_4773296).sum := by decide
  have hdescent : baseEnd_4773296 < baseStart_4773296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773336 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 1, 7]
def baseStart_4773336 : Nat := 118140960795 + 4773336 * 2 ^ 59
def prefixEnd_4773336 : Nat := 4983230072969 + 3 ^ 40 * 4773336 * 2
def baseEnd_4773336 : Nat := 817005231136613844882611

theorem tailTrace_4773336 : CollatzResearch.WordTrace tailWord_4773336 prefixEnd_4773336 817005231136613844882611 := by
  unfold tailWord_4773336
  simp only [CollatzResearch.WordTrace]
  refine ⟨87048933317513183865429931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116065244423350911820573241 87048933317513183865429931)
  ·
    refine ⟨130573399976269775798144897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87048933317513183865429931 130573399976269775798144897)
    ·
      refine ⟨97930049982202331848608673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130573399976269775798144897 97930049982202331848608673)
      ·
        refine ⟨73447537486651748886456505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97930049982202331848608673 73447537486651748886456505)
        ·
          refine ⟨55085653114988811664842379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73447537486651748886456505 55085653114988811664842379)
          ·
            refine ⟨82628479672483217497263569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55085653114988811664842379 82628479672483217497263569)
            ·
              refine ⟨61971359754362413122947677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82628479672483217497263569 61971359754362413122947677)
              ·
                refine ⟨23239259907885904921105379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61971359754362413122947677 23239259907885904921105379)
                ·
                  refine ⟨34858889861828857381658069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23239259907885904921105379 34858889861828857381658069)
                  ·
                    refine ⟨817005231136613844882611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34858889861828857381658069 817005231136613844882611)
                    ·
                      rfl

theorem cell23_4773336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_4773336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773336 prefixEnd_4773336 := by exact prefixLift 4773336
  have htrace : WordTrace (prefixWord ++ tailWord_4773336) baseStart_4773336 baseEnd_4773336 := by
    simpa [prefixWord, tailWord_4773336, baseEnd_4773336] using wordTrace_append hprefix tailTrace_4773336
  have hstable : (prefixWord ++ tailWord_4773336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773336).length < 2 ^ (prefixWord ++ tailWord_4773336).sum := by decide
  have hdescent : baseEnd_4773336 < baseStart_4773336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773357 : List Nat := [1, 5, 1, 3, 2, 1, 1, 4, 5]
def baseStart_4773357 : Nat := 118140960795 + 4773357 * 2 ^ 59
def prefixEnd_4773357 : Nat := 4983230072969 + 3 ^ 40 * 4773357 * 2
def baseEnd_4773357 : Nat := 272336275167065105831693

theorem tailTrace_4773357 : CollatzResearch.WordTrace tailWord_4773357 prefixEnd_4773357 272336275167065105831693 := by
  unfold tailWord_4773357
  simp only [CollatzResearch.WordTrace]
  refine ⟨174098632567950288317374325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116065755045300192211582883 174098632567950288317374325)
  ·
    refine ⟨16321746803245339529753843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174098632567950288317374325 16321746803245339529753843)
    ·
      refine ⟨24482620204868009294630765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16321746803245339529753843 24482620204868009294630765)
      ·
        refine ⟨9180982576825503485486537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24482620204868009294630765 9180982576825503485486537)
        ·
          refine ⟨6885736932619127614114903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9180982576825503485486537 6885736932619127614114903)
          ·
            refine ⟨10328605398928691421172355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6885736932619127614114903 10328605398928691421172355)
            ·
              refine ⟨15492908098393037131758533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10328605398928691421172355 15492908098393037131758533)
              ·
                refine ⟨2904920268448694462204725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15492908098393037131758533 2904920268448694462204725)
                ·
                  refine ⟨272336275167065105831693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2904920268448694462204725 272336275167065105831693)
                  ·
                    rfl

theorem cell23_4773357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_4773357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773357 prefixEnd_4773357 := by exact prefixLift 4773357
  have htrace : WordTrace (prefixWord ++ tailWord_4773357) baseStart_4773357 baseEnd_4773357 := by
    simpa [prefixWord, tailWord_4773357, baseEnd_4773357] using wordTrace_append hprefix tailTrace_4773357
  have hstable : (prefixWord ++ tailWord_4773357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773357).length < 2 ^ (prefixWord ++ tailWord_4773357).sum := by decide
  have hdescent : baseEnd_4773357 < baseStart_4773357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773387 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 2, 5]
def baseStart_4773387 : Nat := 118140960795 + 4773387 * 2 ^ 59
def prefixEnd_4773387 : Nat := 4983230072969 + 3 ^ 40 * 4773387 * 2
def baseEnd_4773387 : Nat := 817013960307740278370033

theorem tailTrace_4773387 : CollatzResearch.WordTrace tailWord_4773387 prefixEnd_4773387 817013960307740278370033 := by
  unfold tailWord_4773387
  simp only [CollatzResearch.WordTrace]
  refine ⟨174099726757841603440966415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116066484505227735627310943 174099726757841603440966415)
  ·
    refine ⟨261149590136762405161449623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174099726757841603440966415 261149590136762405161449623)
    ·
      refine ⟨391724385205143607742174435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261149590136762405161449623 391724385205143607742174435)
      ·
        refine ⟨587586577807715411613261653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391724385205143607742174435 587586577807715411613261653)
        ·
          refine ⟨3442890104342082489921455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 587586577807715411613261653 3442890104342082489921455)
          ·
            refine ⟨5164335156513123734882183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442890104342082489921455 5164335156513123734882183)
            ·
              refine ⟨7746502734769685602323275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5164335156513123734882183 7746502734769685602323275)
              ·
                refine ⟨11619754102154528403484913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7746502734769685602323275 11619754102154528403484913)
                ·
                  refine ⟨8714815576615896302613685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11619754102154528403484913 8714815576615896302613685)
                  ·
                    refine ⟨817013960307740278370033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8714815576615896302613685 817013960307740278370033)
                    ·
                      rfl

theorem cell23_4773387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 2, 5].length) (baseStart_4773387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773387 prefixEnd_4773387 := by exact prefixLift 4773387
  have htrace : WordTrace (prefixWord ++ tailWord_4773387) baseStart_4773387 baseEnd_4773387 := by
    simpa [prefixWord, tailWord_4773387, baseEnd_4773387] using wordTrace_append hprefix tailTrace_4773387
  have hstable : (prefixWord ++ tailWord_4773387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773387).length < 2 ^ (prefixWord ++ tailWord_4773387).sum := by decide
  have hdescent : baseEnd_4773387 < baseStart_4773387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773390 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_4773390 : Nat := 118140960795 + 4773390 * 2 ^ 59
def prefixEnd_4773390 : Nat := 4983230072969 + 3 ^ 40 * 4773390 * 2
def baseEnd_4773390 : Nat := 2451043421365184323372585

theorem tailTrace_4773390 : CollatzResearch.WordTrace tailWord_4773390 prefixEnd_4773390 2451043421365184323372585 := by
  unfold tailWord_4773390
  simp only [CollatzResearch.WordTrace]
  refine ⟨21762479522103841869165703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116066557451220489968883749 21762479522103841869165703)
  ·
    refine ⟨32643719283155762803748555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21762479522103841869165703 32643719283155762803748555)
    ·
      refine ⟨48965578924733644205622833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32643719283155762803748555 48965578924733644205622833)
      ·
        refine ⟨36724184193550233154217125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48965578924733644205622833 36724184193550233154217125)
        ·
          refine ⟨6885784536290668716415711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36724184193550233154217125 6885784536290668716415711)
          ·
            refine ⟨10328676804436003074623567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6885784536290668716415711 10328676804436003074623567)
            ·
              refine ⟨15493015206654004611935351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10328676804436003074623567 15493015206654004611935351)
              ·
                refine ⟨23239522809981006917903027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15493015206654004611935351 23239522809981006917903027)
                ·
                  refine ⟨34859284214971510376854541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23239522809981006917903027 34859284214971510376854541)
                  ·
                    refine ⟨13072231580614316391320453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34859284214971510376854541 13072231580614316391320453)
                    ·
                      refine ⟨2451043421365184323372585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13072231580614316391320453 2451043421365184323372585)
                      ·
                        rfl

theorem cell23_4773390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_4773390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773390 prefixEnd_4773390 := by exact prefixLift 4773390
  have htrace : WordTrace (prefixWord ++ tailWord_4773390) baseStart_4773390 baseEnd_4773390 := by
    simpa [prefixWord, tailWord_4773390, baseEnd_4773390] using wordTrace_append hprefix tailTrace_4773390
  have hstable : (prefixWord ++ tailWord_4773390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773390).length < 2 ^ (prefixWord ++ tailWord_4773390).sum := by decide
  have hdescent : baseEnd_4773390 < baseStart_4773390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773393 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 3]
def baseStart_4773393 : Nat := 118140960795 + 4773393 * 2 ^ 59
def prefixEnd_4773393 : Nat := 4983230072969 + 3 ^ 40 * 4773393 * 2
def baseEnd_4773393 : Nat := 2451044961807147811635071

theorem tailTrace_4773393 : CollatzResearch.WordTrace tailWord_4773393 prefixEnd_4773393 2451044961807147811635071 := by
  unfold tailWord_4773393
  simp only [CollatzResearch.WordTrace]
  refine ⟨174099945595819866465684833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116066630397213244310456555 174099945595819866465684833)
  ·
    refine ⟨130574959196864899849263625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174099945595819866465684833 130574959196864899849263625)
    ·
      refine ⟨97931219397648674886947719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130574959196864899849263625 97931219397648674886947719)
      ·
        refine ⟨146896829096473012330421579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97931219397648674886947719 146896829096473012330421579)
        ·
          refine ⟨220345243644709518495632369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146896829096473012330421579 220345243644709518495632369)
          ·
            refine ⟨165258932733532138871724277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220345243644709518495632369 165258932733532138871724277)
            ·
              refine ⟨15493024943768638019224151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165258932733532138871724277 15493024943768638019224151)
              ·
                refine ⟨23239537415652957028836227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15493024943768638019224151 23239537415652957028836227)
                ·
                  refine ⟨34859306123479435543254341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23239537415652957028836227 34859306123479435543254341)
                  ·
                    refine ⟨6536119898152394164360189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34859306123479435543254341 6536119898152394164360189)
                    ·
                      refine ⟨2451044961807147811635071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6536119898152394164360189 2451044961807147811635071)
                      ·
                        rfl

theorem cell23_4773393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_4773393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773393 prefixEnd_4773393 := by exact prefixLift 4773393
  have htrace : WordTrace (prefixWord ++ tailWord_4773393) baseStart_4773393 baseEnd_4773393 := by
    simpa [prefixWord, tailWord_4773393, baseEnd_4773393] using wordTrace_append hprefix tailTrace_4773393
  have hstable : (prefixWord ++ tailWord_4773393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773393).length < 2 ^ (prefixWord ++ tailWord_4773393).sum := by decide
  have hdescent : baseEnd_4773393 < baseStart_4773393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773410 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_4773410 : Nat := 118140960795 + 4773410 * 2 ^ 59
def prefixEnd_4773410 : Nat := 4983230072969 + 3 ^ 40 * 4773410 * 2
def baseEnd_4773410 : Nat := 2451053690978274245122493

theorem tailTrace_4773410 : CollatzResearch.WordTrace tailWord_4773410 prefixEnd_4773410 2451053690978274245122493 := by
  unfold tailWord_4773410
  simp only [CollatzResearch.WordTrace]
  refine ⟨43525141409189569592263421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116067043757838852246035789 43525141409189569592263421)
  ·
    refine ⟨16321928028446088597098783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43525141409189569592263421 16321928028446088597098783)
    ·
      refine ⟨24482892042669132895648175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16321928028446088597098783 24482892042669132895648175)
      ·
        refine ⟨36724338064003699343472263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24482892042669132895648175 36724338064003699343472263)
        ·
          refine ⟨55086507096005549015208395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36724338064003699343472263 55086507096005549015208395)
          ·
            refine ⟨82629760644008323522812593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55086507096005549015208395 82629760644008323522812593)
            ·
              refine ⟨61972320483006242642109445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82629760644008323522812593 61972320483006242642109445)
              ·
                refine ⟨11619810090563670495395521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61972320483006242642109445 11619810090563670495395521)
                ·
                  refine ⟨8714857567922752871546641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11619810090563670495395521 8714857567922752871546641)
                  ·
                    refine ⟨6536143175942064653659981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8714857567922752871546641 6536143175942064653659981)
                    ·
                      refine ⟨2451053690978274245122493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6536143175942064653659981 2451053690978274245122493)
                      ·
                        rfl

theorem cell23_4773410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_4773410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773410 prefixEnd_4773410 := by exact prefixLift 4773410
  have htrace : WordTrace (prefixWord ++ tailWord_4773410) baseStart_4773410 baseEnd_4773410 := by
    simpa [prefixWord, tailWord_4773410, baseEnd_4773410] using wordTrace_append hprefix tailTrace_4773410
  have hstable : (prefixWord ++ tailWord_4773410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773410).length < 2 ^ (prefixWord ++ tailWord_4773410).sum := by decide
  have hdescent : baseEnd_4773410 < baseStart_4773410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773450 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 1, 5, 2]
def baseStart_4773450 : Nat := 118140960795 + 4773450 * 2 ^ 59
def prefixEnd_4773450 : Nat := 4983230072969 + 3 ^ 40 * 4773450 * 2
def baseEnd_4773450 : Nat := 2451074230204454088622309

theorem tailTrace_4773450 : CollatzResearch.WordTrace tailWord_4773450 prefixEnd_4773450 2451074230204454088622309 := by
  unfold tailWord_4773450
  simp only [CollatzResearch.WordTrace]
  refine ⟨43525506139153341300127451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116068016371075576800339869 43525506139153341300127451)
  ·
    refine ⟨65288259208730011950191177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43525506139153341300127451 65288259208730011950191177)
    ·
      refine ⟨48966194406547508962643383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65288259208730011950191177 48966194406547508962643383)
      ·
        refine ⟨73449291609821263443965075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48966194406547508962643383 73449291609821263443965075)
        ·
          refine ⟨110173937414731895165947613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73449291609821263443965075 110173937414731895165947613)
          ·
            refine ⟨41315226530524460687230355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110173937414731895165947613 41315226530524460687230355)
            ·
              refine ⟨61972839795786691030845533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41315226530524460687230355 61972839795786691030845533)
              ·
                refine ⟨23239814923420009136567075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61972839795786691030845533 23239814923420009136567075)
                ·
                  refine ⟨34859722385130013704850613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23239814923420009136567075 34859722385130013704850613)
                  ·
                    refine ⟨3268098973605938784829745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34859722385130013704850613 3268098973605938784829745)
                    ·
                      refine ⟨2451074230204454088622309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268098973605938784829745 2451074230204454088622309)
                      ·
                        rfl

theorem cell23_4773450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_4773450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773450 prefixEnd_4773450 := by exact prefixLift 4773450
  have htrace : WordTrace (prefixWord ++ tailWord_4773450) baseStart_4773450 baseEnd_4773450 := by
    simpa [prefixWord, tailWord_4773450, baseEnd_4773450] using wordTrace_append hprefix tailTrace_4773450
  have hstable : (prefixWord ++ tailWord_4773450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773450).length < 2 ^ (prefixWord ++ tailWord_4773450).sum := by decide
  have hdescent : baseEnd_4773450 < baseStart_4773450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773460 : List Nat := [2, 4, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_4773460 : Nat := 118140960795 + 4773460 * 2 ^ 59
def prefixEnd_4773460 : Nat := 4983230072969 + 3 ^ 40 * 4773460 * 2
def baseEnd_4773460 : Nat := 817026455003666349832421

theorem tailTrace_4773460 : CollatzResearch.WordTrace tailWord_4773460 prefixEnd_4773460 817026455003666349832421 := by
  unfold tailWord_4773460
  simp only [CollatzResearch.WordTrace]
  refine ⟨87051194643288568454186917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116068259524384757938915889 87051194643288568454186917)
  ·
    refine ⟨16322098995616606585160047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87051194643288568454186917 16322098995616606585160047)
    ·
      refine ⟨24483148493424909877740071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16322098995616606585160047 24483148493424909877740071)
      ·
        refine ⟨36724722740137364816610107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24483148493424909877740071 36724722740137364816610107)
        ·
          refine ⟨55087084110206047224915161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36724722740137364816610107 55087084110206047224915161)
          ·
            refine ⟨41315313082654535418686371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55087084110206047224915161 41315313082654535418686371)
            ·
              refine ⟨61972969623981803128029557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41315313082654535418686371 61972969623981803128029557)
              ·
                refine ⟨5809965902248294043252771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61972969623981803128029557 5809965902248294043252771)
                ·
                  refine ⟨8714948853372441064879157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5809965902248294043252771 8714948853372441064879157)
                  ·
                    refine ⟨817026455003666349832421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8714948853372441064879157 817026455003666349832421)
                    ·
                      rfl

theorem cell23_4773460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_4773460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773460 prefixEnd_4773460 := by exact prefixLift 4773460
  have htrace : WordTrace (prefixWord ++ tailWord_4773460) baseStart_4773460 baseEnd_4773460 := by
    simpa [prefixWord, tailWord_4773460, baseEnd_4773460] using wordTrace_append hprefix tailTrace_4773460
  have hstable : (prefixWord ++ tailWord_4773460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773460).length < 2 ^ (prefixWord ++ tailWord_4773460).sum := by decide
  have hdescent : baseEnd_4773460 < baseStart_4773460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773494 : List Nat := [5, 1, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_4773494 : Nat := 118140960795 + 4773494 * 2 ^ 59
def prefixEnd_4773494 : Nat := 4983230072969 + 3 ^ 40 * 4773494 * 2
def baseEnd_4773494 : Nat := 817032274451083972157369

theorem tailTrace_4773494 : CollatzResearch.WordTrace tailWord_4773494 prefixEnd_4773494 817032274451083972157369 := by
  unfold tailWord_4773494
  simp only [CollatzResearch.WordTrace]
  refine ⟨10881476835528372544694471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116069086245635973810074357 10881476835528372544694471)
  ·
    refine ⟨16322215253292558817041707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10881476835528372544694471 16322215253292558817041707)
    ·
      refine ⟨24483322879938838225562561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16322215253292558817041707 24483322879938838225562561)
      ·
        refine ⟨18362492159954128669171921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24483322879938838225562561 18362492159954128669171921)
        ·
          refine ⟨13771869119965596501878941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18362492159954128669171921 13771869119965596501878941)
          ·
            refine ⟨5164450919987098688204603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13771869119965596501878941 5164450919987098688204603)
            ·
              refine ⟨7746676379980648032306905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5164450919987098688204603 7746676379980648032306905)
              ·
                refine ⟨5810007284985486024230179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7746676379980648032306905 5810007284985486024230179)
                ·
                  refine ⟨8715010927478229036345269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5810007284985486024230179 8715010927478229036345269)
                  ·
                    refine ⟨817032274451083972157369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8715010927478229036345269 817032274451083972157369)
                    ·
                      rfl

theorem cell23_4773494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_4773494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773494 prefixEnd_4773494 := by exact prefixLift 4773494
  have htrace : WordTrace (prefixWord ++ tailWord_4773494) baseStart_4773494 baseEnd_4773494 := by
    simpa [prefixWord, tailWord_4773494, baseEnd_4773494] using wordTrace_append hprefix tailTrace_4773494
  have hstable : (prefixWord ++ tailWord_4773494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773494).length < 2 ^ (prefixWord ++ tailWord_4773494).sum := by decide
  have hdescent : baseEnd_4773494 < baseStart_4773494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773497 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 5, 2, 2]
def baseStart_4773497 : Nat := 118140960795 + 4773497 * 2 ^ 59
def prefixEnd_4773497 : Nat := 4983230072969 + 3 ^ 40 * 4773497 * 2
def baseEnd_4773497 : Nat := 2451098363795215404734593

theorem tailTrace_4773497 : CollatzResearch.WordTrace tailWord_4773497 prefixEnd_4773497 2451098363795215404734593 := by
  unfold tailWord_4773497
  simp only [CollatzResearch.WordTrace]
  refine ⟨174103738787443092227470745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116069159191628728151647163 174103738787443092227470745)
  ·
    refine ⟨130577804090582319170603059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174103738787443092227470745 130577804090582319170603059)
    ·
      refine ⟨195866706135873478755904589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130577804090582319170603059 195866706135873478755904589)
      ·
        refine ⟨73450014800952554533464221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195866706135873478755904589 73450014800952554533464221)
        ·
          refine ⟨27543755550357207950049083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73450014800952554533464221 27543755550357207950049083)
          ·
            refine ⟨41315633325535811925073625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27543755550357207950049083 41315633325535811925073625)
            ·
              refine ⟨30986724994151858943805219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41315633325535811925073625 30986724994151858943805219)
              ·
                refine ⟨46480087491227788415707829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30986724994151858943805219 46480087491227788415707829)
                ·
                  refine ⟨4357508202302605163972609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46480087491227788415707829 4357508202302605163972609)
                  ·
                    refine ⟨3268131151726953872979457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4357508202302605163972609 3268131151726953872979457)
                    ·
                      refine ⟨2451098363795215404734593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3268131151726953872979457 2451098363795215404734593)
                      ·
                        rfl

theorem cell23_4773497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_4773497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773497 prefixEnd_4773497 := by exact prefixLift 4773497
  have htrace : WordTrace (prefixWord ++ tailWord_4773497) baseStart_4773497 baseEnd_4773497 := by
    simpa [prefixWord, tailWord_4773497, baseEnd_4773497] using wordTrace_append hprefix tailTrace_4773497
  have hstable : (prefixWord ++ tailWord_4773497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773497).length < 2 ^ (prefixWord ++ tailWord_4773497).sum := by decide
  have hdescent : baseEnd_4773497 < baseStart_4773497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
