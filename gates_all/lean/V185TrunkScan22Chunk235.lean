import V185TrunkScan22Chunk234

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2095274 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2095274 : Nat := 118140960795 + 2095274 * 2 ^ 59
def prefixEnd_2095274 : Nat := 4983230072969 + 3 ^ 40 * 2095274 * 2
def baseEnd_2095274 : Nat := 717255109912493643026011

theorem tailTrace_2095274 : CollatzResearch.WordTrace tailWord_2095274 prefixEnd_2095274 717255109912493643026011 := by
  unfold tailWord_2095274
  simp only [CollatzResearch.WordTrace]
  refine ⟨19105230252796904288717219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50947280674125078103245917 19105230252796904288717219)
  ·
    refine ⟨28657845379195356433075829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19105230252796904288717219 28657845379195356433075829)
    ·
      refine ⟨2686673004299564665600859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28657845379195356433075829 2686673004299564665600859)
      ·
        refine ⟨4030009506449346998401289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2686673004299564665600859 4030009506449346998401289)
        ·
          refine ⟨3022507129837010248800967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4030009506449346998401289 3022507129837010248800967)
          ·
            refine ⟨4533760694755515373201451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022507129837010248800967 4533760694755515373201451)
            ·
              refine ⟨6800641042133273059802177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533760694755515373201451 6800641042133273059802177)
              ·
                refine ⟨5100480781599954794851633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6800641042133273059802177 5100480781599954794851633)
                ·
                  refine ⟨3825360586199966096138725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5100480781599954794851633 3825360586199966096138725)
                  ·
                    refine ⟨717255109912493643026011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3825360586199966096138725 717255109912493643026011)
                    ·
                      rfl

theorem cell22_2095274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2095274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095274 prefixEnd_2095274 := by exact prefixLift 2095274
  have htrace : WordTrace (prefixWord ++ tailWord_2095274) baseStart_2095274 baseEnd_2095274 := by
    simpa [prefixWord, tailWord_2095274, baseEnd_2095274] using wordTrace_append hprefix tailTrace_2095274
  have hstable : (prefixWord ++ tailWord_2095274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095274).length < 2 ^ (prefixWord ++ tailWord_2095274).sum := by decide
  have hdescent : baseEnd_2095274 < baseStart_2095274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095278 : List Nat := [4, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_2095278 : Nat := 118140960795 + 2095278 * 2 ^ 59
def prefixEnd_2095278 : Nat := 4983230072969 + 3 ^ 40 * 2095278 * 2
def baseEnd_2095278 : Nat := 239085493064746321975333

theorem tailTrace_2095278 : CollatzResearch.WordTrace tailWord_2095278 prefixEnd_2095278 239085493064746321975333 := by
  unfold tailWord_2095278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9552633362896640729751811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50947377935448750558676325 9552633362896640729751811)
  ·
    refine ⟨14328950044344961094627717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9552633362896640729751811 14328950044344961094627717)
    ·
      refine ⟨2686678133314680205242697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14328950044344961094627717 2686678133314680205242697)
      ·
        refine ⟨2015008599986010153932023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2686678133314680205242697 2015008599986010153932023)
        ·
          refine ⟨3022512899979015230898035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015008599986010153932023 3022512899979015230898035)
          ·
            refine ⟨4533769349968522846347053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022512899979015230898035 4533769349968522846347053)
            ·
              refine ⟨1700163506238196067380145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4533769349968522846347053 1700163506238196067380145)
              ·
                refine ⟨1275122629678647050535109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1700163506238196067380145 1275122629678647050535109)
                ·
                  refine ⟨239085493064746321975333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1275122629678647050535109 239085493064746321975333)
                  ·
                    rfl

theorem cell22_2095278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_2095278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095278 prefixEnd_2095278 := by exact prefixLift 2095278
  have htrace : WordTrace (prefixWord ++ tailWord_2095278) baseStart_2095278 baseEnd_2095278 := by
    simpa [prefixWord, tailWord_2095278, baseEnd_2095278] using wordTrace_append hprefix tailTrace_2095278
  have hstable : (prefixWord ++ tailWord_2095278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095278).length < 2 ^ (prefixWord ++ tailWord_2095278).sum := by decide
  have hdescent : baseEnd_2095278 < baseStart_2095278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095287 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 3, 3]
def baseStart_2095287 : Nat := 118140960795 + 2095287 * 2 ^ 59
def prefixEnd_2095287 : Nat := 4983230072969 + 3 ^ 40 * 2095287 * 2
def baseEnd_2095287 : Nat := 717259560078165942450971

theorem tailTrace_2095287 : CollatzResearch.WordTrace tailWord_2095287 prefixEnd_2095287 717259560078165942450971 := by
  unfold tailWord_2095287
  simp only [CollatzResearch.WordTrace]
  refine ⟨76421395160140520375092115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50947596773427013583394743 76421395160140520375092115)
  ·
    refine ⟨114632092740210780562638173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76421395160140520375092115 114632092740210780562638173)
    ·
      refine ⟨42987034777579042710989315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114632092740210780562638173 42987034777579042710989315)
      ·
        refine ⟨64480552166368564066483973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42987034777579042710989315 64480552166368564066483973)
        ·
          refine ⟨12090103531194105762465745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64480552166368564066483973 12090103531194105762465745)
          ·
            refine ⟨9067577648395579321849309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12090103531194105762465745 9067577648395579321849309)
            ·
              refine ⟨3400341618148342245693491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9067577648395579321849309 3400341618148342245693491)
              ·
                refine ⟨5100512427222513368540237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400341618148342245693491 5100512427222513368540237)
                ·
                  refine ⟨1912692160208442513202589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5100512427222513368540237 1912692160208442513202589)
                  ·
                    refine ⟨717259560078165942450971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1912692160208442513202589 717259560078165942450971)
                    ·
                      rfl

theorem cell22_2095287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_2095287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095287 prefixEnd_2095287 := by exact prefixLift 2095287
  have htrace : WordTrace (prefixWord ++ tailWord_2095287) baseStart_2095287 baseEnd_2095287 := by
    simpa [prefixWord, tailWord_2095287, baseEnd_2095287] using wordTrace_append hprefix tailTrace_2095287
  have hstable : (prefixWord ++ tailWord_2095287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095287).length < 2 ^ (prefixWord ++ tailWord_2095287).sum := by decide
  have hdescent : baseEnd_2095287 < baseStart_2095287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095360 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 1, 5]
def baseStart_2095360 : Nat := 118140960795 + 2095360 * 2 ^ 59
def prefixEnd_2095360 : Nat := 4983230072969 + 3 ^ 40 * 2095360 * 2
def baseEnd_2095360 : Nat := 717284549470018085375747

theorem tailTrace_2095360 : CollatzResearch.WordTrace tailWord_2095360 prefixEnd_2095360 717284549470018085375747 := by
  unfold tailWord_2095360
  simp only [CollatzResearch.WordTrace]
  refine ⟨38212028844438026921249767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50949371792584035894999689 38212028844438026921249767)
  ·
    refine ⟨57318043266657040381874651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38212028844438026921249767 57318043266657040381874651)
    ·
      refine ⟨85977064899985560572811977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57318043266657040381874651 85977064899985560572811977)
      ·
        refine ⟨64482798674989170429608983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85977064899985560572811977 64482798674989170429608983)
        ·
          refine ⟨96724198012483755644413475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64482798674989170429608983 96724198012483755644413475)
          ·
            refine ⟨145086297018725633466620213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96724198012483755644413475 145086297018725633466620213)
            ·
              refine ⟨13601840345505528137495645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145086297018725633466620213 13601840345505528137495645)
              ·
                refine ⟨5100690129564573051560867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13601840345505528137495645 5100690129564573051560867)
                ·
                  refine ⟨7651035194346859577341301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100690129564573051560867 7651035194346859577341301)
                  ·
                    refine ⟨717284549470018085375747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7651035194346859577341301 717284549470018085375747)
                    ·
                      rfl

theorem cell22_2095360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_2095360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095360 prefixEnd_2095360 := by exact prefixLift 2095360
  have htrace : WordTrace (prefixWord ++ tailWord_2095360) baseStart_2095360 baseEnd_2095360 := by
    simpa [prefixWord, tailWord_2095360, baseEnd_2095360] using wordTrace_append hprefix tailTrace_2095360
  have hstable : (prefixWord ++ tailWord_2095360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095360).length < 2 ^ (prefixWord ++ tailWord_2095360).sum := by decide
  have hdescent : baseEnd_2095360 < baseStart_2095360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095362 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 8]
def baseStart_2095362 : Nat := 118140960795 + 2095362 * 2 ^ 59
def prefixEnd_2095362 : Nat := 4983230072969 + 3 ^ 40 * 2095362 * 2
def baseEnd_2095362 : Nat := 239095078036963582275247

theorem tailTrace_2095362 : CollatzResearch.WordTrace tailWord_2095362 prefixEnd_2095362 239095078036963582275247 := by
  unfold tailWord_2095362
  simp only [CollatzResearch.WordTrace]
  refine ⟨19106032658717202046018085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50949420423245872122714893 19106032658717202046018085)
  ·
    refine ⟨3582381123509475383628391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19106032658717202046018085 3582381123509475383628391)
    ·
      refine ⟨5373571685264213075442587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3582381123509475383628391 5373571685264213075442587)
      ·
        refine ⟨8060357527896319613163881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373571685264213075442587 8060357527896319613163881)
        ·
          refine ⟨6045268145922239709872911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8060357527896319613163881 6045268145922239709872911)
          ·
            refine ⟨9067902218883359564809367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6045268145922239709872911 9067902218883359564809367)
            ·
              refine ⟨13601853328325039347214051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9067902218883359564809367 13601853328325039347214051)
              ·
                refine ⟨20402779992487559020821077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13601853328325039347214051 20402779992487559020821077)
                ·
                  refine ⟨239095078036963582275247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20402779992487559020821077 239095078036963582275247)
                  ·
                    rfl

theorem cell22_2095362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_2095362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095362 prefixEnd_2095362 := by exact prefixLift 2095362
  have htrace : WordTrace (prefixWord ++ tailWord_2095362) baseStart_2095362 baseEnd_2095362 := by
    simpa [prefixWord, tailWord_2095362, baseEnd_2095362] using wordTrace_append hprefix tailTrace_2095362
  have hstable : (prefixWord ++ tailWord_2095362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095362).length < 2 ^ (prefixWord ++ tailWord_2095362).sum := by decide
  have hdescent : baseEnd_2095362 < baseStart_2095362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095394 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2095394 : Nat := 118140960795 + 2095394 * 2 ^ 59
def prefixEnd_2095394 : Nat := 4983230072969 + 3 ^ 40 * 2095394 * 2
def baseEnd_2095394 : Nat := 717296188364853330025643

theorem tailTrace_2095394 : CollatzResearch.WordTrace tailWord_2095394 prefixEnd_2095394 717296188364853330025643 := by
  unfold tailWord_2095394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19106324442688219412309309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50950198513835251766158157 19106324442688219412309309)
  ·
    refine ⟨7164871666008082279615991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19106324442688219412309309 7164871666008082279615991)
    ·
      refine ⟨10747307499012123419423987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7164871666008082279615991 10747307499012123419423987)
      ·
        refine ⟨16120961248518185129135981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10747307499012123419423987 16120961248518185129135981)
        ·
          refine ⟨6045360468194319423425993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16120961248518185129135981 6045360468194319423425993)
          ·
            refine ⟨4534020351145739567569495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6045360468194319423425993 4534020351145739567569495)
            ·
              refine ⟨6801030526718609351354243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4534020351145739567569495 6801030526718609351354243)
              ·
                refine ⟨10201545790077914027031365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6801030526718609351354243 10201545790077914027031365)
                ·
                  refine ⟨1912789835639608880068381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10201545790077914027031365 1912789835639608880068381)
                  ·
                    refine ⟨717296188364853330025643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1912789835639608880068381 717296188364853330025643)
                    ·
                      rfl

theorem cell22_2095394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2095394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095394 prefixEnd_2095394 := by exact prefixLift 2095394
  have htrace : WordTrace (prefixWord ++ tailWord_2095394) baseStart_2095394 baseEnd_2095394 := by
    simpa [prefixWord, tailWord_2095394, baseEnd_2095394] using wordTrace_append hprefix tailTrace_2095394
  have hstable : (prefixWord ++ tailWord_2095394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095394).length < 2 ^ (prefixWord ++ tailWord_2095394).sum := by decide
  have hdescent : baseEnd_2095394 < baseStart_2095394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095439 : List Nat := [1, 1, 2, 1, 1, 2, 1, 9, 1, 3]
def baseStart_2095439 : Nat := 118140960795 + 2095439 * 2 ^ 59
def prefixEnd_2095439 : Nat := 4983230072969 + 3 ^ 40 * 2095439 * 2
def baseEnd_2095439 : Nat := 717311592784488212650505

theorem tailTrace_2095439 : CollatzResearch.WordTrace tailWord_2095439 prefixEnd_2095439 717311592784488212650505 := by
  unfold tailWord_2095439
  simp only [CollatzResearch.WordTrace]
  refine ⟨76426939055589850334625371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50951292703726566889750247 76426939055589850334625371)
  ·
    refine ⟨114640408583384775501938057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76426939055589850334625371 114640408583384775501938057)
    ·
      refine ⟨85980306437538581626453543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114640408583384775501938057 85980306437538581626453543)
      ·
        refine ⟨128970459656307872439680315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85980306437538581626453543 128970459656307872439680315)
        ·
          refine ⟨193455689484461808659520473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128970459656307872439680315 193455689484461808659520473)
          ·
            refine ⟨145091767113346356494640355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193455689484461808659520473 145091767113346356494640355)
            ·
              refine ⟨217637650670019534741960533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145091767113346356494640355 217637650670019534741960533)
              ·
                refine ⟨1275220609394645711378675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 217637650670019534741960533 1275220609394645711378675)
                ·
                  refine ⟨1912830914091968567068013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275220609394645711378675 1912830914091968567068013)
                  ·
                    refine ⟨717311592784488212650505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1912830914091968567068013 717311592784488212650505)
                    ·
                      rfl

theorem cell22_2095439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 1, 3].length) (baseStart_2095439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095439 prefixEnd_2095439 := by exact prefixLift 2095439
  have htrace : WordTrace (prefixWord ++ tailWord_2095439) baseStart_2095439 baseEnd_2095439 := by
    simpa [prefixWord, tailWord_2095439, baseEnd_2095439] using wordTrace_append hprefix tailTrace_2095439
  have hstable : (prefixWord ++ tailWord_2095439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095439).length < 2 ^ (prefixWord ++ tailWord_2095439).sum := by decide
  have hdescent : baseEnd_2095439 < baseStart_2095439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095456 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 3, 3]
def baseStart_2095456 : Nat := 118140960795 + 2095456 * 2 ^ 59
def prefixEnd_2095456 : Nat := 4983230072969 + 3 ^ 40 * 2095456 * 2
def baseEnd_2095456 : Nat := 717317412231905834975453

theorem tailTrace_2095456 : CollatzResearch.WordTrace tailWord_2095456 prefixEnd_2095456 717317412231905834975453 := by
  unfold tailWord_2095456
  simp only [CollatzResearch.WordTrace]
  refine ⟨38213779548264131118997111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50951706064352174825329481 38213779548264131118997111)
  ·
    refine ⟨57320669322396196678495667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38213779548264131118997111 57320669322396196678495667)
    ·
      refine ⟨85981003983594295017743501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57320669322396196678495667 85981003983594295017743501)
      ·
        refine ⟨32242876493847860631653813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85981003983594295017743501 32242876493847860631653813)
        ·
          refine ⟨3022769671298236934217545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32242876493847860631653813 3022769671298236934217545)
          ·
            refine ⟨2267077253473677700663159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3022769671298236934217545 2267077253473677700663159)
            ·
              refine ⟨3400615880210516550994739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267077253473677700663159 3400615880210516550994739)
              ·
                refine ⟨5100923820315774826492109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400615880210516550994739 5100923820315774826492109)
                ·
                  refine ⟨1912846432618415559934541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5100923820315774826492109 1912846432618415559934541)
                  ·
                    refine ⟨717317412231905834975453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1912846432618415559934541 717317412231905834975453)
                    ·
                      rfl

theorem cell22_2095456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 3, 3].length) (baseStart_2095456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095456 prefixEnd_2095456 := by exact prefixLift 2095456
  have htrace : WordTrace (prefixWord ++ tailWord_2095456) baseStart_2095456 baseEnd_2095456 := by
    simpa [prefixWord, tailWord_2095456, baseEnd_2095456] using wordTrace_append hprefix tailTrace_2095456
  have hstable : (prefixWord ++ tailWord_2095456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095456).length < 2 ^ (prefixWord ++ tailWord_2095456).sum := by decide
  have hdescent : baseEnd_2095456 < baseStart_2095456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095651 : List Nat := [1, 1, 1, 4, 4, 1, 3, 2, 1, 4]
def baseStart_2095651 : Nat := 118140960795 + 2095651 * 2 ^ 59
def prefixEnd_2095651 : Nat := 4983230072969 + 3 ^ 40 * 2095651 * 2
def baseEnd_2095651 : Nat := 717384164716990326349855

theorem tailTrace_2095651 : CollatzResearch.WordTrace tailWord_2095651 prefixEnd_2095651 717384164716990326349855 := by
  unfold tailWord_2095651
  simp only [CollatzResearch.WordTrace]
  refine ⟨76434671330821810541342807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50956447553881207027561871 76434671330821810541342807)
  ·
    refine ⟨114652006996232715812014211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76434671330821810541342807 114652006996232715812014211)
    ·
      refine ⟨171978010494349073718021317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114652006996232715812014211 171978010494349073718021317)
      ·
        refine ⟨32245876967690451322128997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171978010494349073718021317 32245876967690451322128997)
        ·
          refine ⟨6046101931441959622899187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32245876967690451322128997 6046101931441959622899187)
          ·
            refine ⟨9069152897162939434348781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6046101931441959622899187 9069152897162939434348781)
            ·
              refine ⟨3400932336436102287880793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9069152897162939434348781 3400932336436102287880793)
              ·
                refine ⟨2550699252327076715910595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400932336436102287880793 2550699252327076715910595)
                ·
                  refine ⟨3826048878490615073865893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550699252327076715910595 3826048878490615073865893)
                  ·
                    refine ⟨717384164716990326349855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826048878490615073865893 717384164716990326349855)
                    ·
                      rfl

theorem cell22_2095651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 4].length) (baseStart_2095651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095651 prefixEnd_2095651 := by exact prefixLift 2095651
  have htrace : WordTrace (prefixWord ++ tailWord_2095651) baseStart_2095651 baseEnd_2095651 := by
    simpa [prefixWord, tailWord_2095651, baseEnd_2095651] using wordTrace_append hprefix tailTrace_2095651
  have hstable : (prefixWord ++ tailWord_2095651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095651).length < 2 ^ (prefixWord ++ tailWord_2095651).sum := by decide
  have hdescent : baseEnd_2095651 < baseStart_2095651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095664 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 6, 3]
def baseStart_2095664 : Nat := 118140960795 + 2095664 * 2 ^ 59
def prefixEnd_2095664 : Nat := 4983230072969 + 3 ^ 40 * 2095664 * 2
def baseEnd_2095664 : Nat := 717388614882662625774815

theorem tailTrace_2095664 : CollatzResearch.WordTrace tailWord_2095664 prefixEnd_2095664 717388614882662625774815 := by
  unfold tailWord_2095664
  simp only [CollatzResearch.WordTrace]
  refine ⟨38217572739887356880783023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50956763653183142507710697 38217572739887356880783023)
  ·
    refine ⟨57326359109831035321174535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38217572739887356880783023 57326359109831035321174535)
    ·
      refine ⟨85989538664746552981761803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57326359109831035321174535 85989538664746552981761803)
      ·
        refine ⟨128984307997119829472642705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85989538664746552981761803 128984307997119829472642705)
        ·
          refine ⟨96738230997839872104482029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128984307997119829472642705 96738230997839872104482029)
          ·
            refine ⟨36276836624189952039180761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96738230997839872104482029 36276836624189952039180761)
            ·
              refine ⟨27207627468142464029385571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36276836624189952039180761 27207627468142464029385571)
              ·
                refine ⟨40811441202213696044078357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27207627468142464029385571 40811441202213696044078357)
                ·
                  refine ⟨1913036306353767002066173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40811441202213696044078357 1913036306353767002066173)
                  ·
                    refine ⟨717388614882662625774815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1913036306353767002066173 717388614882662625774815)
                    ·
                      rfl

theorem cell22_2095664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6, 3].length) (baseStart_2095664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095664 prefixEnd_2095664 := by exact prefixLift 2095664
  have htrace : WordTrace (prefixWord ++ tailWord_2095664) baseStart_2095664 baseEnd_2095664 := by
    simpa [prefixWord, tailWord_2095664, baseEnd_2095664] using wordTrace_append hprefix tailTrace_2095664
  have hstable : (prefixWord ++ tailWord_2095664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095664).length < 2 ^ (prefixWord ++ tailWord_2095664).sum := by decide
  have hdescent : baseEnd_2095664 < baseStart_2095664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095679 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 2, 4]
def baseStart_2095679 : Nat := 118140960795 + 2095679 * 2 ^ 59
def prefixEnd_2095679 : Nat := 4983230072969 + 3 ^ 40 * 2095679 * 2
def baseEnd_2095679 : Nat := 717393749689207586649769

theorem tailTrace_2095679 : CollatzResearch.WordTrace tailWord_2095679 prefixEnd_2095679 717393749689207586649769 := by
  unfold tailWord_2095679
  simp only [CollatzResearch.WordTrace]
  refine ⟨76435692574720371323362091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50957128383146914215574727 76435692574720371323362091)
  ·
    refine ⟨114653538862080556985043137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76435692574720371323362091 114653538862080556985043137)
    ·
      refine ⟨85990154146560417738782353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114653538862080556985043137 85990154146560417738782353)
      ·
        refine ⟨64492615609920313304086765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85990154146560417738782353 64492615609920313304086765)
        ·
          refine ⟨24184730853720117489032537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64492615609920313304086765 24184730853720117489032537)
          ·
            refine ⟨18138548140290088116774403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24184730853720117489032537 18138548140290088116774403)
            ·
              refine ⟨27207822210435132175161605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18138548140290088116774403 27207822210435132175161605)
              ·
                refine ⟨5101466664456587282842801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27207822210435132175161605 5101466664456587282842801)
                ·
                  refine ⟨3826099998342440462132101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5101466664456587282842801 3826099998342440462132101)
                  ·
                    refine ⟨717393749689207586649769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826099998342440462132101 717393749689207586649769)
                    ·
                      rfl

theorem cell22_2095679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_2095679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095679 prefixEnd_2095679 := by exact prefixLift 2095679
  have htrace : WordTrace (prefixWord ++ tailWord_2095679) baseStart_2095679 baseEnd_2095679 := by
    simpa [prefixWord, tailWord_2095679, baseEnd_2095679] using wordTrace_append hprefix tailTrace_2095679
  have hstable : (prefixWord ++ tailWord_2095679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095679).length < 2 ^ (prefixWord ++ tailWord_2095679).sum := by decide
  have hdescent : baseEnd_2095679 < baseStart_2095679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095694 : List Nat := [4, 1, 1, 1, 1, 2, 5, 7]
def baseStart_2095694 : Nat := 118140960795 + 2095694 * 2 ^ 59
def prefixEnd_2095694 : Nat := 4983230072969 + 3 ^ 40 * 2095694 * 2
def baseEnd_2095694 : Nat := 79710987166194727502747

theorem tailTrace_2095694 : CollatzResearch.WordTrace tailWord_2095694 prefixEnd_2095694 79710987166194727502747 := by
  unfold tailWord_2095694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9554529958708253610644767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50957493113110685923438757 9554529958708253610644767)
  ·
    refine ⟨14331794938062380415967151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9554529958708253610644767 14331794938062380415967151)
    ·
      refine ⟨21497692407093570623950727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14331794938062380415967151 21497692407093570623950727)
      ·
        refine ⟨32246538610640355935926091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21497692407093570623950727 32246538610640355935926091)
        ·
          refine ⟨48369807915960533903889137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32246538610640355935926091 48369807915960533903889137)
          ·
            refine ⟨36277355936970400427916853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48369807915960533903889137 36277355936970400427916853)
            ·
              refine ⟨3401002119090975040117205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36277355936970400427916853 3401002119090975040117205)
              ·
                refine ⟨79710987166194727502747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3401002119090975040117205 79710987166194727502747)
                ·
                  rfl

theorem cell22_2095694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_2095694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095694 prefixEnd_2095694 := by exact prefixLift 2095694
  have htrace : WordTrace (prefixWord ++ tailWord_2095694) baseStart_2095694 baseEnd_2095694 := by
    simpa [prefixWord, tailWord_2095694, baseEnd_2095694] using wordTrace_append hprefix tailTrace_2095694
  have hstable : (prefixWord ++ tailWord_2095694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095694).length < 2 ^ (prefixWord ++ tailWord_2095694).sum := by decide
  have hdescent : baseEnd_2095694 < baseStart_2095694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095739 : List Nat := [1, 1, 1, 1, 1, 4, 2, 6, 5]
def baseStart_2095739 : Nat := 118140960795 + 2095739 * 2 ^ 59
def prefixEnd_2095739 : Nat := 4983230072969 + 3 ^ 40 * 2095739 * 2
def baseEnd_2095739 : Nat := 239138096305129143383195

theorem tailTrace_2095739 : CollatzResearch.WordTrace tailWord_2095739 prefixEnd_2095739 239138096305129143383195 := by
  unfold tailWord_2095739
  simp only [CollatzResearch.WordTrace]
  refine ⟨76437880954503001570546271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50958587303002001047030847 76437880954503001570546271)
  ·
    refine ⟨114656821431754502355819407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76437880954503001570546271 114656821431754502355819407)
    ·
      refine ⟨171985232147631753533729111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114656821431754502355819407 171985232147631753533729111)
      ·
        refine ⟨257977848221447630300593667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171985232147631753533729111 257977848221447630300593667)
        ·
          refine ⟨386966772332171445450890501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257977848221447630300593667 386966772332171445450890501)
          ·
            refine ⟨72556269812282146022041969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386966772332171445450890501 72556269812282146022041969)
            ·
              refine ⟨54417202359211609516531477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72556269812282146022041969 54417202359211609516531477)
              ·
                refine ⟨2550806360588044196087413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54417202359211609516531477 2550806360588044196087413)
                ·
                  refine ⟨239138096305129143383195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2550806360588044196087413 239138096305129143383195)
                  ·
                    rfl

theorem cell22_2095739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 5].length) (baseStart_2095739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095739 prefixEnd_2095739 := by exact prefixLift 2095739
  have htrace : WordTrace (prefixWord ++ tailWord_2095739) baseStart_2095739 baseEnd_2095739 := by
    simpa [prefixWord, tailWord_2095739, baseEnd_2095739] using wordTrace_append hprefix tailTrace_2095739
  have hstable : (prefixWord ++ tailWord_2095739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095739).length < 2 ^ (prefixWord ++ tailWord_2095739).sum := by decide
  have hdescent : baseEnd_2095739 < baseStart_2095739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095777 : List Nat := [1, 2, 3, 3, 3, 2, 1, 3, 1, 3]
def baseStart_2095777 : Nat := 118140960795 + 2095777 * 2 ^ 59
def prefixEnd_2095777 : Nat := 4983230072969 + 3 ^ 40 * 2095777 * 2
def baseEnd_2095777 : Nat := 717427297091967997699469

theorem tailTrace_2095777 : CollatzResearch.WordTrace tailWord_2095777 prefixEnd_2095777 717427297091967997699469 := by
  unfold tailWord_2095777
  simp only [CollatzResearch.WordTrace]
  refine ⟨76439266928365334060429585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50959511285576889373619723 76439266928365334060429585)
  ·
    refine ⟨57329450196274000545322189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76439266928365334060429585 57329450196274000545322189)
    ·
      refine ⟨21498543823602750204495821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57329450196274000545322189 21498543823602750204495821)
      ·
        refine ⟨8061953933851031326685933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21498543823602750204495821 8061953933851031326685933)
        ·
          refine ⟨3023232725194136747507225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8061953933851031326685933 3023232725194136747507225)
          ·
            refine ⟨2267424543895602560630419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3023232725194136747507225 2267424543895602560630419)
            ·
              refine ⟨3401136815843403840945629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267424543895602560630419 3401136815843403840945629)
              ·
                refine ⟨1275426305941276440354611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3401136815843403840945629 1275426305941276440354611)
                ·
                  refine ⟨1913139458911914660531917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275426305941276440354611 1913139458911914660531917)
                  ·
                    refine ⟨717427297091967997699469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1913139458911914660531917 717427297091967997699469)
                    ·
                      rfl

theorem cell22_2095777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_2095777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095777 prefixEnd_2095777 := by exact prefixLift 2095777
  have htrace : WordTrace (prefixWord ++ tailWord_2095777) baseStart_2095777 baseEnd_2095777 := by
    simpa [prefixWord, tailWord_2095777, baseEnd_2095777] using wordTrace_append hprefix tailTrace_2095777
  have hstable : (prefixWord ++ tailWord_2095777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095777).length < 2 ^ (prefixWord ++ tailWord_2095777).sum := by decide
  have hdescent : baseEnd_2095777 < baseStart_2095777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095820 : List Nat := [2, 2, 1, 5, 1, 3, 1, 2, 1, 4]
def baseStart_2095820 : Nat := 118140960795 + 2095820 * 2 ^ 59
def prefixEnd_2095820 : Nat := 4983230072969 + 3 ^ 40 * 2095820 * 2
def baseEnd_2095820 : Nat := 717442016870730218874337

theorem tailTrace_2095820 : CollatzResearch.WordTrace tailWord_2095820 prefixEnd_2095820 717442016870730218874337 := by
  unfold tailWord_2095820
  simp only [CollatzResearch.WordTrace]
  refine ⟨38220417633604776202122457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50960556844806368269496609 38220417633604776202122457)
  ·
    refine ⟨28665313225203582151591843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38220417633604776202122457 28665313225203582151591843)
    ·
      refine ⟨42997969837805373227387765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28665313225203582151591843 42997969837805373227387765)
      ·
        refine ⟨4031059672294253740067603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42997969837805373227387765 4031059672294253740067603)
        ·
          refine ⟨6046589508441380610101405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031059672294253740067603 6046589508441380610101405)
          ·
            refine ⟨2267471065665517728788027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6046589508441380610101405 2267471065665517728788027)
            ·
              refine ⟨3401206598498276593182041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267471065665517728788027 3401206598498276593182041)
              ·
                refine ⟨2550904948873707444886531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3401206598498276593182041 2550904948873707444886531)
                ·
                  refine ⟨3826357423310561167329797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550904948873707444886531 3826357423310561167329797)
                  ·
                    refine ⟨717442016870730218874337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826357423310561167329797 717442016870730218874337)
                    ·
                      rfl

theorem cell22_2095820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_2095820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095820 prefixEnd_2095820 := by exact prefixLift 2095820
  have htrace : WordTrace (prefixWord ++ tailWord_2095820) baseStart_2095820 baseEnd_2095820 := by
    simpa [prefixWord, tailWord_2095820, baseEnd_2095820] using wordTrace_append hprefix tailTrace_2095820
  have hstable : (prefixWord ++ tailWord_2095820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095820).length < 2 ^ (prefixWord ++ tailWord_2095820).sum := by decide
  have hdescent : baseEnd_2095820 < baseStart_2095820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095831 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 2, 4]
def baseStart_2095831 : Nat := 118140960795 + 2095831 * 2 ^ 59
def prefixEnd_2095831 : Nat := 4983230072969 + 3 ^ 40 * 2095831 * 2
def baseEnd_2095831 : Nat := 717445782395529856849303

theorem tailTrace_2095831 : CollatzResearch.WordTrace tailWord_2095831 prefixEnd_2095831 717445782395529856849303 := by
  unfold tailWord_2095831
  simp only [CollatzResearch.WordTrace]
  refine ⟨76441236470169701282895347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50960824313446467521930231 76441236470169701282895347)
  ·
    refine ⟨114661854705254551924343021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76441236470169701282895347 114661854705254551924343021)
    ·
      refine ⟨42998195514470456971628633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114661854705254551924343021 42998195514470456971628633)
      ·
        refine ⟨32248646635852842728721475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42998195514470456971628633 32248646635852842728721475)
        ·
          refine ⟨48372969953779264093082213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32248646635852842728721475 48372969953779264093082213)
          ·
            refine ⟨9069931866333612017452915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48372969953779264093082213 9069931866333612017452915)
            ·
              refine ⟨13604897799500418026179373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9069931866333612017452915 13604897799500418026179373)
              ·
                refine ⟨5101836674812656759817265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13604897799500418026179373 5101836674812656759817265)
                ·
                  refine ⟨3826377506109492569862949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5101836674812656759817265 3826377506109492569862949)
                  ·
                    refine ⟨717445782395529856849303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826377506109492569862949 717445782395529856849303)
                    ·
                      rfl

theorem cell22_2095831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_2095831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095831 prefixEnd_2095831 := by exact prefixLift 2095831
  have htrace : WordTrace (prefixWord ++ tailWord_2095831) baseStart_2095831 baseEnd_2095831 := by
    simpa [prefixWord, tailWord_2095831, baseEnd_2095831] using wordTrace_append hprefix tailTrace_2095831
  have hstable : (prefixWord ++ tailWord_2095831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095831).length < 2 ^ (prefixWord ++ tailWord_2095831).sum := by decide
  have hdescent : baseEnd_2095831 < baseStart_2095831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095876 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_2095876 : Nat := 118140960795 + 2095876 * 2 ^ 59
def prefixEnd_2095876 : Nat := 4983230072969 + 3 ^ 40 * 2095876 * 2
def baseEnd_2095876 : Nat := 717461186815164739474165

theorem tailTrace_2095876 : CollatzResearch.WordTrace tailWord_2095876 prefixEnd_2095876 717461186815164739474165 := by
  unfold tailWord_2095876
  simp only [CollatzResearch.WordTrace]
  refine ⟨38221438877503336984141741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50961918503337782645522321 38221438877503336984141741)
  ·
    refine ⟨14333039579063751369053153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38221438877503336984141741 14333039579063751369053153)
    ·
      refine ⟨10749779684297813526789865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14333039579063751369053153 10749779684297813526789865)
      ·
        refine ⟨8062334763223360145092399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10749779684297813526789865 8062334763223360145092399)
        ·
          refine ⟨12093502144835040217638599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8062334763223360145092399 12093502144835040217638599)
          ·
            refine ⟨18140253217252560326457899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12093502144835040217638599 18140253217252560326457899)
            ·
              refine ⟨27210379825878840489686849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18140253217252560326457899 27210379825878840489686849)
              ·
                refine ⟨20407784869409130367265137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27210379825878840489686849 20407784869409130367265137)
                ·
                  refine ⟨15305838652056847775448853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20407784869409130367265137 15305838652056847775448853)
                  ·
                    refine ⟨717461186815164739474165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15305838652056847775448853 717461186815164739474165)
                    ·
                      rfl

theorem cell22_2095876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_2095876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095876 prefixEnd_2095876 := by exact prefixLift 2095876
  have htrace : WordTrace (prefixWord ++ tailWord_2095876) baseStart_2095876 baseEnd_2095876 := by
    simpa [prefixWord, tailWord_2095876, baseEnd_2095876] using wordTrace_append hprefix tailTrace_2095876
  have hstable : (prefixWord ++ tailWord_2095876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095876).length < 2 ^ (prefixWord ++ tailWord_2095876).sum := by decide
  have hdescent : baseEnd_2095876 < baseStart_2095876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095908 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 7]
def baseStart_2095908 : Nat := 118140960795 + 2095908 * 2 ^ 59
def prefixEnd_2095908 : Nat := 4983230072969 + 3 ^ 40 * 2095908 * 2
def baseEnd_2095908 : Nat := 239157380356375774224689

theorem tailTrace_2095908 : CollatzResearch.WordTrace tailWord_2095908 prefixEnd_2095908 239157380356375774224689 := by
  unfold tailWord_2095908
  simp only [CollatzResearch.WordTrace]
  refine ⟨38222022445445371716724189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50962696593927162288965585 38222022445445371716724189)
  ·
    refine ⟨14333258417042014393771571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38222022445445371716724189 14333258417042014393771571)
    ·
      refine ⟨21499887625563021590657357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14333258417042014393771571 21499887625563021590657357)
      ·
        refine ⟨8062457859586133096496509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21499887625563021590657357 8062457859586133096496509)
        ·
          refine ⟨3023421697344799911186191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8062457859586133096496509 3023421697344799911186191)
          ·
            refine ⟨4535132546017199866779287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023421697344799911186191 4535132546017199866779287)
            ·
              refine ⟨6802698819025799800168931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535132546017199866779287 6802698819025799800168931)
              ·
                refine ⟨10204048228538699700253397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6802698819025799800168931 10204048228538699700253397)
                ·
                  refine ⟨239157380356375774224689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10204048228538699700253397 239157380356375774224689)
                  ·
                    rfl

theorem cell22_2095908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_2095908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095908 prefixEnd_2095908 := by exact prefixLift 2095908
  have htrace : WordTrace (prefixWord ++ tailWord_2095908) baseStart_2095908 baseEnd_2095908 := by
    simpa [prefixWord, tailWord_2095908, baseEnd_2095908] using wordTrace_append hprefix tailTrace_2095908
  have hstable : (prefixWord ++ tailWord_2095908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095908).length < 2 ^ (prefixWord ++ tailWord_2095908).sum := by decide
  have hdescent : baseEnd_2095908 < baseStart_2095908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095925 : List Nat := [1, 3, 3, 1, 3, 2, 3, 1, 5]
def baseStart_2095925 : Nat := 118140960795 + 2095925 * 2 ^ 59
def prefixEnd_2095925 : Nat := 4983230072969 + 3 ^ 40 * 2095925 * 2
def baseEnd_2095925 : Nat := 239159320172181648333005

theorem tailTrace_2095925 : CollatzResearch.WordTrace tailWord_2095925 prefixEnd_2095925 239159320172181648333005 := by
  unfold tailWord_2095925
  simp only [CollatzResearch.WordTrace]
  refine ⟨76444664931829155336817229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50963109954552770224544819 76444664931829155336817229)
  ·
    refine ⟨28666749349435933251306461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76444664931829155336817229 28666749349435933251306461)
    ·
      refine ⟨10750031006038474969239923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28666749349435933251306461 10750031006038474969239923)
      ·
        refine ⟨16125046509057712453859885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10750031006038474969239923 16125046509057712453859885)
        ·
          refine ⟨6046892440896642170197457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16125046509057712453859885 6046892440896642170197457)
          ·
            refine ⟨4535169330672481627648093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6046892440896642170197457 4535169330672481627648093)
            ·
              refine ⟨1700688499002180610368035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4535169330672481627648093 1700688499002180610368035)
              ·
                refine ⟨2551032748503270915552053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700688499002180610368035 2551032748503270915552053)
                ·
                  refine ⟨239159320172181648333005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2551032748503270915552053 239159320172181648333005)
                  ·
                    rfl

theorem cell22_2095925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_2095925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095925 prefixEnd_2095925 := by exact prefixLift 2095925
  have htrace : WordTrace (prefixWord ++ tailWord_2095925) baseStart_2095925 baseEnd_2095925 := by
    simpa [prefixWord, tailWord_2095925, baseEnd_2095925] using wordTrace_append hprefix tailTrace_2095925
  have hstable : (prefixWord ++ tailWord_2095925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095925).length < 2 ^ (prefixWord ++ tailWord_2095925).sum := by decide
  have hdescent : baseEnd_2095925 < baseStart_2095925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095968 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 4, 3]
def baseStart_2095968 : Nat := 118140960795 + 2095968 * 2 ^ 59
def prefixEnd_2095968 : Nat := 4983230072969 + 3 ^ 40 * 2095968 * 2
def baseEnd_2095968 : Nat := 717492680295307166173883

theorem tailTrace_2095968 : CollatzResearch.WordTrace tailWord_2095968 prefixEnd_2095968 717492680295307166173883 := by
  unfold tailWord_2095968
  simp only [CollatzResearch.WordTrace]
  refine ⟨38223116635336686840316279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50964155513782249120421705 38223116635336686840316279)
  ·
    refine ⟨57334674953005030260474419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38223116635336686840316279 57334674953005030260474419)
    ·
      refine ⟨86002012429507545390711629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57334674953005030260474419 86002012429507545390711629)
      ·
        refine ⟨32250754661065329521516861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86002012429507545390711629 32250754661065329521516861)
        ·
          refine ⟨12094032997899498570568823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32250754661065329521516861 12094032997899498570568823)
          ·
            refine ⟨18141049496849247855853235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12094032997899498570568823 18141049496849247855853235)
            ·
              refine ⟨27211574245273871783779853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18141049496849247855853235 27211574245273871783779853)
              ·
                refine ⟨10204340341977701918917445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27211574245273871783779853 10204340341977701918917445)
                ·
                  refine ⟨1913313814120819109797021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10204340341977701918917445 1913313814120819109797021)
                  ·
                    refine ⟨717492680295307166173883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1913313814120819109797021 717492680295307166173883)
                    ·
                      rfl

theorem cell22_2095968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 4, 3].length) (baseStart_2095968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095968 prefixEnd_2095968 := by exact prefixLift 2095968
  have htrace : WordTrace (prefixWord ++ tailWord_2095968) baseStart_2095968 baseEnd_2095968 := by
    simpa [prefixWord, tailWord_2095968, baseEnd_2095968] using wordTrace_append hprefix tailTrace_2095968
  have hstable : (prefixWord ++ tailWord_2095968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095968).length < 2 ^ (prefixWord ++ tailWord_2095968).sum := by decide
  have hdescent : baseEnd_2095968 < baseStart_2095968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095985 : List Nat := [1, 2, 2, 2, 1, 5, 1, 3, 2, 3]
def baseStart_2095985 : Nat := 118140960795 + 2095985 * 2 ^ 59
def prefixEnd_2095985 : Nat := 4983230072969 + 3 ^ 40 * 2095985 * 2
def baseEnd_2095985 : Nat := 717498499742724788498831

theorem tailTrace_2095985 : CollatzResearch.WordTrace tailWord_2095985 prefixEnd_2095985 717498499742724788498831 := by
  unfold tailWord_2095985
  simp only [CollatzResearch.WordTrace]
  refine ⟨76446853311611785584001409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50964568874407857056000939 76446853311611785584001409)
  ·
    refine ⟨57335139983708839188001057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76446853311611785584001409 57335139983708839188001057)
    ·
      refine ⟨43001354987781629391000793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57335139983708839188001057 43001354987781629391000793)
      ·
        refine ⟨32251016240836222043250595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43001354987781629391000793 32251016240836222043250595)
        ·
          refine ⟨48376524361254333064875893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32251016240836222043250595 48376524361254333064875893)
          ·
            refine ⟨4535299158867593724832115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48376524361254333064875893 4535299158867593724832115)
            ·
              refine ⟨6802948738301390587248173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535299158867593724832115 6802948738301390587248173)
              ·
                refine ⟨2551105776863021470218065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6802948738301390587248173 2551105776863021470218065)
                ·
                  refine ⟨1913329332647266102663549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2551105776863021470218065 1913329332647266102663549)
                  ·
                    refine ⟨717498499742724788498831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1913329332647266102663549 717498499742724788498831)
                    ·
                      rfl

theorem cell22_2095985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_2095985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095985 prefixEnd_2095985 := by exact prefixLift 2095985
  have htrace : WordTrace (prefixWord ++ tailWord_2095985) baseStart_2095985 baseEnd_2095985 := by
    simpa [prefixWord, tailWord_2095985, baseEnd_2095985] using wordTrace_append hprefix tailTrace_2095985
  have hstable : (prefixWord ++ tailWord_2095985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095985).length < 2 ^ (prefixWord ++ tailWord_2095985).sum := by decide
  have hdescent : baseEnd_2095985 < baseStart_2095985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2095996 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_2095996 : Nat := 118140960795 + 2095996 * 2 ^ 59
def prefixEnd_2095996 : Nat := 4983230072969 + 3 ^ 40 * 2095996 * 2
def baseEnd_2095996 : Nat := 717502265267524426473797

theorem tailTrace_2095996 : CollatzResearch.WordTrace tailWord_2095996 prefixEnd_2095996 717502265267524426473797 := by
  unfold tailWord_2095996
  simp only [CollatzResearch.WordTrace]
  refine ⟨38223627257285967231325921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50964836343047956308434561 38223627257285967231325921)
  ·
    refine ⟨28667720442964475423494441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38223627257285967231325921 28667720442964475423494441)
    ·
      refine ⟨21500790332223356567620831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28667720442964475423494441 21500790332223356567620831)
      ·
        refine ⟨32251185498335034851431247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21500790332223356567620831 32251185498335034851431247)
        ·
          refine ⟨48376778247502552277146871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32251185498335034851431247 48376778247502552277146871)
          ·
            refine ⟨72565167371253828415720307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48376778247502552277146871 72565167371253828415720307)
            ·
              refine ⟨108847751056880742623580461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72565167371253828415720307 108847751056880742623580461)
              ·
                refine ⟨40817906646330278483842673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108847751056880742623580461 40817906646330278483842673)
                ·
                  refine ⟨30613429984747708862882005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40817906646330278483842673 30613429984747708862882005)
                  ·
                    refine ⟨717502265267524426473797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30613429984747708862882005 717502265267524426473797)
                    ·
                      rfl

theorem cell22_2095996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_2095996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2095996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2095996 prefixEnd_2095996 := by exact prefixLift 2095996
  have htrace : WordTrace (prefixWord ++ tailWord_2095996) baseStart_2095996 baseEnd_2095996 := by
    simpa [prefixWord, tailWord_2095996, baseEnd_2095996] using wordTrace_append hprefix tailTrace_2095996
  have hstable : (prefixWord ++ tailWord_2095996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2095996).length < 2 ^ (prefixWord ++ tailWord_2095996).sum := by decide
  have hdescent : baseEnd_2095996 < baseStart_2095996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2095996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096070 : List Nat := [6, 1, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2096070 : Nat := 118140960795 + 2096070 * 2 ^ 59
def prefixEnd_2096070 : Nat := 4983230072969 + 3 ^ 40 * 2096070 * 2
def baseEnd_2096070 : Nat := 717527596979812900123571

theorem tailTrace_2096070 : CollatzResearch.WordTrace tailWord_2096070 prefixEnd_2096070 717527596979812900123571 := by
  unfold tailWord_2096070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2389061047384495159401427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50966635677535896733897109 2389061047384495159401427)
  ·
    refine ⟨3583591571076742739102141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2389061047384495159401427 3583591571076742739102141)
    ·
      refine ⟨1343846839153778527163303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3583591571076742739102141 1343846839153778527163303)
      ·
        refine ⟨2015770258730667790744955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343846839153778527163303 2015770258730667790744955)
        ·
          refine ⟨3023655388096001686117433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015770258730667790744955 3023655388096001686117433)
          ·
            refine ⟨2267741541072001264588075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3023655388096001686117433 2267741541072001264588075)
            ·
              refine ⟨3401612311608001896882113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267741541072001264588075 3401612311608001896882113)
              ·
                refine ⟨2551209233706001422661585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3401612311608001896882113 2551209233706001422661585)
                ·
                  refine ⟨1913406925279501066996189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2551209233706001422661585 1913406925279501066996189)
                  ·
                    refine ⟨717527596979812900123571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1913406925279501066996189 717527596979812900123571)
                    ·
                      rfl

theorem cell22_2096070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2096070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096070 prefixEnd_2096070 := by exact prefixLift 2096070
  have htrace : WordTrace (prefixWord ++ tailWord_2096070) baseStart_2096070 baseEnd_2096070 := by
    simpa [prefixWord, tailWord_2096070, baseEnd_2096070] using wordTrace_append hprefix tailTrace_2096070
  have hstable : (prefixWord ++ tailWord_2096070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096070).length < 2 ^ (prefixWord ++ tailWord_2096070).sum := by decide
  have hdescent : baseEnd_2096070 < baseStart_2096070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096088 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 6]
def baseStart_2096088 : Nat := 118140960795 + 2096088 * 2 ^ 59
def prefixEnd_2096088 : Nat := 4983230072969 + 3 ^ 40 * 2096088 * 2
def baseEnd_2096088 : Nat := 239177919582555617724505

theorem tailTrace_2096088 : CollatzResearch.WordTrace tailWord_2096088 prefixEnd_2096088 239177919582555617724505 := by
  unfold tailWord_2096088
  simp only [CollatzResearch.WordTrace]
  refine ⟨38225305015119317087500459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50967073353492422783333945 38225305015119317087500459)
  ·
    refine ⟨57337957522678975631250689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38225305015119317087500459 57337957522678975631250689)
    ·
      refine ⟨43003468142009231723438017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57337957522678975631250689 43003468142009231723438017)
      ·
        refine ⟨32252601106506923792578513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43003468142009231723438017 32252601106506923792578513)
        ·
          refine ⟨24189450829880192844433885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32252601106506923792578513 24189450829880192844433885)
          ·
            refine ⟨9071044061205072316662707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24189450829880192844433885 9071044061205072316662707)
            ·
              refine ⟨13606566091807608474994061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071044061205072316662707 13606566091807608474994061)
              ·
                refine ⟨5102462284427853178122773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13606566091807608474994061 5102462284427853178122773)
                ·
                  refine ⟨239177919582555617724505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5102462284427853178122773 239177919582555617724505)
                  ·
                    rfl

theorem cell22_2096088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_2096088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096088 prefixEnd_2096088 := by exact prefixLift 2096088
  have htrace : WordTrace (prefixWord ++ tailWord_2096088) baseStart_2096088 baseEnd_2096088 := by
    simpa [prefixWord, tailWord_2096088, baseEnd_2096088] using wordTrace_append hprefix tailTrace_2096088
  have hstable : (prefixWord ++ tailWord_2096088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096088).length < 2 ^ (prefixWord ++ tailWord_2096088).sum := by decide
  have hdescent : baseEnd_2096088 < baseStart_2096088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096135 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 2, 4]
def baseStart_2096135 : Nat := 118140960795 + 2096135 * 2 ^ 59
def prefixEnd_2096135 : Nat := 4983230072969 + 3 ^ 40 * 2096135 * 2
def baseEnd_2096135 : Nat := 717549847808174397248371

theorem tailTrace_2096135 : CollatzResearch.WordTrace tailWord_2096135 prefixEnd_2096135 717549847808174397248371 := by
  unfold tailWord_2096135
  simp only [CollatzResearch.WordTrace]
  refine ⟨76452324261068361201961859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50968216174045574134641239 76452324261068361201961859)
  ·
    refine ⟨114678486391602541802942789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76452324261068361201961859 114678486391602541802942789)
    ·
      refine ⟨21502216198425476588051773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114678486391602541802942789 21502216198425476588051773)
      ·
        refine ⟨8063331074409553720519415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21502216198425476588051773 8063331074409553720519415)
        ·
          refine ⟨12094996611614330580779123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8063331074409553720519415 12094996611614330580779123)
          ·
            refine ⟨18142494917421495871168685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12094996611614330580779123 18142494917421495871168685)
            ·
              refine ⟨6803435594033060951688257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18142494917421495871168685 6803435594033060951688257)
              ·
                refine ⟨5102576695524795713766193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6803435594033060951688257 5102576695524795713766193)
                ·
                  refine ⟨3826932521643596785324645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5102576695524795713766193 3826932521643596785324645)
                  ·
                    refine ⟨717549847808174397248371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826932521643596785324645 717549847808174397248371)
                    ·
                      rfl

theorem cell22_2096135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_2096135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096135 prefixEnd_2096135 := by exact prefixLift 2096135
  have htrace : WordTrace (prefixWord ++ tailWord_2096135) baseStart_2096135 baseEnd_2096135 := by
    simpa [prefixWord, tailWord_2096135, baseEnd_2096135] using wordTrace_append hprefix tailTrace_2096135
  have hstable : (prefixWord ++ tailWord_2096135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096135).length < 2 ^ (prefixWord ++ tailWord_2096135).sum := by decide
  have hdescent : baseEnd_2096135 < baseStart_2096135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096165 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 5, 3]
def baseStart_2096165 : Nat := 118140960795 + 2096165 * 2 ^ 59
def prefixEnd_2096165 : Nat := 4983230072969 + 3 ^ 40 * 2096165 * 2
def baseEnd_2096165 : Nat := 717560117421264318998279

theorem tailTrace_2096165 : CollatzResearch.WordTrace tailWord_2096165 prefixEnd_2096165 717560117421264318998279 := by
  unfold tailWord_2096165
  simp only [CollatzResearch.WordTrace]
  refine ⟨76453418450959676325553949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50968945633973117550369299 76453418450959676325553949)
  ·
    refine ⟨28670031919109878622082731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76453418450959676325553949 28670031919109878622082731)
    ·
      refine ⟨43005047878664817933124097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28670031919109878622082731 43005047878664817933124097)
      ·
        refine ⟨32253785908998613449843073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43005047878664817933124097 32253785908998613449843073)
        ·
          refine ⟨24190339431748960087382305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32253785908998613449843073 24190339431748960087382305)
          ·
            refine ⟨18142754573811720065536729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24190339431748960087382305 18142754573811720065536729)
            ·
              refine ⟨13607065930358790049152547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18142754573811720065536729 13607065930358790049152547)
              ·
                refine ⟨20410598895538185073728821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13607065930358790049152547 20410598895538185073728821)
                ·
                  refine ⟨1913493646456704850662077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20410598895538185073728821 1913493646456704850662077)
                  ·
                    refine ⟨717560117421264318998279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1913493646456704850662077 717560117421264318998279)
                    ·
                      rfl

theorem cell22_2096165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_2096165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096165 prefixEnd_2096165 := by exact prefixLift 2096165
  have htrace : WordTrace (prefixWord ++ tailWord_2096165) baseStart_2096165 baseEnd_2096165 := by
    simpa [prefixWord, tailWord_2096165, baseEnd_2096165] using wordTrace_append hprefix tailTrace_2096165
  have hstable : (prefixWord ++ tailWord_2096165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096165).length < 2 ^ (prefixWord ++ tailWord_2096165).sum := by decide
  have hdescent : baseEnd_2096165 < baseStart_2096165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096195 : List Nat := [1, 1, 1, 3, 1, 2, 6, 2, 5]
def baseStart_2096195 : Nat := 118140960795 + 2096195 * 2 ^ 59
def prefixEnd_2096195 : Nat := 4983230072969 + 3 ^ 40 * 2096195 * 2
def baseEnd_2096195 : Nat := 239190129011451413582729

theorem tailTrace_2096195 : CollatzResearch.WordTrace tailWord_2096195 prefixEnd_2096195 239190129011451413582729 := by
  unfold tailWord_2096195
  simp only [CollatzResearch.WordTrace]
  refine ⟨76454512640850991449146039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50969675093900660966097359 76454512640850991449146039)
  ·
    refine ⟨114681768961276487173719059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76454512640850991449146039 114681768961276487173719059)
    ·
      refine ⟨172022653441914730760578589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114681768961276487173719059 172022653441914730760578589)
      ·
        refine ⟨64508495040718024035216971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172022653441914730760578589 64508495040718024035216971)
        ·
          refine ⟨96762742561077036052825457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64508495040718024035216971 96762742561077036052825457)
          ·
            refine ⟨72572056920807777039619093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96762742561077036052825457 72572056920807777039619093)
            ·
              refine ⟨3401815168162864548732145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72572056920807777039619093 3401815168162864548732145)
              ·
                refine ⟨2551361376122148411549109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3401815168162864548732145 2551361376122148411549109)
                ·
                  refine ⟨239190129011451413582729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2551361376122148411549109 239190129011451413582729)
                  ·
                    rfl

theorem cell22_2096195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 5].length) (baseStart_2096195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096195 prefixEnd_2096195 := by exact prefixLift 2096195
  have htrace : WordTrace (prefixWord ++ tailWord_2096195) baseStart_2096195 baseEnd_2096195 := by
    simpa [prefixWord, tailWord_2096195, baseEnd_2096195] using wordTrace_append hprefix tailTrace_2096195
  have hstable : (prefixWord ++ tailWord_2096195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096195).length < 2 ^ (prefixWord ++ tailWord_2096195).sum := by decide
  have hdescent : baseEnd_2096195 < baseStart_2096195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096199 : List Nat := [1, 1, 4, 1, 3, 3, 1, 4, 1, 3]
def baseStart_2096199 : Nat := 118140960795 + 2096199 * 2 ^ 59
def prefixEnd_2096199 : Nat := 4983230072969 + 3 ^ 40 * 2096199 * 2
def baseEnd_2096199 : Nat := 717571756316099563648175

theorem tailTrace_2096199 : CollatzResearch.WordTrace tailWord_2096199 prefixEnd_2096199 717571756316099563648175 := by
  unfold tailWord_2096199
  simp only [CollatzResearch.WordTrace]
  refine ⟨76454658532836500132291651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50969772355224333421527767 76454658532836500132291651)
  ·
    refine ⟨114681987799254750198437477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76454658532836500132291651 114681987799254750198437477)
    ·
      refine ⟨21502872712360265662207027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114681987799254750198437477 21502872712360265662207027)
      ·
        refine ⟨32254309068540398493310541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21502872712360265662207027 32254309068540398493310541)
        ·
          refine ⟨12095365900702649434991453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32254309068540398493310541 12095365900702649434991453)
          ·
            refine ⟨4535762212763493538121795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12095365900702649434991453 4535762212763493538121795)
            ·
              refine ⟨6803643319145240307182693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535762212763493538121795 6803643319145240307182693)
              ·
                refine ⟨1275683122339732557596755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6803643319145240307182693 1275683122339732557596755)
                ·
                  refine ⟨1913524683509598836395133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275683122339732557596755 1913524683509598836395133)
                  ·
                    refine ⟨717571756316099563648175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1913524683509598836395133 717571756316099563648175)
                    ·
                      rfl

theorem cell22_2096199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_2096199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096199 prefixEnd_2096199 := by exact prefixLift 2096199
  have htrace : WordTrace (prefixWord ++ tailWord_2096199) baseStart_2096199 baseEnd_2096199 := by
    simpa [prefixWord, tailWord_2096199, baseEnd_2096199] using wordTrace_append hprefix tailTrace_2096199
  have hstable : (prefixWord ++ tailWord_2096199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096199).length < 2 ^ (prefixWord ++ tailWord_2096199).sum := by decide
  have hdescent : baseEnd_2096199 < baseStart_2096199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096210 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_2096210 : Nat := 118140960795 + 2096210 * 2 ^ 59
def prefixEnd_2096210 : Nat := 4983230072969 + 3 ^ 40 * 2096210 * 2
def baseEnd_2096210 : Nat := 717575521840899201623141

theorem tailTrace_2096210 : CollatzResearch.WordTrace tailWord_2096210 prefixEnd_2096210 717575521840899201623141 := by
  unfold tailWord_2096210
  simp only [CollatzResearch.WordTrace]
  refine ⟨19113764933949162252735521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50970039823864432673961389 19113764933949162252735521)
  ·
    refine ⟨14335323700461871689551641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19113764933949162252735521 14335323700461871689551641)
    ·
      refine ⟨10751492775346403767163731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14335323700461871689551641 10751492775346403767163731)
      ·
        refine ⟨16127239163019605650745597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10751492775346403767163731 16127239163019605650745597)
        ·
          refine ⟨6047714686132352119029599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16127239163019605650745597 6047714686132352119029599)
          ·
            refine ⟨9071572029198528178544399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6047714686132352119029599 9071572029198528178544399)
            ·
              refine ⟨13607358043797792267816599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071572029198528178544399 13607358043797792267816599)
              ·
                refine ⟨20411037065696688401724899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13607358043797792267816599 20411037065696688401724899)
                ·
                  refine ⟨30616555598545032602587349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20411037065696688401724899 30616555598545032602587349)
                  ·
                    refine ⟨717575521840899201623141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30616555598545032602587349 717575521840899201623141)
                    ·
                      rfl

theorem cell22_2096210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_2096210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096210 prefixEnd_2096210 := by exact prefixLift 2096210
  have htrace : WordTrace (prefixWord ++ tailWord_2096210) baseStart_2096210 baseEnd_2096210 := by
    simpa [prefixWord, tailWord_2096210, baseEnd_2096210] using wordTrace_append hprefix tailTrace_2096210
  have hstable : (prefixWord ++ tailWord_2096210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096210).length < 2 ^ (prefixWord ++ tailWord_2096210).sum := by decide
  have hdescent : baseEnd_2096210 < baseStart_2096210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096225 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 3, 4]
def baseStart_2096225 : Nat := 118140960795 + 2096225 * 2 ^ 59
def prefixEnd_2096225 : Nat := 4983230072969 + 3 ^ 40 * 2096225 * 2
def baseEnd_2096225 : Nat := 717580656647444162498095

theorem tailTrace_2096225 : CollatzResearch.WordTrace tailWord_2096225 prefixEnd_2096225 717580656647444162498095 := by
  unfold tailWord_2096225
  simp only [CollatzResearch.WordTrace]
  refine ⟨76455606830742306572738129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50970404553828204381825419 76455606830742306572738129)
  ·
    refine ⟨57341705123056729929553597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76455606830742306572738129 57341705123056729929553597)
    ·
      refine ⟨21503139421146273723582599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57341705123056729929553597 21503139421146273723582599)
      ·
        refine ⟨32254709131719410585373899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21503139421146273723582599 32254709131719410585373899)
        ·
          refine ⟨48382063697579115878060849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32254709131719410585373899 48382063697579115878060849)
          ·
            refine ⟨36286547773184336908545637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48382063697579115878060849 36286547773184336908545637)
            ·
              refine ⟨6803727707472063170352307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36286547773184336908545637 6803727707472063170352307)
              ·
                refine ⟨10205591561208094755528461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6803727707472063170352307 10205591561208094755528461)
                ·
                  refine ⟨3827096835453035533323173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10205591561208094755528461 3827096835453035533323173)
                  ·
                    refine ⟨717580656647444162498095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3827096835453035533323173 717580656647444162498095)
                    ·
                      rfl

theorem cell22_2096225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_2096225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096225 prefixEnd_2096225 := by exact prefixLift 2096225
  have htrace : WordTrace (prefixWord ++ tailWord_2096225) baseStart_2096225 baseEnd_2096225 := by
    simpa [prefixWord, tailWord_2096225, baseEnd_2096225] using wordTrace_append hprefix tailTrace_2096225
  have hstable : (prefixWord ++ tailWord_2096225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096225).length < 2 ^ (prefixWord ++ tailWord_2096225).sum := by decide
  have hdescent : baseEnd_2096225 < baseStart_2096225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096242 : List Nat := [3, 2, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_2096242 : Nat := 118140960795 + 2096242 * 2 ^ 59
def prefixEnd_2096242 : Nat := 4983230072969 + 3 ^ 40 * 2096242 * 2
def baseEnd_2096242 : Nat := 717586476094861784823043

theorem tailTrace_2096242 : CollatzResearch.WordTrace tailWord_2096242 prefixEnd_2096242 717586476094861784823043 := by
  unfold tailWord_2096242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19114056717920179619026745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50970817914453812317404653 19114056717920179619026745)
  ·
    refine ⟨14335542538440134714270059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19114056717920179619026745 14335542538440134714270059)
    ·
      refine ⟨21503313807660202071405089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14335542538440134714270059 21503313807660202071405089)
      ·
        refine ⟨16127485355745151553553817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21503313807660202071405089 16127485355745151553553817)
        ·
          refine ⟨12095614016808863665165363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16127485355745151553553817 12095614016808863665165363)
          ·
            refine ⟨18143421025213295497748045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12095614016808863665165363 18143421025213295497748045)
            ·
              refine ⟨6803782884454985811655517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18143421025213295497748045 6803782884454985811655517)
              ·
                refine ⟨2551418581670619679370819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6803782884454985811655517 2551418581670619679370819)
                ·
                  refine ⟨3827127872505929519056229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551418581670619679370819 3827127872505929519056229)
                  ·
                    refine ⟨717586476094861784823043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3827127872505929519056229 717586476094861784823043)
                    ·
                      rfl

theorem cell22_2096242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_2096242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096242 prefixEnd_2096242 := by exact prefixLift 2096242
  have htrace : WordTrace (prefixWord ++ tailWord_2096242) baseStart_2096242 baseEnd_2096242 := by
    simpa [prefixWord, tailWord_2096242, baseEnd_2096242] using wordTrace_append hprefix tailTrace_2096242
  have hstable : (prefixWord ++ tailWord_2096242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096242).length < 2 ^ (prefixWord ++ tailWord_2096242).sum := by decide
  have hdescent : baseEnd_2096242 < baseStart_2096242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096257 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 6]
def baseStart_2096257 : Nat := 118140960795 + 2096257 * 2 ^ 59
def prefixEnd_2096257 : Nat := 4983230072969 + 3 ^ 40 * 2096257 * 2
def baseEnd_2096257 : Nat := 239197203633802248565999

theorem tailTrace_2096257 : CollatzResearch.WordTrace tailWord_2096257 prefixEnd_2096257 239197203633802248565999 := by
  unfold tailWord_2096257
  simp only [CollatzResearch.WordTrace]
  refine ⟨76456773966626376037903025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50971182644417584025268683 76456773966626376037903025)
  ·
    refine ⟨57342580474969782028427269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76456773966626376037903025 57342580474969782028427269)
    ·
      refine ⟨10751733839056834130330113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57342580474969782028427269 10751733839056834130330113)
      ·
        refine ⟨8063800379292625597747585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10751733839056834130330113 8063800379292625597747585)
        ·
          refine ⟨6047850284469469198310689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8063800379292625597747585 6047850284469469198310689)
          ·
            refine ⟨4535887713352101898733017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6047850284469469198310689 4535887713352101898733017)
            ·
              refine ⟨3401915785014076424049763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4535887713352101898733017 3401915785014076424049763)
              ·
                refine ⟨5102873677521114636074645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401915785014076424049763 5102873677521114636074645)
                ·
                  refine ⟨239197203633802248565999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5102873677521114636074645 239197203633802248565999)
                  ·
                    rfl

theorem cell22_2096257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_2096257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096257 prefixEnd_2096257 := by exact prefixLift 2096257
  have htrace : WordTrace (prefixWord ++ tailWord_2096257) baseStart_2096257 baseEnd_2096257 := by
    simpa [prefixWord, tailWord_2096257, baseEnd_2096257] using wordTrace_append hprefix tailTrace_2096257
  have hstable : (prefixWord ++ tailWord_2096257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096257).length < 2 ^ (prefixWord ++ tailWord_2096257).sum := by decide
  have hdescent : baseEnd_2096257 < baseStart_2096257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096285 : List Nat := [1, 4, 2, 1, 1, 2, 3, 8]
def baseStart_2096285 : Nat := 118140960795 + 2096285 * 2 ^ 59
def prefixEnd_2096285 : Nat := 4983230072969 + 3 ^ 40 * 2096285 * 2
def baseEnd_2096285 : Nat := 79733466208180445110879

theorem tailTrace_2096285 : CollatzResearch.WordTrace tailWord_2096285 prefixEnd_2096285 79733466208180445110879 := by
  unfold tailWord_2096285
  simp only [CollatzResearch.WordTrace]
  refine ⟨76457795210524936819922309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50971863473683291213281539 76457795210524936819922309)
  ·
    refine ⟨14335836601973425653735433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76457795210524936819922309 14335836601973425653735433)
    ·
      refine ⟨10751877451480069240301575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14335836601973425653735433 10751877451480069240301575)
      ·
        refine ⟨16127816177220103860452363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10751877451480069240301575 16127816177220103860452363)
        ·
          refine ⟨24191724265830155790678545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16127816177220103860452363 24191724265830155790678545)
          ·
            refine ⟨18143793199372616843008909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24191724265830155790678545 18143793199372616843008909)
            ·
              refine ⟨6803922449764731316128341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18143793199372616843008909 6803922449764731316128341)
              ·
                refine ⟨79733466208180445110879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6803922449764731316128341 79733466208180445110879)
                ·
                  rfl

theorem cell22_2096285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 8].length) (baseStart_2096285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096285 prefixEnd_2096285 := by exact prefixLift 2096285
  have htrace : WordTrace (prefixWord ++ tailWord_2096285) baseStart_2096285 baseEnd_2096285 := by
    simpa [prefixWord, tailWord_2096285, baseEnd_2096285] using wordTrace_append hprefix tailTrace_2096285
  have hstable : (prefixWord ++ tailWord_2096285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096285).length < 2 ^ (prefixWord ++ tailWord_2096285).sum := by decide
  have hdescent : baseEnd_2096285 < baseStart_2096285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096345 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 4, 5]
def baseStart_2096345 : Nat := 118140960795 + 2096345 * 2 ^ 59
def prefixEnd_2096345 : Nat := 4983230072969 + 3 ^ 40 * 2096345 * 2
def baseEnd_2096345 : Nat := 717621735099803849497727

theorem tailTrace_2096345 : CollatzResearch.WordTrace tailWord_2096345 prefixEnd_2096345 717621735099803849497727 := by
  unfold tailWord_2096345
  simp only [CollatzResearch.WordTrace]
  refine ⟨76459983590307567067106489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50973322393538378044737659 76459983590307567067106489)
  ·
    refine ⟨57344987692730675300329867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76459983590307567067106489 57344987692730675300329867)
    ·
      refine ⟨86017481539096012950494801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57344987692730675300329867 86017481539096012950494801)
      ·
        refine ⟨64513111154322009712871101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86017481539096012950494801 64513111154322009712871101)
        ·
          refine ⟨24192416682870753642326663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64513111154322009712871101 24192416682870753642326663)
          ·
            refine ⟨36288625024306130463489995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24192416682870753642326663 36288625024306130463489995)
            ·
              refine ⟨54432937536459195695234993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36288625024306130463489995 54432937536459195695234993)
              ·
                refine ⟨40824703152344396771426245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54432937536459195695234993 40824703152344396771426245)
                ·
                  refine ⟨7654631841064574394642421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40824703152344396771426245 7654631841064574394642421)
                  ·
                    refine ⟨717621735099803849497727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7654631841064574394642421 717621735099803849497727)
                    ·
                      rfl

theorem cell22_2096345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_2096345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096345 prefixEnd_2096345 := by exact prefixLift 2096345
  have htrace : WordTrace (prefixWord ++ tailWord_2096345) baseStart_2096345 baseEnd_2096345 := by
    simpa [prefixWord, tailWord_2096345, baseEnd_2096345] using wordTrace_append hprefix tailTrace_2096345
  have hstable : (prefixWord ++ tailWord_2096345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096345).length < 2 ^ (prefixWord ++ tailWord_2096345).sum := by decide
  have hdescent : baseEnd_2096345 < baseStart_2096345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096407 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 1, 5]
def baseStart_2096407 : Nat := 118140960795 + 2096407 * 2 ^ 59
def prefixEnd_2096407 : Nat := 4983230072969 + 3 ^ 40 * 2096407 * 2
def baseEnd_2096407 : Nat := 717642958966856354447537

theorem tailTrace_2096407 : CollatzResearch.WordTrace tailWord_2096407 prefixEnd_2096407 717642958966856354447537 := by
  unfold tailWord_2096407
  simp only [CollatzResearch.WordTrace]
  refine ⟨76462244916082951655863475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50974829944055301103908983 76462244916082951655863475)
  ·
    refine ⟨114693367374124427483795213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76462244916082951655863475 114693367374124427483795213)
    ·
      refine ⟨43010012765296660306423205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114693367374124427483795213 43010012765296660306423205)
      ·
        refine ⟨8064377393493123807454351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43010012765296660306423205 8064377393493123807454351)
        ·
          refine ⟨12096566090239685711181527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8064377393493123807454351 12096566090239685711181527)
          ·
            refine ⟨18144849135359528566772291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12096566090239685711181527 18144849135359528566772291)
            ·
              refine ⟨27217273703039292850158437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18144849135359528566772291 27217273703039292850158437)
              ·
                refine ⟨5103238819319867409404707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27217273703039292850158437 5103238819319867409404707)
                ·
                  refine ⟨7654858228979801114107061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5103238819319867409404707 7654858228979801114107061)
                  ·
                    refine ⟨717642958966856354447537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7654858228979801114107061 717642958966856354447537)
                    ·
                      rfl

theorem cell22_2096407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_2096407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096407 prefixEnd_2096407 := by exact prefixLift 2096407
  have htrace : WordTrace (prefixWord ++ tailWord_2096407) baseStart_2096407 baseEnd_2096407 := by
    simpa [prefixWord, tailWord_2096407, baseEnd_2096407] using wordTrace_append hprefix tailTrace_2096407
  have hstable : (prefixWord ++ tailWord_2096407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096407).length < 2 ^ (prefixWord ++ tailWord_2096407).sum := by decide
  have hdescent : baseEnd_2096407 < baseStart_2096407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096426 : List Nat := [3, 1, 4, 2, 1, 1, 2, 4, 4]
def baseStart_2096426 : Nat := 118140960795 + 2096426 * 2 ^ 59
def prefixEnd_2096426 : Nat := 4983230072969 + 3 ^ 40 * 2096426 * 2
def baseEnd_2096426 : Nat := 239216487685048879407493

theorem tailTrace_2096426 : CollatzResearch.WordTrace tailWord_2096426 prefixEnd_2096426 239216487685048879407493 := by
  unfold tailWord_2096426
  simp only [CollatzResearch.WordTrace]
  refine ⟨19115734475753529475201283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50975291935342745267203421 19115734475753529475201283)
  ·
    refine ⟨28673601713630294212801925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19115734475753529475201283 28673601713630294212801925)
    ·
      refine ⟨5376300321305680164900361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28673601713630294212801925 5376300321305680164900361)
      ·
        refine ⟨4032225240979260123675271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5376300321305680164900361 4032225240979260123675271)
        ·
          refine ⟨6048337861468890185512907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032225240979260123675271 6048337861468890185512907)
          ·
            refine ⟨9072506792203335278269361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6048337861468890185512907 9072506792203335278269361)
            ·
              refine ⟨6804380094152501458702021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9072506792203335278269361 6804380094152501458702021)
              ·
                refine ⟨1275821267653594023506629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6804380094152501458702021 1275821267653594023506629)
                ·
                  refine ⟨239216487685048879407493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1275821267653594023506629 239216487685048879407493)
                  ·
                    rfl

theorem cell22_2096426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_2096426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096426 prefixEnd_2096426 := by exact prefixLift 2096426
  have htrace : WordTrace (prefixWord ++ tailWord_2096426) baseStart_2096426 baseEnd_2096426 := by
    simpa [prefixWord, tailWord_2096426, baseEnd_2096426] using wordTrace_append hprefix tailTrace_2096426
  have hstable : (prefixWord ++ tailWord_2096426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096426).length < 2 ^ (prefixWord ++ tailWord_2096426).sum := by decide
  have hdescent : baseEnd_2096426 < baseStart_2096426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096441 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 1, 5]
def baseStart_2096441 : Nat := 118140960795 + 2096441 * 2 ^ 59
def prefixEnd_2096441 : Nat := 4983230072969 + 3 ^ 40 * 2096441 * 2
def baseEnd_2096441 : Nat := 717654597861691599097433

theorem tailTrace_2096441 : CollatzResearch.WordTrace tailWord_2096441 prefixEnd_2096441 717654597861691599097433 := by
  unfold tailWord_2096441
  simp only [CollatzResearch.WordTrace]
  refine ⟨76463484997959775462601177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50975656665306516975067451 76463484997959775462601177)
  ·
    refine ⟨57347613748469831596950883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76463484997959775462601177 57347613748469831596950883)
    ·
      refine ⟨86021420622704747395426325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57347613748469831596950883 86021420622704747395426325)
      ·
        refine ⟨4032254091689285034160609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86021420622704747395426325 4032254091689285034160609)
        ·
          refine ⟨3024190568766963775620457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4032254091689285034160609 3024190568766963775620457)
          ·
            refine ⟨2268142926575222831715343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3024190568766963775620457 2268142926575222831715343)
            ·
              refine ⟨3402214389862834247573015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2268142926575222831715343 3402214389862834247573015)
              ·
                refine ⟨5103321584794251371359523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3402214389862834247573015 5103321584794251371359523)
                ·
                  refine ⟨7654982377191377057039285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5103321584794251371359523 7654982377191377057039285)
                  ·
                    refine ⟨717654597861691599097433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7654982377191377057039285 717654597861691599097433)
                    ·
                      rfl

theorem cell22_2096441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 5].length) (baseStart_2096441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096441 prefixEnd_2096441 := by exact prefixLift 2096441
  have htrace : WordTrace (prefixWord ++ tailWord_2096441) baseStart_2096441 baseEnd_2096441 := by
    simpa [prefixWord, tailWord_2096441, baseEnd_2096441] using wordTrace_append hprefix tailTrace_2096441
  have hstable : (prefixWord ++ tailWord_2096441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096441).length < 2 ^ (prefixWord ++ tailWord_2096441).sum := by decide
  have hdescent : baseEnd_2096441 < baseStart_2096441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096477 : List Nat := [1, 4, 5, 1, 1, 1, 3, 2, 4]
def baseStart_2096477 : Nat := 118140960795 + 2096477 * 2 ^ 59
def prefixEnd_2096477 : Nat := 4983230072969 + 3 ^ 40 * 2096477 * 2
def baseEnd_2096477 : Nat := 239222307132466501732441

theorem tailTrace_2096477 : CollatzResearch.WordTrace tailWord_2096477 prefixEnd_2096477 239222307132466501732441 := by
  unfold tailWord_2096477
  simp only [CollatzResearch.WordTrace]
  refine ⟨76464798025829353610911685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50976532017219569073941123 76464798025829353610911685)
  ·
    refine ⟨14337149629843003802045941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76464798025829353610911685 14337149629843003802045941)
    ·
      refine ⟨1344107777797781606441807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14337149629843003802045941 1344107777797781606441807)
      ·
        refine ⟨2016161666696672409662711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1344107777797781606441807 2016161666696672409662711)
        ·
          refine ⟨3024242500045008614494067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2016161666696672409662711 3024242500045008614494067)
          ·
            refine ⟨4536363750067512921741101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024242500045008614494067 4536363750067512921741101)
            ·
              refine ⟨1701136406275317345652913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4536363750067512921741101 1701136406275317345652913)
              ·
                refine ⟨1275852304706488009239685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1701136406275317345652913 1275852304706488009239685)
                ·
                  refine ⟨239222307132466501732441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1275852304706488009239685 239222307132466501732441)
                  ·
                    rfl

theorem cell22_2096477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_2096477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096477 prefixEnd_2096477 := by exact prefixLift 2096477
  have htrace : WordTrace (prefixWord ++ tailWord_2096477) baseStart_2096477 baseEnd_2096477 := by
    simpa [prefixWord, tailWord_2096477, baseEnd_2096477] using wordTrace_append hprefix tailTrace_2096477
  have hstable : (prefixWord ++ tailWord_2096477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096477).length < 2 ^ (prefixWord ++ tailWord_2096477).sum := by decide
  have hdescent : baseEnd_2096477 < baseStart_2096477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096497 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 2, 5]
def baseStart_2096497 : Nat := 118140960795 + 2096497 * 2 ^ 59
def prefixEnd_2096497 : Nat := 4983230072969 + 3 ^ 40 * 2096497 * 2
def baseEnd_2096497 : Nat := 717673767806126119697261

theorem tailTrace_2096497 : CollatzResearch.WordTrace tailWord_2096497 prefixEnd_2096497 717673767806126119697261 := by
  unfold tailWord_2096497
  simp only [CollatzResearch.WordTrace]
  refine ⟨76465527485756897026639745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50977018323837931351093163 76465527485756897026639745)
  ·
    refine ⟨57349145614317672769979809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76465527485756897026639745 57349145614317672769979809)
    ·
      refine ⟨43011859210738254577484857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57349145614317672769979809 43011859210738254577484857)
      ·
        refine ⟨32258894408053690933113643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43011859210738254577484857 32258894408053690933113643)
        ·
          refine ⟨48388341612080536399670465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32258894408053690933113643 48388341612080536399670465)
          ·
            refine ⟨36291256209060402299752849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48388341612080536399670465 36291256209060402299752849)
            ·
              refine ⟨27218442156795301724814637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36291256209060402299752849 27218442156795301724814637)
              ·
                refine ⟨10206915808798238146805489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27218442156795301724814637 10206915808798238146805489)
                ·
                  refine ⟨7655186856598678610104117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10206915808798238146805489 7655186856598678610104117)
                  ·
                    refine ⟨717673767806126119697261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7655186856598678610104117 717673767806126119697261)
                    ·
                      rfl

theorem cell22_2096497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_2096497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096497 prefixEnd_2096497 := by exact prefixLift 2096497
  have htrace : WordTrace (prefixWord ++ tailWord_2096497) baseStart_2096497 baseEnd_2096497 := by
    simpa [prefixWord, tailWord_2096497, baseEnd_2096497] using wordTrace_append hprefix tailTrace_2096497
  have hstable : (prefixWord ++ tailWord_2096497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096497).length < 2 ^ (prefixWord ++ tailWord_2096497).sum := by decide
  have hdescent : baseEnd_2096497 < baseStart_2096497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096580 : List Nat := [2, 3, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_2096580 : Nat := 118140960795 + 2096580 * 2 ^ 59
def prefixEnd_2096580 : Nat := 4983230072969 + 3 ^ 40 * 2096580 * 2
def baseEnd_2096580 : Nat := 717702180402341569872007

theorem tailTrace_2096580 : CollatzResearch.WordTrace tailWord_2096580 prefixEnd_2096580 717702180402341569872007 := by
  unfold tailWord_2096580
  simp only [CollatzResearch.WordTrace]
  refine ⟨38234277372228101100955597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50979036496304134801274129 38234277372228101100955597)
  ·
    refine ⟨14337854014585537912858349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38234277372228101100955597 14337854014585537912858349)
    ·
      refine ⟨5376695255469576717321881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14337854014585537912858349 5376695255469576717321881)
      ·
        refine ⟨4032521441602182537991411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5376695255469576717321881 4032521441602182537991411)
        ·
          refine ⟨6048782162403273806987117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032521441602182537991411 6048782162403273806987117)
          ·
            refine ⟨2268293310901227677620169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6048782162403273806987117 2268293310901227677620169)
            ·
              refine ⟨1701219983175920758215127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2268293310901227677620169 1701219983175920758215127)
              ·
                refine ⟨2551829974763881137322691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1701219983175920758215127 2551829974763881137322691)
                ·
                  refine ⟨3827744962145821705984037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551829974763881137322691 3827744962145821705984037)
                  ·
                    refine ⟨717702180402341569872007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3827744962145821705984037 717702180402341569872007)
                    ·
                      rfl

theorem cell22_2096580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_2096580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096580 prefixEnd_2096580 := by exact prefixLift 2096580
  have htrace : WordTrace (prefixWord ++ tailWord_2096580) baseStart_2096580 baseEnd_2096580 := by
    simpa [prefixWord, tailWord_2096580, baseEnd_2096580] using wordTrace_append hprefix tailTrace_2096580
  have hstable : (prefixWord ++ tailWord_2096580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096580).length < 2 ^ (prefixWord ++ tailWord_2096580).sum := by decide
  have hdescent : baseEnd_2096580 < baseStart_2096580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096698 : List Nat := [3, 1, 1, 1, 3, 2, 5, 1, 1, 4]
def baseStart_2096698 : Nat := 118140960795 + 2096698 * 2 ^ 59
def prefixEnd_2096698 : Nat := 4983230072969 + 3 ^ 40 * 2096698 * 2
def baseEnd_2096698 : Nat := 717742574213828595421645

theorem tailTrace_2096698 : CollatzResearch.WordTrace tailWord_2096698 prefixEnd_2096698 717742574213828595421645 := by
  unfold tailWord_2096698
  simp only [CollatzResearch.WordTrace]
  refine ⟨19118214639507177088676687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50981905705352472236471165 19118214639507177088676687)
  ·
    refine ⟨28677321959260765633015031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19118214639507177088676687 28677321959260765633015031)
    ·
      refine ⟨43015982938891148449522547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28677321959260765633015031 43015982938891148449522547)
      ·
        refine ⟨64523974408336722674283821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43015982938891148449522547 64523974408336722674283821)
        ·
          refine ⟨24196490403126271002856433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64523974408336722674283821 24196490403126271002856433)
          ·
            refine ⟨18147367802344703252142325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24196490403126271002856433 18147367802344703252142325)
            ·
              refine ⟨1701315731469815929888343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18147367802344703252142325 1701315731469815929888343)
              ·
                refine ⟨2551973597204723894832515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1701315731469815929888343 2551973597204723894832515)
                ·
                  refine ⟨3827960395807085842248773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551973597204723894832515 3827960395807085842248773)
                  ·
                    refine ⟨717742574213828595421645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3827960395807085842248773 717742574213828595421645)
                    ·
                      rfl

theorem cell22_2096698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_2096698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096698 prefixEnd_2096698 := by exact prefixLift 2096698
  have htrace : WordTrace (prefixWord ++ tailWord_2096698) baseStart_2096698 baseEnd_2096698 := by
    simpa [prefixWord, tailWord_2096698, baseEnd_2096698] using wordTrace_append hprefix tailTrace_2096698
  have hstable : (prefixWord ++ tailWord_2096698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096698).length < 2 ^ (prefixWord ++ tailWord_2096698).sum := by decide
  have hdescent : baseEnd_2096698 < baseStart_2096698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096773 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 3, 3]
def baseStart_2096773 : Nat := 118140960795 + 2096773 * 2 ^ 59
def prefixEnd_2096773 : Nat := 4983230072969 + 3 ^ 40 * 2096773 * 2
def baseEnd_2096773 : Nat := 717768248246553399796415

theorem tailTrace_2096773 : CollatzResearch.WordTrace tailWord_2096773 prefixEnd_2096773 717768248246553399796415 := by
  unfold tailWord_2096773
  simp only [CollatzResearch.WordTrace]
  refine ⟨76475594032756996163686973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50983729355171330775791315 76475594032756996163686973)
  ·
    refine ⟨28678347762283873561382615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76475594032756996163686973 28678347762283873561382615)
    ·
      refine ⟨43017521643425810342073923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28678347762283873561382615 43017521643425810342073923)
      ·
        refine ⟨64526282465138715513110885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43017521643425810342073923 64526282465138715513110885)
        ·
          refine ⟨12098677962213509158708291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64526282465138715513110885 12098677962213509158708291)
          ·
            refine ⟨18148016943320263738062437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12098677962213509158708291 18148016943320263738062437)
            ·
              refine ⟨3402753176872549450886707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18148016943320263738062437 3402753176872549450886707)
              ·
                refine ⟨5104129765308824176330061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3402753176872549450886707 5104129765308824176330061)
                ·
                  refine ⟨1914048661990809066123773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5104129765308824176330061 1914048661990809066123773)
                  ·
                    refine ⟨717768248246553399796415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1914048661990809066123773 717768248246553399796415)
                    ·
                      rfl

theorem cell22_2096773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_2096773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096773 prefixEnd_2096773 := by exact prefixLift 2096773
  have htrace : WordTrace (prefixWord ++ tailWord_2096773) baseStart_2096773 baseEnd_2096773 := by
    simpa [prefixWord, tailWord_2096773, baseEnd_2096773] using wordTrace_append hprefix tailTrace_2096773
  have hstable : (prefixWord ++ tailWord_2096773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096773).length < 2 ^ (prefixWord ++ tailWord_2096773).sum := by decide
  have hdescent : baseEnd_2096773 < baseStart_2096773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096850 : List Nat := [3, 2, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_2096850 : Nat := 118140960795 + 2096850 * 2 ^ 59
def prefixEnd_2096850 : Nat := 4983230072969 + 3 ^ 40 * 2096850 * 2
def baseEnd_2096850 : Nat := 717794606920150865621179

theorem tailTrace_2096850 : CollatzResearch.WordTrace tailWord_2096850 prefixEnd_2096850 717794606920150865621179 := by
  unfold tailWord_2096850
  simp only [CollatzResearch.WordTrace]
  refine ⟨19119600613369509578560001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50985601635652025542826669 19119600613369509578560001)
  ·
    refine ⟨14339700460027132183920001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19119600613369509578560001 14339700460027132183920001)
    ·
      refine ⟨10754775345020349137940001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14339700460027132183920001 10754775345020349137940001)
      ·
        refine ⟨8066081508765261853455001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10754775345020349137940001 8066081508765261853455001)
        ·
          refine ⟨6049561131573946390091251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8066081508765261853455001 6049561131573946390091251)
          ·
            refine ⟨9074341697360919585136877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6049561131573946390091251 9074341697360919585136877)
            ·
              refine ⟨3402878136510344844426329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9074341697360919585136877 3402878136510344844426329)
              ·
                refine ⟨2552158602382758633319747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3402878136510344844426329 2552158602382758633319747)
                ·
                  refine ⟨3828237903574137949979621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552158602382758633319747 3828237903574137949979621)
                  ·
                    refine ⟨717794606920150865621179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3828237903574137949979621 717794606920150865621179)
                    ·
                      rfl

theorem cell22_2096850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_2096850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096850 prefixEnd_2096850 := by exact prefixLift 2096850
  have htrace : WordTrace (prefixWord ++ tailWord_2096850) baseStart_2096850 baseEnd_2096850 := by
    simpa [prefixWord, tailWord_2096850, baseEnd_2096850] using wordTrace_append hprefix tailTrace_2096850
  have hstable : (prefixWord ++ tailWord_2096850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096850).length < 2 ^ (prefixWord ++ tailWord_2096850).sum := by decide
  have hdescent : baseEnd_2096850 < baseStart_2096850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096867 : List Nat := [1, 1, 1, 7, 2, 1, 3, 1, 1, 4]
def baseStart_2096867 : Nat := 118140960795 + 2096867 * 2 ^ 59
def prefixEnd_2096867 : Nat := 4983230072969 + 3 ^ 40 * 2096867 * 2
def baseEnd_2096867 : Nat := 717800426367568487946127

theorem tailTrace_2096867 : CollatzResearch.WordTrace tailWord_2096867 prefixEnd_2096867 717800426367568487946127 := by
  unfold tailWord_2096867
  simp only [CollatzResearch.WordTrace]
  refine ⟨76479022494416450217608855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50986014996277633478405903 76479022494416450217608855)
  ·
    refine ⟨114718533741624675326413283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76479022494416450217608855 114718533741624675326413283)
    ·
      refine ⟨172077800612437012989619925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114718533741624675326413283 172077800612437012989619925)
      ·
        refine ⟨4033073451853992491944217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 172077800612437012989619925 4033073451853992491944217)
        ·
          refine ⟨3024805088890494368958163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4033073451853992491944217 3024805088890494368958163)
          ·
            refine ⟨4537207633335741553437245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024805088890494368958163 4537207633335741553437245)
            ·
              refine ⟨1701452862500903082538967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4537207633335741553437245 1701452862500903082538967)
              ·
                refine ⟨2552179293751354623808451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1701452862500903082538967 2552179293751354623808451)
                ·
                  refine ⟨3828268940627031935712677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552179293751354623808451 3828268940627031935712677)
                  ·
                    refine ⟨717800426367568487946127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3828268940627031935712677 717800426367568487946127)
                    ·
                      rfl

theorem cell22_2096867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 1, 4].length) (baseStart_2096867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096867 prefixEnd_2096867 := by exact prefixLift 2096867
  have htrace : WordTrace (prefixWord ++ tailWord_2096867) baseStart_2096867 baseEnd_2096867 := by
    simpa [prefixWord, tailWord_2096867, baseEnd_2096867] using wordTrace_append hprefix tailTrace_2096867
  have hstable : (prefixWord ++ tailWord_2096867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096867).length < 2 ^ (prefixWord ++ tailWord_2096867).sum := by decide
  have hdescent : baseEnd_2096867 < baseStart_2096867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096878 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2096878 : Nat := 118140960795 + 2096878 * 2 ^ 59
def prefixEnd_2096878 : Nat := 4983230072969 + 3 ^ 40 * 2096878 * 2
def baseEnd_2096878 : Nat := 717804191892368125921093

theorem tailTrace_2096878 : CollatzResearch.WordTrace tailWord_2096878 prefixEnd_2096878 717804191892368125921093 := by
  unfold tailWord_2096878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9559927962172074887032411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50986282464917732730839525 9559927962172074887032411)
  ·
    refine ⟨14339891943258112330548617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9559927962172074887032411 14339891943258112330548617)
    ·
      refine ⟨10754918957443584247911463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14339891943258112330548617 10754918957443584247911463)
      ·
        refine ⟨16132378436165376371867195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10754918957443584247911463 16132378436165376371867195)
        ·
          refine ⟨24198567654248064557800793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16132378436165376371867195 24198567654248064557800793)
          ·
            refine ⟨18148925740686048418350595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24198567654248064557800793 18148925740686048418350595)
            ·
              refine ⟨27223388611029072627525893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18148925740686048418350595 27223388611029072627525893)
              ·
                refine ⟨5104385364567951117661105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27223388611029072627525893 5104385364567951117661105)
                ·
                  refine ⟨3828289023425963338245829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5104385364567951117661105 3828289023425963338245829)
                  ·
                    refine ⟨717804191892368125921093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3828289023425963338245829 717804191892368125921093)
                    ·
                      rfl

theorem cell22_2096878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2096878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096878 prefixEnd_2096878 := by exact prefixLift 2096878
  have htrace : WordTrace (prefixWord ++ tailWord_2096878) baseStart_2096878 baseEnd_2096878 := by
    simpa [prefixWord, tailWord_2096878, baseEnd_2096878] using wordTrace_append hprefix tailTrace_2096878
  have hstable : (prefixWord ++ tailWord_2096878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096878).length < 2 ^ (prefixWord ++ tailWord_2096878).sum := by decide
  have hdescent : baseEnd_2096878 < baseStart_2096878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096908 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 5, 3]
def baseStart_2096908 : Nat := 118140960795 + 2096908 * 2 ^ 59
def prefixEnd_2096908 : Nat := 4983230072969 + 3 ^ 40 * 2096908 * 2
def baseEnd_2096908 : Nat := 717814461505458047671001

theorem tailTrace_2096908 : CollatzResearch.WordTrace tailWord_2096908 prefixEnd_2096908 717814461505458047671001 := by
  unfold tailWord_2096908
  simp only [CollatzResearch.WordTrace]
  refine ⟨38240258943633957109925689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50987011924845276146567585 38240258943633957109925689)
  ·
    refine ⟨28680194207725467832444267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38240258943633957109925689 28680194207725467832444267)
    ·
      refine ⟨43020291311588201748666401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28680194207725467832444267 43020291311588201748666401)
      ·
        refine ⟨32265218483691151311499801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43020291311588201748666401 32265218483691151311499801)
        ·
          refine ⟨24198913862768363483624851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32265218483691151311499801 24198913862768363483624851)
          ·
            refine ⟨36298370794152545225437277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24198913862768363483624851 36298370794152545225437277)
            ·
              refine ⟨13611889047807204459538979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36298370794152545225437277 13611889047807204459538979)
              ·
                refine ⟨20417833571710806689308469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13611889047807204459538979 20417833571710806689308469)
                ·
                  refine ⟨1914171897347888127122669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20417833571710806689308469 1914171897347888127122669)
                  ·
                    refine ⟨717814461505458047671001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1914171897347888127122669 717814461505458047671001)
                    ·
                      rfl

theorem cell22_2096908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_2096908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096908 prefixEnd_2096908 := by exact prefixLift 2096908
  have htrace : WordTrace (prefixWord ++ tailWord_2096908) baseStart_2096908 baseEnd_2096908 := by
    simpa [prefixWord, tailWord_2096908, baseEnd_2096908] using wordTrace_append hprefix tailTrace_2096908
  have hstable : (prefixWord ++ tailWord_2096908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096908).length < 2 ^ (prefixWord ++ tailWord_2096908).sum := by decide
  have hdescent : baseEnd_2096908 < baseStart_2096908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096916 : List Nat := [2, 4, 4, 1, 1, 1, 2, 3, 4]
def baseStart_2096916 : Nat := 118140960795 + 2096916 * 2 ^ 59
def prefixEnd_2096916 : Nat := 4983230072969 + 3 ^ 40 * 2096916 * 2
def baseEnd_2096916 : Nat := 239272400022982897823659

theorem tailTrace_2096916 : CollatzResearch.WordTrace tailWord_2096916 prefixEnd_2096916 239272400022982897823659 := by
  unfold tailWord_2096916
  simp only [CollatzResearch.WordTrace]
  refine ⟨38240404835619465793071301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50987206447492621057428401 38240404835619465793071301)
  ·
    refine ⟨7170075906678649836200869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38240404835619465793071301 7170075906678649836200869)
    ·
      refine ⟨1344389232502246844287663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7170075906678649836200869 1344389232502246844287663)
      ·
        refine ⟨2016583848753370266431495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1344389232502246844287663 2016583848753370266431495)
        ·
          refine ⟨3024875773130055399647243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2016583848753370266431495 3024875773130055399647243)
          ·
            refine ⟨4537313659695083099470865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024875773130055399647243 4537313659695083099470865)
            ·
              refine ⟨3402985244771312324603149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4537313659695083099470865 3402985244771312324603149)
              ·
                refine ⟨1276119466789242121726181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3402985244771312324603149 1276119466789242121726181)
                ·
                  refine ⟨239272400022982897823659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1276119466789242121726181 239272400022982897823659)
                  ·
                    rfl

theorem cell22_2096916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_2096916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096916 prefixEnd_2096916 := by exact prefixLift 2096916
  have htrace : WordTrace (prefixWord ++ tailWord_2096916) baseStart_2096916 baseEnd_2096916 := by
    simpa [prefixWord, tailWord_2096916, baseEnd_2096916] using wordTrace_append hprefix tailTrace_2096916
  have hstable : (prefixWord ++ tailWord_2096916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096916).length < 2 ^ (prefixWord ++ tailWord_2096916).sum := by decide
  have hdescent : baseEnd_2096916 < baseStart_2096916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2096951 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 2, 8]
def baseStart_2096951 : Nat := 118140960795 + 2096951 * 2 ^ 59
def prefixEnd_2096951 : Nat := 4983230072969 + 3 ^ 40 * 2096951 * 2
def baseEnd_2096951 : Nat := 717829181284220268845869

theorem tailTrace_2096951 : CollatzResearch.WordTrace tailWord_2096951 prefixEnd_2096951 717829181284220268845869 := by
  unfold tailWord_2096951
  simp only [CollatzResearch.WordTrace]
  refine ⟨76482086226112132563666707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50988057484074755042444471 76482086226112132563666707)
  ·
    refine ⟨114723129339168198845500061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76482086226112132563666707 114723129339168198845500061)
    ·
      refine ⟨43021173502188074567062523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114723129339168198845500061 43021173502188074567062523)
      ·
        refine ⟨64531760253282111850593785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43021173502188074567062523 64531760253282111850593785)
        ·
          refine ⟨48398820189961583887945339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64531760253282111850593785 48398820189961583887945339)
          ·
            refine ⟨72598230284942375831918009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48398820189961583887945339 72598230284942375831918009)
            ·
              refine ⟨54448672713706781873938507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72598230284942375831918009 54448672713706781873938507)
              ·
                refine ⟨81673009070560172810907761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54448672713706781873938507 81673009070560172810907761)
                ·
                  refine ⟨61254756802920129608180821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81673009070560172810907761 61254756802920129608180821)
                  ·
                    refine ⟨717829181284220268845869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61254756802920129608180821 717829181284220268845869)
                    ·
                      rfl

theorem cell22_2096951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_2096951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2096951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2096951 prefixEnd_2096951 := by exact prefixLift 2096951
  have htrace : WordTrace (prefixWord ++ tailWord_2096951) baseStart_2096951 baseEnd_2096951 := by
    simpa [prefixWord, tailWord_2096951, baseEnd_2096951] using wordTrace_append hprefix tailTrace_2096951
  have hstable : (prefixWord ++ tailWord_2096951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2096951).length < 2 ^ (prefixWord ++ tailWord_2096951).sum := by decide
  have hdescent : baseEnd_2096951 < baseStart_2096951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2096951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097028 : List Nat := [2, 3, 2, 1, 1, 1, 4, 8]
def baseStart_2097028 : Nat := 118140960795 + 2097028 * 2 ^ 59
def prefixEnd_2097028 : Nat := 4983230072969 + 3 ^ 40 * 2097028 * 2
def baseEnd_2097028 : Nat := 79761726661979748296737

theorem tailTrace_2097028 : CollatzResearch.WordTrace tailWord_2097028 prefixEnd_2097028 79761726661979748296737 := by
  unfold tailWord_2097028
  simp only [CollatzResearch.WordTrace]
  refine ⟨38242447323416587357109869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50989929764555449809479825 38242447323416587357109869)
  ·
    refine ⟨14340917746281220258916201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38242447323416587357109869 14340917746281220258916201)
    ·
      refine ⟨10755688309710915194187151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14340917746281220258916201 10755688309710915194187151)
      ·
        refine ⟨16133532464566372791280727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10755688309710915194187151 16133532464566372791280727)
        ·
          refine ⟨24200298696849559186921091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16133532464566372791280727 24200298696849559186921091)
          ·
            refine ⟨36300448045274338780381637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24200298696849559186921091 36300448045274338780381637)
            ·
              refine ⟨6806334008488938521321557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36300448045274338780381637 6806334008488938521321557)
              ·
                refine ⟨79761726661979748296737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6806334008488938521321557 79761726661979748296737)
                ·
                  rfl

theorem cell22_2097028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 8].length) (baseStart_2097028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097028 prefixEnd_2097028 := by exact prefixLift 2097028
  have htrace : WordTrace (prefixWord ++ tailWord_2097028) baseStart_2097028 baseEnd_2097028 := by
    simpa [prefixWord, tailWord_2097028, baseEnd_2097028] using wordTrace_append hprefix tailTrace_2097028
  have hstable : (prefixWord ++ tailWord_2097028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097028).length < 2 ^ (prefixWord ++ tailWord_2097028).sum := by decide
  have hdescent : baseEnd_2097028 < baseStart_2097028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097077 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 3, 3]
def baseStart_2097077 : Nat := 118140960795 + 2097077 * 2 ^ 59
def prefixEnd_2097077 : Nat := 4983230072969 + 3 ^ 40 * 2097077 * 2
def baseEnd_2097077 : Nat := 717872313659197940195483

theorem tailTrace_2097077 : CollatzResearch.WordTrace tailWord_2097077 prefixEnd_2097077 717872313659197940195483 := by
  unfold tailWord_2097077
  simp only [CollatzResearch.WordTrace]
  refine ⟨76486681823655656082753485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50991121215770437388502323 76486681823655656082753485)
  ·
    refine ⟨28682505683870871031032557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76486681823655656082753485 28682505683870871031032557)
    ·
      refine ⟨10755939631451576636637209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28682505683870871031032557 10755939631451576636637209)
      ·
        refine ⟨8066954723588682477477907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10755939631451576636637209 8066954723588682477477907)
        ·
          refine ⟨12100432085383023716216861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8066954723588682477477907 12100432085383023716216861)
          ·
            refine ⟨4537662032018633893581323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12100432085383023716216861 4537662032018633893581323)
            ·
              refine ⟨6806493048027950840371985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4537662032018633893581323 6806493048027950840371985)
              ·
                refine ⟨5104869786020963130278989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6806493048027950840371985 5104869786020963130278989)
                ·
                  refine ⟨1914326169757861173854621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5104869786020963130278989 1914326169757861173854621)
                  ·
                    refine ⟨717872313659197940195483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1914326169757861173854621 717872313659197940195483)
                    ·
                      rfl

theorem cell22_2097077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_2097077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097077 prefixEnd_2097077 := by exact prefixLift 2097077
  have htrace : WordTrace (prefixWord ++ tailWord_2097077) baseStart_2097077 baseEnd_2097077 := by
    simpa [prefixWord, tailWord_2097077, baseEnd_2097077] using wordTrace_append hprefix tailTrace_2097077
  have hstable : (prefixWord ++ tailWord_2097077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097077).length < 2 ^ (prefixWord ++ tailWord_2097077).sum := by decide
  have hdescent : baseEnd_2097077 < baseStart_2097077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097088 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 1, 7]
def baseStart_2097088 : Nat := 118140960795 + 2097088 * 2 ^ 59
def prefixEnd_2097088 : Nat := 4983230072969 + 3 ^ 40 * 2097088 * 2
def baseEnd_2097088 : Nat := 717876079183997578170449

theorem tailTrace_2097088 : CollatzResearch.WordTrace tailWord_2097088 prefixEnd_2097088 717876079183997578170449 := by
  unfold tailWord_2097088
  simp only [CollatzResearch.WordTrace]
  refine ⟨38243541513307902480701959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50991388684410536640935945 38243541513307902480701959)
  ·
    refine ⟨57365312269961853721052939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38243541513307902480701959 57365312269961853721052939)
    ·
      refine ⟨86047968404942780581579409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57365312269961853721052939 86047968404942780581579409)
      ·
        refine ⟨64535976303707085436184557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86047968404942780581579409 64535976303707085436184557)
        ·
          refine ⟨24200991113890157038569209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64535976303707085436184557 24200991113890157038569209)
          ·
            refine ⟨18150743335417617778926907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24200991113890157038569209 18150743335417617778926907)
            ·
              refine ⟨27226115003126426668390361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18150743335417617778926907 27226115003126426668390361)
              ·
                refine ⟨20419586252344820001292771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27226115003126426668390361 20419586252344820001292771)
                ·
                  refine ⟨30629379378517230001939157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20419586252344820001292771 30629379378517230001939157)
                  ·
                    refine ⟨717876079183997578170449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30629379378517230001939157 717876079183997578170449)
                    ·
                      rfl

theorem cell22_2097088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_2097088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097088 prefixEnd_2097088 := by exact prefixLift 2097088
  have htrace : WordTrace (prefixWord ++ tailWord_2097088) baseStart_2097088 baseEnd_2097088 := by
    simpa [prefixWord, tailWord_2097088, baseEnd_2097088] using wordTrace_append hprefix tailTrace_2097088
  have hstable : (prefixWord ++ tailWord_2097088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097088).length < 2 ^ (prefixWord ++ tailWord_2097088).sum := by decide
  have hdescent : baseEnd_2097088 < baseStart_2097088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097180 : List Nat := [2, 2, 3, 1, 3, 1, 1, 9]
def baseStart_2097180 : Nat := 118140960795 + 2097180 * 2 ^ 59
def prefixEnd_2097180 : Nat := 4983230072969 + 3 ^ 40 * 2097180 * 2
def baseEnd_2097180 : Nat := 79767508073793333874463

theorem tailTrace_2097180 : CollatzResearch.WordTrace tailWord_2097180 prefixEnd_2097180 79767508073793333874463 := by
  unfold tailWord_2097180
  simp only [CollatzResearch.WordTrace]
  refine ⟨38245219271141252336876497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50993625694855003115835329 38245219271141252336876497)
  ·
    refine ⟨28683914453355939252657373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38245219271141252336876497 28683914453355939252657373)
    ·
      refine ⟨10756467920008477219746515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28683914453355939252657373 10756467920008477219746515)
      ·
        refine ⟨16134701880012715829619773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10756467920008477219746515 16134701880012715829619773)
        ·
          refine ⟨6050513205004768436107415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16134701880012715829619773 6050513205004768436107415)
          ·
            refine ⟨9075769807507152654161123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6050513205004768436107415 9075769807507152654161123)
            ·
              refine ⟨13613654711260728981241685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9075769807507152654161123 13613654711260728981241685)
              ·
                refine ⟨79767508073793333874463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13613654711260728981241685 79767508073793333874463)
                ·
                  rfl

theorem cell22_2097180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 9].length) (baseStart_2097180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097180 prefixEnd_2097180 := by exact prefixLift 2097180
  have htrace : WordTrace (prefixWord ++ tailWord_2097180) baseStart_2097180 baseEnd_2097180 := by
    simpa [prefixWord, tailWord_2097180, baseEnd_2097180] using wordTrace_append hprefix tailTrace_2097180
  have hstable : (prefixWord ++ tailWord_2097180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097180).length < 2 ^ (prefixWord ++ tailWord_2097180).sum := by decide
  have hdescent : baseEnd_2097180 < baseStart_2097180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097229 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_2097229 : Nat := 118140960795 + 2097229 * 2 ^ 59
def prefixEnd_2097229 : Nat := 4983230072969 + 3 ^ 40 * 2097229 * 2
def baseEnd_2097229 : Nat := 717924346365520210395017

theorem tailTrace_2097229 : CollatzResearch.WordTrace tailWord_2097229 prefixEnd_2097229 717924346365520210395017 := by
  unfold tailWord_2097229
  simp only [CollatzResearch.WordTrace]
  refine ⟨76492225719104986042286741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50994817146069990694857827 76492225719104986042286741)
  ·
    refine ⟨3585573080583046220732191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76492225719104986042286741 3585573080583046220732191)
    ·
      refine ⟨5378359620874569331098287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3585573080583046220732191 5378359620874569331098287)
      ·
        refine ⟨8067539431311853996647431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5378359620874569331098287 8067539431311853996647431)
        ·
          refine ⟨12101309146967780994971147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8067539431311853996647431 12101309146967780994971147)
          ·
            refine ⟨18151963720451671492456721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12101309146967780994971147 18151963720451671492456721)
            ·
              refine ⟨13613972790338753619342541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18151963720451671492456721 13613972790338753619342541)
              ·
                refine ⟨5105239796377032607253453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13613972790338753619342541 5105239796377032607253453)
                ·
                  refine ⟨1914464923641387227720045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5105239796377032607253453 1914464923641387227720045)
                  ·
                    refine ⟨717924346365520210395017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1914464923641387227720045 717924346365520210395017)
                    ·
                      rfl

theorem cell22_2097229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_2097229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097229 prefixEnd_2097229 := by exact prefixLift 2097229
  have htrace : WordTrace (prefixWord ++ tailWord_2097229) baseStart_2097229 baseEnd_2097229 := by
    simpa [prefixWord, tailWord_2097229, baseEnd_2097229] using wordTrace_append hprefix tailTrace_2097229
  have hstable : (prefixWord ++ tailWord_2097229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097229).length < 2 ^ (prefixWord ++ tailWord_2097229).sum := by decide
  have hdescent : baseEnd_2097229 < baseStart_2097229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097240 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 1, 7]
def baseStart_2097240 : Nat := 118140960795 + 2097240 * 2 ^ 59
def prefixEnd_2097240 : Nat := 4983230072969 + 3 ^ 40 * 2097240 * 2
def baseEnd_2097240 : Nat := 717928111890319848369983

theorem tailTrace_2097240 : CollatzResearch.WordTrace tailWord_2097240 prefixEnd_2097240 717928111890319848369983 := by
  unfold tailWord_2097240
  simp only [CollatzResearch.WordTrace]
  refine ⟨38246313461032567460468587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50995084614710089947291449 38246313461032567460468587)
  ·
    refine ⟨57369470191548851190702881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38246313461032567460468587 57369470191548851190702881)
    ·
      refine ⟨43027102643661638393027161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57369470191548851190702881 43027102643661638393027161)
      ·
        refine ⟨32270326982746228794770371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43027102643661638393027161 32270326982746228794770371)
        ·
          refine ⟨48405490474119343192155557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32270326982746228794770371 48405490474119343192155557)
          ·
            refine ⟨9076029463897376848529167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48405490474119343192155557 9076029463897376848529167)
            ·
              refine ⟨13614044195846065272793751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9076029463897376848529167 13614044195846065272793751)
              ·
                refine ⟨20421066293769097909190627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13614044195846065272793751 20421066293769097909190627)
                ·
                  refine ⟨30631599440653646863785941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20421066293769097909190627 30631599440653646863785941)
                  ·
                    refine ⟨717928111890319848369983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30631599440653646863785941 717928111890319848369983)
                    ·
                      rfl

theorem cell22_2097240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_2097240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097240 prefixEnd_2097240 := by exact prefixLift 2097240
  have htrace : WordTrace (prefixWord ++ tailWord_2097240) baseStart_2097240 baseEnd_2097240 := by
    simpa [prefixWord, tailWord_2097240, baseEnd_2097240] using wordTrace_append hprefix tailTrace_2097240
  have hstable : (prefixWord ++ tailWord_2097240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097240).length < 2 ^ (prefixWord ++ tailWord_2097240).sum := by decide
  have hdescent : baseEnd_2097240 < baseStart_2097240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097306 : List Nat := [3, 1, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_2097306 : Nat := 118140960795 + 2097306 * 2 ^ 59
def prefixEnd_2097306 : Nat := 4983230072969 + 3 ^ 40 * 2097306 * 2
def baseEnd_2097306 : Nat := 717950705039117676219781

theorem tailTrace_2097306 : CollatzResearch.WordTrace tailWord_2097306 prefixEnd_2097306 717950705039117676219781 := by
  unfold tailWord_2097306
  simp only [CollatzResearch.WordTrace]
  refine ⟨19123758534956507048209943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50996689426550685461893181 19123758534956507048209943)
  ·
    refine ⟨28685637802434760572314915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19123758534956507048209943 28685637802434760572314915)
    ·
      refine ⟨43028456703652140858472373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28685637802434760572314915 43028456703652140858472373)
      ·
        refine ⟨4033917815967388205481785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43028456703652140858472373 4033917815967388205481785)
        ·
          refine ⟨3025438361975541154111339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4033917815967388205481785 3025438361975541154111339)
          ·
            refine ⟨4538157542963311731167009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025438361975541154111339 4538157542963311731167009)
            ·
              refine ⟨3403618157222483798375257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4538157542963311731167009 3403618157222483798375257)
              ·
                refine ⟨2552713617916862848781443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3403618157222483798375257 2552713617916862848781443)
                ·
                  refine ⟨3829070426875294273172165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552713617916862848781443 3829070426875294273172165)
                  ·
                    refine ⟨717950705039117676219781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3829070426875294273172165 717950705039117676219781)
                    ·
                      rfl

theorem cell22_2097306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_2097306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097306 prefixEnd_2097306 := by exact prefixLift 2097306
  have htrace : WordTrace (prefixWord ++ tailWord_2097306) baseStart_2097306 baseEnd_2097306 := by
    simpa [prefixWord, tailWord_2097306, baseEnd_2097306] using wordTrace_append hprefix tailTrace_2097306
  have hstable : (prefixWord ++ tailWord_2097306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097306).length < 2 ^ (prefixWord ++ tailWord_2097306).sum := by decide
  have hdescent : baseEnd_2097306 < baseStart_2097306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097317 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_2097317 : Nat := 118140960795 + 2097317 * 2 ^ 59
def prefixEnd_2097317 : Nat := 4983230072969 + 3 ^ 40 * 2097317 * 2
def baseEnd_2097317 : Nat := 717954470563917314194747

theorem tailTrace_2097317 : CollatzResearch.WordTrace tailWord_2097317 prefixEnd_2097317 717954470563917314194747 := by
  unfold tailWord_2097317
  simp only [CollatzResearch.WordTrace]
  refine ⟨76495435342786177071490205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50996956895190784714326803 76495435342786177071490205)
  ·
    refine ⟨28685788253544816401808827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76495435342786177071490205 28685788253544816401808827)
    ·
      refine ⟨43028682380317224602713241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28685788253544816401808827 43028682380317224602713241)
      ·
        refine ⟨32271511785237918452034931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43028682380317224602713241 32271511785237918452034931)
        ·
          refine ⟨48407267677856877678052397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32271511785237918452034931 48407267677856877678052397)
          ·
            refine ⟨18152725379196329129269649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48407267677856877678052397 18152725379196329129269649)
            ·
              refine ⟨13614544034397246846952237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18152725379196329129269649 13614544034397246846952237)
              ·
                refine ⟨5105454012898967567607089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13614544034397246846952237 5105454012898967567607089)
                ·
                  refine ⟨3829090509674225675705317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5105454012898967567607089 3829090509674225675705317)
                  ·
                    refine ⟨717954470563917314194747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3829090509674225675705317 717954470563917314194747)
                    ·
                      rfl

theorem cell22_2097317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_2097317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097317 prefixEnd_2097317 := by exact prefixLift 2097317
  have htrace : WordTrace (prefixWord ++ tailWord_2097317) baseStart_2097317 baseEnd_2097317 := by
    simpa [prefixWord, tailWord_2097317, baseEnd_2097317] using wordTrace_append hprefix tailTrace_2097317
  have hstable : (prefixWord ++ tailWord_2097317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097317).length < 2 ^ (prefixWord ++ tailWord_2097317).sum := by decide
  have hdescent : baseEnd_2097317 < baseStart_2097317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097394 : List Nat := [3, 2, 1, 3, 2, 1, 1, 4, 5]
def baseStart_2097394 : Nat := 118140960795 + 2097394 * 2 ^ 59
def prefixEnd_2097394 : Nat := 4983230072969 + 3 ^ 40 * 2097394 * 2
def baseEnd_2097394 : Nat := 239326943079171593339837

theorem tailTrace_2097394 : CollatzResearch.WordTrace tailWord_2097394 prefixEnd_2097394 239326943079171593339837 := by
  unfold tailWord_2097394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19124560940876804805510809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50998829175671479481362157 19124560940876804805510809)
  ·
    refine ⟨14343420705657603604133107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19124560940876804805510809 14343420705657603604133107)
    ·
      refine ⟨21515131058486405406199661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14343420705657603604133107 21515131058486405406199661)
      ·
        refine ⟨8068174146932402027324873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21515131058486405406199661 8068174146932402027324873)
        ·
          refine ⟨6051130610199301520493655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8068174146932402027324873 6051130610199301520493655)
          ·
            refine ⟨9076695915298952280740483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6051130610199301520493655 9076695915298952280740483)
            ·
              refine ⟨13615043872948428421110725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9076695915298952280740483 13615043872948428421110725)
              ·
                refine ⟨2552820726177830328958261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13615043872948428421110725 2552820726177830328958261)
                ·
                  refine ⟨239326943079171593339837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2552820726177830328958261 239326943079171593339837)
                  ·
                    rfl

theorem cell22_2097394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_2097394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097394 prefixEnd_2097394 := by exact prefixLift 2097394
  have htrace : WordTrace (prefixWord ++ tailWord_2097394) baseStart_2097394 baseEnd_2097394 := by
    simpa [prefixWord, tailWord_2097394, baseEnd_2097394] using wordTrace_append hprefix tailTrace_2097394
  have hstable : (prefixWord ++ tailWord_2097394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097394).length < 2 ^ (prefixWord ++ tailWord_2097394).sum := by decide
  have hdescent : baseEnd_2097394 < baseStart_2097394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097407 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 5, 4]
def baseStart_2097407 : Nat := 118140960795 + 2097407 * 2 ^ 59
def prefixEnd_2097407 : Nat := 4983230072969 + 3 ^ 40 * 2097407 * 2
def baseEnd_2097407 : Nat := 717985279403187079444471

theorem tailTrace_2097407 : CollatzResearch.WordTrace tailWord_2097407 prefixEnd_2097407 717985279403187079444471 := by
  unfold tailWord_2097407
  simp only [CollatzResearch.WordTrace]
  refine ⟨76498717912460122442266475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50999145274973414961510983 76498717912460122442266475)
  ·
    refine ⟨114748076868690183663399713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76498717912460122442266475 114748076868690183663399713)
    ·
      refine ⟨86061057651517637747549785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114748076868690183663399713 86061057651517637747549785)
      ·
        refine ⟨64545793238638228310662339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86061057651517637747549785 64545793238638228310662339)
        ·
          refine ⟨96818689857957342465993509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64545793238638228310662339 96818689857957342465993509)
          ·
            refine ⟨18153504348367001712373783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96818689857957342465993509 18153504348367001712373783)
            ·
              refine ⟨27230256522550502568560675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18153504348367001712373783 27230256522550502568560675)
              ·
                refine ⟨40845384783825753852841013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27230256522550502568560675 40845384783825753852841013)
                ·
                  refine ⟨3829254823483664423703845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40845384783825753852841013 3829254823483664423703845)
                  ·
                    refine ⟨717985279403187079444471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3829254823483664423703845 717985279403187079444471)
                    ·
                      rfl

theorem cell22_2097407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_2097407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097407 prefixEnd_2097407 := by exact prefixLift 2097407
  have htrace : WordTrace (prefixWord ++ tailWord_2097407) baseStart_2097407 baseEnd_2097407 := by
    simpa [prefixWord, tailWord_2097407, baseEnd_2097407] using wordTrace_append hprefix tailTrace_2097407
  have hstable : (prefixWord ++ tailWord_2097407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097407).length < 2 ^ (prefixWord ++ tailWord_2097407).sum := by decide
  have hdescent : baseEnd_2097407 < baseStart_2097407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097441 : List Nat := [1, 2, 3, 2, 1, 1, 6, 1, 1, 4]
def baseStart_2097441 : Nat := 118140960795 + 2097441 * 2 ^ 59
def prefixEnd_2097441 : Nat := 4983230072969 + 3 ^ 40 * 2097441 * 2
def baseEnd_2097441 : Nat := 717996918298022324094367

theorem tailTrace_2097441 : CollatzResearch.WordTrace tailWord_2097441 prefixEnd_2097441 717996918298022324094367 := by
  unfold tailWord_2097441
  simp only [CollatzResearch.WordTrace]
  refine ⟨76499957994336946249004177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50999971996224630832669451 76499957994336946249004177)
  ·
    refine ⟨57374968495752709686753133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76499957994336946249004177 57374968495752709686753133)
    ·
      refine ⟨21515613185907266132532425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57374968495752709686753133 21515613185907266132532425)
      ·
        refine ⟨16136709889430449599399319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21515613185907266132532425 16136709889430449599399319)
        ·
          refine ⟨24205064834145674399098979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16136709889430449599399319 24205064834145674399098979)
          ·
            refine ⟨36307597251218511598648469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24205064834145674399098979 36307597251218511598648469)
            ·
              refine ⟨1701918621150867731186647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36307597251218511598648469 1701918621150867731186647)
              ·
                refine ⟨2552877931726301596779971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1701918621150867731186647 2552877931726301596779971)
                ·
                  refine ⟨3829316897589452395169957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552877931726301596779971 3829316897589452395169957)
                  ·
                    refine ⟨717996918298022324094367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3829316897589452395169957 717996918298022324094367)
                    ·
                      rfl

theorem cell22_2097441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_2097441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097441 prefixEnd_2097441 := by exact prefixLift 2097441
  have htrace : WordTrace (prefixWord ++ tailWord_2097441) baseStart_2097441 baseEnd_2097441 := by
    simpa [prefixWord, tailWord_2097441, baseEnd_2097441] using wordTrace_append hprefix tailTrace_2097441
  have hstable : (prefixWord ++ tailWord_2097441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097441).length < 2 ^ (prefixWord ++ tailWord_2097441).sum := by decide
  have hdescent : baseEnd_2097441 < baseStart_2097441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097497 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 1, 8]
def baseStart_2097497 : Nat := 118140960795 + 2097497 * 2 ^ 59
def prefixEnd_2097497 : Nat := 4983230072969 + 3 ^ 40 * 2097497 * 2
def baseEnd_2097497 : Nat := 718016088242456844694195

theorem tailTrace_2097497 : CollatzResearch.WordTrace tailWord_2097497 prefixEnd_2097497 718016088242456844694195 := by
  unfold tailWord_2097497
  simp only [CollatzResearch.WordTrace]
  refine ⟨76502000482134067813042745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51001333654756045208695163 76502000482134067813042745)
  ·
    refine ⟨57376500361600550859782059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76502000482134067813042745 57376500361600550859782059)
    ·
      refine ⟨86064750542400826289673089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57376500361600550859782059 86064750542400826289673089)
      ·
        refine ⟨64548562906800619717254817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86064750542400826289673089 64548562906800619717254817)
        ·
          refine ⟨48411422180100464787941113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64548562906800619717254817 48411422180100464787941113)
          ·
            refine ⟨36308566635075348590955835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48411422180100464787941113 36308566635075348590955835)
            ·
              refine ⟨54462849952613022886433753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36308566635075348590955835 54462849952613022886433753)
              ·
                refine ⟨40847137464459767164825315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54462849952613022886433753 40847137464459767164825315)
                ·
                  refine ⟨61270706196689650747237973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40847137464459767164825315 61270706196689650747237973)
                  ·
                    refine ⟨718016088242456844694195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61270706196689650747237973 718016088242456844694195)
                    ·
                      rfl

theorem cell22_2097497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_2097497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097497 prefixEnd_2097497 := by exact prefixLift 2097497
  have htrace : WordTrace (prefixWord ++ tailWord_2097497) baseStart_2097497 baseEnd_2097497 := by
    simpa [prefixWord, tailWord_2097497, baseEnd_2097497] using wordTrace_append hprefix tailTrace_2097497
  have hstable : (prefixWord ++ tailWord_2097497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097497).length < 2 ^ (prefixWord ++ tailWord_2097497).sum := by decide
  have hdescent : baseEnd_2097497 < baseStart_2097497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097608 : List Nat := [2, 1, 3, 1, 3, 3, 2, 3, 4]
def baseStart_2097608 : Nat := 118140960795 + 2097608 * 2 ^ 59
def prefixEnd_2097608 : Nat := 4983230072969 + 3 ^ 40 * 2097608 * 2
def baseEnd_2097608 : Nat := 239351361936963185056285

theorem tailTrace_2097608 : CollatzResearch.WordTrace tailWord_2097608 prefixEnd_2097608 239351361936963185056285 := by
  unfold tailWord_2097608
  simp only [CollatzResearch.WordTrace]
  refine ⟨38253024492365966885166739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51004032656487955846888985 38253024492365966885166739)
  ·
    refine ⟨57379536738548950327750109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38253024492365966885166739 57379536738548950327750109)
    ·
      refine ⟨21517326276955856372906291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57379536738548950327750109 21517326276955856372906291)
      ·
        refine ⟨32275989415433784559359437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21517326276955856372906291 32275989415433784559359437)
        ·
          refine ⟨12103496030787669209759789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32275989415433784559359437 12103496030787669209759789)
          ·
            refine ⟨4538811011545375953659921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12103496030787669209759789 4538811011545375953659921)
            ·
              refine ⟨3404108258659031965244941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4538811011545375953659921 3404108258659031965244941)
              ·
                refine ⟨1276540596997136986966853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3404108258659031965244941 1276540596997136986966853)
                ·
                  refine ⟨239351361936963185056285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1276540596997136986966853 239351361936963185056285)
                  ·
                    rfl

theorem cell22_2097608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 4].length) (baseStart_2097608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097608 prefixEnd_2097608 := by exact prefixLift 2097608
  have htrace : WordTrace (prefixWord ++ tailWord_2097608) baseStart_2097608 baseEnd_2097608 := by
    simpa [prefixWord, tailWord_2097608, baseEnd_2097608] using wordTrace_append hprefix tailTrace_2097608
  have hstable : (prefixWord ++ tailWord_2097608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097608).length < 2 ^ (prefixWord ++ tailWord_2097608).sum := by decide
  have hdescent : baseEnd_2097608 < baseStart_2097608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097640 : List Nat := [2, 1, 4, 1, 1, 4, 3, 1, 2, 3]
def baseStart_2097640 : Nat := 118140960795 + 2097640 * 2 ^ 59
def prefixEnd_2097640 : Nat := 4983230072969 + 3 ^ 40 * 2097640 * 2
def baseEnd_2097640 : Nat := 718065040064852138368757

theorem tailTrace_2097640 : CollatzResearch.WordTrace tailWord_2097640 prefixEnd_2097640 718065040064852138368757 := by
  unfold tailWord_2097640
  simp only [CollatzResearch.WordTrace]
  refine ⟨38253608060308001617749187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51004810747077335490332249 38253608060308001617749187)
  ·
    refine ⟨57380412090462002426623781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38253608060308001617749187 57380412090462002426623781)
    ·
      refine ⟨10758827266961625454991959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57380412090462002426623781 10758827266961625454991959)
      ·
        refine ⟨16138240900442438182487939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10758827266961625454991959 16138240900442438182487939)
        ·
          refine ⟨24207361350663657273731909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16138240900442438182487939 24207361350663657273731909)
          ·
            refine ⟨4538880253249435738824733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24207361350663657273731909 4538880253249435738824733)
            ·
              refine ⟨1702080094968538402059275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4538880253249435738824733 1702080094968538402059275)
              ·
                refine ⟨2553120142452807603088913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702080094968538402059275 2553120142452807603088913)
                ·
                  refine ⟨1914840106839605702316685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2553120142452807603088913 1914840106839605702316685)
                  ·
                    refine ⟨718065040064852138368757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1914840106839605702316685 718065040064852138368757)
                    ·
                      rfl

theorem cell22_2097640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_2097640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097640 prefixEnd_2097640 := by exact prefixLift 2097640
  have htrace : WordTrace (prefixWord ++ tailWord_2097640) baseStart_2097640 baseEnd_2097640 := by
    simpa [prefixWord, tailWord_2097640, baseEnd_2097640] using wordTrace_append hprefix tailTrace_2097640
  have hstable : (prefixWord ++ tailWord_2097640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097640).length < 2 ^ (prefixWord ++ tailWord_2097640).sum := by decide
  have hdescent : baseEnd_2097640 < baseStart_2097640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097651 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 3, 3]
def baseStart_2097651 : Nat := 118140960795 + 2097651 * 2 ^ 59
def prefixEnd_2097651 : Nat := 4983230072969 + 3 ^ 40 * 2097651 * 2
def baseEnd_2097651 : Nat := 718068805589651776343723

theorem tailTrace_2097651 : CollatzResearch.WordTrace tailWord_2097651 prefixEnd_2097651 718068805589651776343723 := by
  unfold tailWord_2097651
  simp only [CollatzResearch.WordTrace]
  refine ⟨76507617323576152114148807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51005078215717434742765871 76507617323576152114148807)
  ·
    refine ⟨114761425985364228171223211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76507617323576152114148807 114761425985364228171223211)
    ·
      refine ⟨172142138978046342256834817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114761425985364228171223211 172142138978046342256834817)
      ·
        refine ⟨129106604233534756692626113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172142138978046342256834817 129106604233534756692626113)
        ·
          refine ⟨96829953175151067519469585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129106604233534756692626113 96829953175151067519469585)
          ·
            refine ⟨72622464881363300639602189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96829953175151067519469585 72622464881363300639602189)
            ·
              refine ⟨27233424330511237739850821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72622464881363300639602189 27233424330511237739850821)
              ·
                refine ⟨5106267061970857076222029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27233424330511237739850821 5106267061970857076222029)
                ·
                  refine ⟨1914850148239071403583261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5106267061970857076222029 1914850148239071403583261)
                  ·
                    refine ⟨718068805589651776343723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1914850148239071403583261 718068805589651776343723)
                    ·
                      rfl

theorem cell22_2097651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 3].length) (baseStart_2097651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097651 prefixEnd_2097651 := by exact prefixLift 2097651
  have htrace : WordTrace (prefixWord ++ tailWord_2097651) baseStart_2097651 baseEnd_2097651 := by
    simpa [prefixWord, tailWord_2097651, baseEnd_2097651] using wordTrace_append hprefix tailTrace_2097651
  have hstable : (prefixWord ++ tailWord_2097651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097651).length < 2 ^ (prefixWord ++ tailWord_2097651).sum := by decide
  have hdescent : baseEnd_2097651 < baseStart_2097651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097653 : List Nat := [1, 3, 5, 1, 2, 1, 1, 8]
def baseStart_2097653 : Nat := 118140960795 + 2097653 * 2 ^ 59
def prefixEnd_2097653 : Nat := 4983230072969 + 3 ^ 40 * 2097653 * 2
def baseEnd_2097653 : Nat := 79785498914502715310413

theorem tailTrace_2097653 : CollatzResearch.WordTrace tailWord_2097653 prefixEnd_2097653 79785498914502715310413 := by
  unfold tailWord_2097653
  simp only [CollatzResearch.WordTrace]
  refine ⟨76507690269568906455721613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51005126846379270970481075 76507690269568906455721613)
  ·
    refine ⟨28690383851088339920895605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76507690269568906455721613 28690383851088339920895605)
    ·
      refine ⟨2689723486039531867583963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28690383851088339920895605 2689723486039531867583963)
      ·
        refine ⟨4034585229059297801375945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2689723486039531867583963 4034585229059297801375945)
        ·
          refine ⟨3025938921794473351031959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4034585229059297801375945 3025938921794473351031959)
          ·
            refine ⟨4538908382691710026547939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025938921794473351031959 4538908382691710026547939)
            ·
              refine ⟨6808362574037565039821909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4538908382691710026547939 6808362574037565039821909)
              ·
                refine ⟨79785498914502715310413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6808362574037565039821909 79785498914502715310413)
                ·
                  rfl

theorem cell22_2097653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 8].length) (baseStart_2097653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097653 prefixEnd_2097653 := by exact prefixLift 2097653
  have htrace : WordTrace (prefixWord ++ tailWord_2097653) baseStart_2097653 baseEnd_2097653 := by
    simpa [prefixWord, tailWord_2097653, baseEnd_2097653] using wordTrace_append hprefix tailTrace_2097653
  have hstable : (prefixWord ++ tailWord_2097653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097653).length < 2 ^ (prefixWord ++ tailWord_2097653).sum := by decide
  have hdescent : baseEnd_2097653 < baseStart_2097653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097670 : List Nat := [6, 2, 1, 1, 1, 1, 10]
def baseStart_2097670 : Nat := 118140960795 + 2097670 * 2 ^ 59
def prefixEnd_2097670 : Nat := 4983230072969 + 3 ^ 40 * 2097670 * 2
def baseEnd_2097670 : Nat := 26595381839923780004395

theorem tailTrace_2097670 : CollatzResearch.WordTrace tailWord_2097670 prefixEnd_2097670 26595381839923780004395 := by
  unfold tailWord_2097670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2390884697203353698721577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51005540207004878906060309 2390884697203353698721577)
  ·
    refine ⟨1793163522902515274041183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2390884697203353698721577 1793163522902515274041183)
    ·
      refine ⟨2689745284353772911061775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1793163522902515274041183 2689745284353772911061775)
      ·
        refine ⟨4034617926530659366592663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2689745284353772911061775 4034617926530659366592663)
        ·
          refine ⟨6051926889795989049888995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4034617926530659366592663 6051926889795989049888995)
          ·
            refine ⟨9077890334693983574833493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6051926889795989049888995 9077890334693983574833493)
            ·
              refine ⟨26595381839923780004395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9077890334693983574833493 26595381839923780004395)
              ·
                rfl

theorem cell22_2097670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 10].length) (baseStart_2097670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097670 prefixEnd_2097670 := by exact prefixLift 2097670
  have htrace : WordTrace (prefixWord ++ tailWord_2097670) baseStart_2097670 baseEnd_2097670 := by
    simpa [prefixWord, tailWord_2097670, baseEnd_2097670] using wordTrace_append hprefix tailTrace_2097670
  have hstable : (prefixWord ++ tailWord_2097670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097670).length < 2 ^ (prefixWord ++ tailWord_2097670).sum := by decide
  have hdescent : baseEnd_2097670 < baseStart_2097670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097773 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_2097773 : Nat := 118140960795 + 2097773 * 2 ^ 59
def prefixEnd_2097773 : Nat := 4983230072969 + 3 ^ 40 * 2097773 * 2
def baseEnd_2097773 : Nat := 718110568682884124793349

theorem tailTrace_2097773 : CollatzResearch.WordTrace tailWord_2097773 prefixEnd_2097773 718110568682884124793349 := by
  unfold tailWord_2097773
  simp only [CollatzResearch.WordTrace]
  refine ⟨76512067029134166950089973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51008044686089444633393315 76512067029134166950089973)
  ·
    refine ⟨7173006283981328151570935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76512067029134166950089973 7173006283981328151570935)
    ·
      refine ⟨10759509425971992227356403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7173006283981328151570935 10759509425971992227356403)
      ·
        refine ⟨16139264138957988341034605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10759509425971992227356403 16139264138957988341034605)
        ·
          refine ⟨6052224052109245627887977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16139264138957988341034605 6052224052109245627887977)
          ·
            refine ⟨4539168039081934220915983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6052224052109245627887977 4539168039081934220915983)
            ·
              refine ⟨6808752058622901331373975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4539168039081934220915983 6808752058622901331373975)
              ·
                refine ⟨10213128087934351997060963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6808752058622901331373975 10213128087934351997060963)
                ·
                  refine ⟨15319692131901527995591445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10213128087934351997060963 15319692131901527995591445)
                  ·
                    refine ⟨718110568682884124793349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15319692131901527995591445 718110568682884124793349)
                    ·
                      rfl

theorem cell22_2097773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_2097773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097773 prefixEnd_2097773 := by exact prefixLift 2097773
  have htrace : WordTrace (prefixWord ++ tailWord_2097773) baseStart_2097773 baseEnd_2097773 := by
    simpa [prefixWord, tailWord_2097773, baseEnd_2097773] using wordTrace_append hprefix tailTrace_2097773
  have hstable : (prefixWord ++ tailWord_2097773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097773).length < 2 ^ (prefixWord ++ tailWord_2097773).sum := by decide
  have hdescent : baseEnd_2097773 < baseStart_2097773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097794 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 6]
def baseStart_2097794 : Nat := 118140960795 + 2097794 * 2 ^ 59
def prefixEnd_2097794 : Nat := 4983230072969 + 3 ^ 40 * 2097794 * 2
def baseEnd_2097794 : Nat := 239372585804015690006095

theorem tailTrace_2097794 : CollatzResearch.WordTrace tailWord_2097794 prefixEnd_2097794 239372585804015690006095 := by
  unfold tailWord_2097794
  simp only [CollatzResearch.WordTrace]
  refine ⟨19128208240514521884151109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51008555308038725024402957 19128208240514521884151109)
  ·
    refine ⟨3586539045096472853278333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19128208240514521884151109 3586539045096472853278333)
    ·
      refine ⟨1344952141911177319979375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3586539045096472853278333 1344952141911177319979375)
      ·
        refine ⟨2017428212866765979969063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1344952141911177319979375 2017428212866765979969063)
        ·
          refine ⟨3026142319300148969953595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2017428212866765979969063 3026142319300148969953595)
          ·
            refine ⟨4539213478950223454930393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026142319300148969953595 4539213478950223454930393)
            ·
              refine ⟨3404410109212667591197795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4539213478950223454930393 3404410109212667591197795)
              ·
                refine ⟨5106615163819001386796693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404410109212667591197795 5106615163819001386796693)
                ·
                  refine ⟨239372585804015690006095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5106615163819001386796693 239372585804015690006095)
                  ·
                    rfl

theorem cell22_2097794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_2097794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097794 prefixEnd_2097794 := by exact prefixLift 2097794
  have htrace : WordTrace (prefixWord ++ tailWord_2097794) baseStart_2097794 baseEnd_2097794 := by
    simpa [prefixWord, tailWord_2097794, baseEnd_2097794] using wordTrace_append hprefix tailTrace_2097794
  have hstable : (prefixWord ++ tailWord_2097794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097794).length < 2 ^ (prefixWord ++ tailWord_2097794).sum := by decide
  have hdescent : baseEnd_2097794 < baseStart_2097794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097820 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 3, 3]
def baseStart_2097820 : Nat := 118140960795 + 2097820 * 2 ^ 59
def prefixEnd_2097820 : Nat := 4983230072969 + 3 ^ 40 * 2097820 * 2
def baseEnd_2097820 : Nat := 718126657743391668868205

theorem tailTrace_2097820 : CollatzResearch.WordTrace tailWord_2097820 prefixEnd_2097820 718126657743391668868205 := by
  unfold tailWord_2097820
  simp only [CollatzResearch.WordTrace]
  refine ⟨38256890629981946988525457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51009187506642595984700609 38256890629981946988525457)
  ·
    refine ⟨28692667972486460241394093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38256890629981946988525457 28692667972486460241394093)
    ·
      refine ⟨10759750489682422590522785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28692667972486460241394093 10759750489682422590522785)
      ·
        refine ⟨8069812867261816942892089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10759750489682422590522785 8069812867261816942892089)
        ·
          refine ⟨6052359650446362707169067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8069812867261816942892089 6052359650446362707169067)
          ·
            refine ⟨9078539475669544060753601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6052359650446362707169067 9078539475669544060753601)
            ·
              refine ⟨6808904606752158045565201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9078539475669544060753601 6808904606752158045565201)
              ·
                refine ⟨5106678455064118534173901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6808904606752158045565201 5106678455064118534173901)
                ·
                  refine ⟨1915004420649044450315213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5106678455064118534173901 1915004420649044450315213)
                  ·
                    refine ⟨718126657743391668868205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1915004420649044450315213 718126657743391668868205)
                    ·
                      rfl

theorem cell22_2097820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_2097820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097820 prefixEnd_2097820 := by exact prefixLift 2097820
  have htrace : WordTrace (prefixWord ++ tailWord_2097820) baseStart_2097820 baseEnd_2097820 := by
    simpa [prefixWord, tailWord_2097820, baseEnd_2097820] using wordTrace_append hprefix tailTrace_2097820
  have hstable : (prefixWord ++ tailWord_2097820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097820).length < 2 ^ (prefixWord ++ tailWord_2097820).sum := by decide
  have hdescent : baseEnd_2097820 < baseStart_2097820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097854 : List Nat := [4, 2, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_2097854 : Nat := 118140960795 + 2097854 * 2 ^ 59
def prefixEnd_2097854 : Nat := 4983230072969 + 3 ^ 40 * 2097854 * 2
def baseEnd_2097854 : Nat := 718138296638226913518101

theorem tailTrace_2097854 : CollatzResearch.WordTrace tailWord_2097854 prefixEnd_2097854 718138296638226913518101 := by
  unfold tailWord_2097854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9564377667730089722973577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51010014227893811855859077 9564377667730089722973577)
  ·
    refine ⟨7173283250797567292230183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9564377667730089722973577 7173283250797567292230183)
    ·
      refine ⟨10759924876196350938345275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7173283250797567292230183 10759924876196350938345275)
      ·
        refine ⟨16139887314294526407517913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10759924876196350938345275 16139887314294526407517913)
        ·
          refine ⟨12104915485720894805638435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16139887314294526407517913 12104915485720894805638435)
          ·
            refine ⟨18157373228581342208457653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12104915485720894805638435 18157373228581342208457653)
            ·
              refine ⟨1702253740179500832042905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18157373228581342208457653 1702253740179500832042905)
              ·
                refine ⟨1276690305134625624032179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1702253740179500832042905 1276690305134625624032179)
                ·
                  refine ⟨1915035457701938436048269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276690305134625624032179 1915035457701938436048269)
                  ·
                    refine ⟨718138296638226913518101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1915035457701938436048269 718138296638226913518101)
                    ·
                      rfl

theorem cell22_2097854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_2097854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097854 prefixEnd_2097854 := by exact prefixLift 2097854
  have htrace : WordTrace (prefixWord ++ tailWord_2097854) baseStart_2097854 baseEnd_2097854 := by
    simpa [prefixWord, tailWord_2097854, baseEnd_2097854] using wordTrace_append hprefix tailTrace_2097854
  have hstable : (prefixWord ++ tailWord_2097854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097854).length < 2 ^ (prefixWord ++ tailWord_2097854).sum := by decide
  have hdescent : baseEnd_2097854 < baseStart_2097854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097880 : List Nat := [2, 1, 2, 2, 3, 2, 3, 2, 1, 4]
def baseStart_2097880 : Nat := 118140960795 + 2097880 * 2 ^ 59
def prefixEnd_2097880 : Nat := 4983230072969 + 3 ^ 40 * 2097880 * 2
def baseEnd_2097880 : Nat := 718147196969571512368021

theorem tailTrace_2097880 : CollatzResearch.WordTrace tailWord_2097880 prefixEnd_2097880 718147196969571512368021 := by
  unfold tailWord_2097880
  simp only [CollatzResearch.WordTrace]
  refine ⟨38257984819873262112117547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51010646426497682816156729 38257984819873262112117547)
  ·
    refine ⟨57386977229809893168176321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38257984819873262112117547 57386977229809893168176321)
    ·
      refine ⟨43040232922357419876132241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57386977229809893168176321 43040232922357419876132241)
      ·
        refine ⟨32280174691768064907099181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43040232922357419876132241 32280174691768064907099181)
        ·
          refine ⟨12105065509413024340162193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32280174691768064907099181 12105065509413024340162193)
          ·
            refine ⟨9078799132059768255121645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12105065509413024340162193 9078799132059768255121645)
            ·
              refine ⟨3404549674522413095670617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9078799132059768255121645 3404549674522413095670617)
              ·
                refine ⟨2553412255891809821752963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3404549674522413095670617 2553412255891809821752963)
                ·
                  refine ⟨3830118383837714732629445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2553412255891809821752963 3830118383837714732629445)
                  ·
                    refine ⟨718147196969571512368021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3830118383837714732629445 718147196969571512368021)
                    ·
                      rfl

theorem cell22_2097880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_2097880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097880 prefixEnd_2097880 := by exact prefixLift 2097880
  have htrace : WordTrace (prefixWord ++ tailWord_2097880) baseStart_2097880 baseEnd_2097880 := by
    simpa [prefixWord, tailWord_2097880, baseEnd_2097880] using wordTrace_append hprefix tailTrace_2097880
  have hstable : (prefixWord ++ tailWord_2097880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097880).length < 2 ^ (prefixWord ++ tailWord_2097880).sum := by decide
  have hdescent : baseEnd_2097880 < baseStart_2097880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097893 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_2097893 : Nat := 118140960795 + 2097893 * 2 ^ 59
def prefixEnd_2097893 : Nat := 4983230072969 + 3 ^ 40 * 2097893 * 2
def baseEnd_2097893 : Nat := 718151647135243811792981

theorem tailTrace_2097893 : CollatzResearch.WordTrace tailWord_2097893 prefixEnd_2097893 718151647135243811792981 := by
  unfold tailWord_2097893
  simp only [CollatzResearch.WordTrace]
  refine ⟨76516443788699427444458333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51010962525799618296305555 76516443788699427444458333)
  ·
    refine ⟨28693666420762285291671875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76516443788699427444458333 28693666420762285291671875)
    ·
      refine ⟨43040499631143427937507813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28693666420762285291671875 43040499631143427937507813)
      ·
        refine ⟨8070093680839392738282715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43040499631143427937507813 8070093680839392738282715)
        ·
          refine ⟨12105140521259089107424073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8070093680839392738282715 12105140521259089107424073)
          ·
            refine ⟨9078855390944316830568055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12105140521259089107424073 9078855390944316830568055)
            ·
              refine ⟨13618283086416475245852083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9078855390944316830568055 13618283086416475245852083)
              ·
                refine ⟨20427424629624712868778125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13618283086416475245852083 20427424629624712868778125)
                ·
                  refine ⟨7660284236109267325791797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20427424629624712868778125 7660284236109267325791797)
                  ·
                    refine ⟨718151647135243811792981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7660284236109267325791797 718151647135243811792981)
                    ·
                      rfl

theorem cell22_2097893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_2097893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097893 prefixEnd_2097893 := by exact prefixLift 2097893
  have htrace : WordTrace (prefixWord ++ tailWord_2097893) baseStart_2097893 baseEnd_2097893 := by
    simpa [prefixWord, tailWord_2097893, baseEnd_2097893] using wordTrace_append hprefix tailTrace_2097893
  have hstable : (prefixWord ++ tailWord_2097893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097893).length < 2 ^ (prefixWord ++ tailWord_2097893).sum := by decide
  have hdescent : baseEnd_2097893 < baseStart_2097893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097927 : List Nat := [1, 1, 4, 4, 1, 1, 2, 3, 2, 3]
def baseStart_2097927 : Nat := 118140960795 + 2097927 * 2 ^ 59
def prefixEnd_2097927 : Nat := 4983230072969 + 3 ^ 40 * 2097927 * 2
def baseEnd_2097927 : Nat := 718163286030079056442877

theorem tailTrace_2097927 : CollatzResearch.WordTrace tailWord_2097927 prefixEnd_2097927 718163286030079056442877 := by
  unfold tailWord_2097927
  simp only [CollatzResearch.WordTrace]
  refine ⟨76517683870576251251196035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51011789247050834167464023 76517683870576251251196035)
  ·
    refine ⟨114776525805864376876794053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76517683870576251251196035 114776525805864376876794053)
    ·
      refine ⟨21520598588599570664398885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114776525805864376876794053 21520598588599570664398885)
      ·
        refine ⟨4035112235362419499574791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21520598588599570664398885 4035112235362419499574791)
        ·
          refine ⟨6052668353043629249362187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035112235362419499574791 6052668353043629249362187)
          ·
            refine ⟨9079002529565443874043281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6052668353043629249362187 9079002529565443874043281)
            ·
              refine ⟨6809251897174082905532461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9079002529565443874043281 6809251897174082905532461)
              ·
                refine ⟨2553469461440281089574673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6809251897174082905532461 2553469461440281089574673)
                ·
                  refine ⟨1915102096080210817181005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2553469461440281089574673 1915102096080210817181005)
                  ·
                    refine ⟨718163286030079056442877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1915102096080210817181005 718163286030079056442877)
                    ·
                      rfl

theorem cell22_2097927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_2097927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097927 prefixEnd_2097927 := by exact prefixLift 2097927
  have htrace : WordTrace (prefixWord ++ tailWord_2097927) baseStart_2097927 baseEnd_2097927 := by
    simpa [prefixWord, tailWord_2097927, baseEnd_2097927] using wordTrace_append hprefix tailTrace_2097927
  have hstable : (prefixWord ++ tailWord_2097927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097927).length < 2 ^ (prefixWord ++ tailWord_2097927).sum := by decide
  have hdescent : baseEnd_2097927 < baseStart_2097927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2097998 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_2097998 : Nat := 118140960795 + 2097998 * 2 ^ 59
def prefixEnd_2097998 : Nat := 4983230072969 + 3 ^ 40 * 2097998 * 2
def baseEnd_2097998 : Nat := 718187590781058537917659

theorem tailTrace_2097998 : CollatzResearch.WordTrace tailWord_2097998 prefixEnd_2097998 718187590781058537917659 := by
  unfold tailWord_2097998
  simp only [CollatzResearch.WordTrace]
  refine ⟨9565034181664878797128831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51013515635546020251353765 9565034181664878797128831)
  ·
    refine ⟨14347551272497318195693247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9565034181664878797128831 14347551272497318195693247)
    ·
      refine ⟨21521326908745977293539871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14347551272497318195693247 21521326908745977293539871)
      ·
        refine ⟨32281990363118965940309807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21521326908745977293539871 32281990363118965940309807)
        ·
          refine ⟨48422985544678448910464711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32281990363118965940309807 48422985544678448910464711)
          ·
            refine ⟨72634478317017673365697067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48422985544678448910464711 72634478317017673365697067)
            ·
              refine ⟨108951717475526510048545601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72634478317017673365697067 108951717475526510048545601)
              ·
                refine ⟨81713788106644882536409201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108951717475526510048545601 81713788106644882536409201)
                ·
                  refine ⟨61285341079983661902306901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81713788106644882536409201 61285341079983661902306901)
                  ·
                    refine ⟨718187590781058537917659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61285341079983661902306901 718187590781058537917659)
                    ·
                      rfl

theorem cell22_2097998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_2097998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2097998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2097998 prefixEnd_2097998 := by exact prefixLift 2097998
  have htrace : WordTrace (prefixWord ++ tailWord_2097998) baseStart_2097998 baseEnd_2097998 := by
    simpa [prefixWord, tailWord_2097998, baseEnd_2097998] using wordTrace_append hprefix tailTrace_2097998
  have hstable : (prefixWord ++ tailWord_2097998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2097998).length < 2 ^ (prefixWord ++ tailWord_2097998).sum := by decide
  have hdescent : baseEnd_2097998 < baseStart_2097998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2097998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098015 : List Nat := [1, 1, 2, 3, 1, 3, 1, 5, 1, 4]
def baseStart_2098015 : Nat := 118140960795 + 2098015 * 2 ^ 59
def prefixEnd_2098015 : Nat := 4983230072969 + 3 ^ 40 * 2098015 * 2
def baseEnd_2098015 : Nat := 718193410228476160242607

theorem tailTrace_2098015 : CollatzResearch.WordTrace tailWord_2098015 prefixEnd_2098015 718193410228476160242607 := by
  unfold tailWord_2098015
  simp only [CollatzResearch.WordTrace]
  refine ⟨76520893494257442280399499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51013928996171628186932999 76520893494257442280399499)
  ·
    refine ⟨114781340241386163420599249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76520893494257442280399499 114781340241386163420599249)
    ·
      refine ⟨86086005181039622565449437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114781340241386163420599249 86086005181039622565449437)
      ·
        refine ⟨32282251942889858462043539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86086005181039622565449437 32282251942889858462043539)
        ·
          refine ⟨48423377914334787693065309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32282251942889858462043539 48423377914334787693065309)
          ·
            refine ⟨18158766717875545384899491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48423377914334787693065309 18158766717875545384899491)
            ·
              refine ⟨27238150076813318077349237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18158766717875545384899491 27238150076813318077349237)
              ·
                refine ⟨2553576569701248569751491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27238150076813318077349237 2553576569701248569751491)
                ·
                  refine ⟨3830364854551872854627237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2553576569701248569751491 3830364854551872854627237)
                  ·
                    refine ⟨718193410228476160242607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3830364854551872854627237 718193410228476160242607)
                    ·
                      rfl

theorem cell22_2098015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_2098015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098015 prefixEnd_2098015 := by exact prefixLift 2098015
  have htrace : WordTrace (prefixWord ++ tailWord_2098015) baseStart_2098015 baseEnd_2098015 := by
    simpa [prefixWord, tailWord_2098015, baseEnd_2098015] using wordTrace_append hprefix tailTrace_2098015
  have hstable : (prefixWord ++ tailWord_2098015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098015).length < 2 ^ (prefixWord ++ tailWord_2098015).sum := by decide
  have hdescent : baseEnd_2098015 < baseStart_2098015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098043 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 3, 6]
def baseStart_2098043 : Nat := 118140960795 + 2098043 * 2 ^ 59
def prefixEnd_2098043 : Nat := 4983230072969 + 3 ^ 40 * 2098043 * 2
def baseEnd_2098043 : Nat := 718202995200693420542521

theorem tailTrace_2098043 : CollatzResearch.WordTrace tailWord_2098043 prefixEnd_2098043 718202995200693420542521 := by
  unfold tailWord_2098043
  simp only [CollatzResearch.WordTrace]
  refine ⟨76521914738156003062418783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51014609825437335374945855 76521914738156003062418783)
  ·
    refine ⟨114782872107234004593628175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76521914738156003062418783 114782872107234004593628175)
    ·
      refine ⟨172174308160851006890442263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114782872107234004593628175 172174308160851006890442263)
      ·
        refine ⟨258261462241276510335663395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172174308160851006890442263 258261462241276510335663395)
        ·
          refine ⟨387392193361914765503495093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258261462241276510335663395 387392193361914765503495093)
          ·
            refine ⟨36318018127679509265952665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 387392193361914765503495093 36318018127679509265952665)
            ·
              refine ⟨27238513595759631949464499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36318018127679509265952665 27238513595759631949464499)
              ·
                refine ⟨40857770393639447924196749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27238513595759631949464499 40857770393639447924196749)
                ·
                  refine ⟨15321663897614792971573781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40857770393639447924196749 15321663897614792971573781)
                  ·
                    refine ⟨718202995200693420542521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15321663897614792971573781 718202995200693420542521)
                    ·
                      rfl

theorem cell22_2098043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_2098043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098043 prefixEnd_2098043 := by exact prefixLift 2098043
  have htrace : WordTrace (prefixWord ++ tailWord_2098043) baseStart_2098043 baseEnd_2098043 := by
    simpa [prefixWord, tailWord_2098043, baseEnd_2098043] using wordTrace_append hprefix tailTrace_2098043
  have hstable : (prefixWord ++ tailWord_2098043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098043).length < 2 ^ (prefixWord ++ tailWord_2098043).sum := by decide
  have hdescent : baseEnd_2098043 < baseStart_2098043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098060 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_2098060 : Nat := 118140960795 + 2098060 * 2 ^ 59
def prefixEnd_2098060 : Nat := 4983230072969 + 3 ^ 40 * 2098060 * 2
def baseEnd_2098060 : Nat := 718208814648111042867469

theorem tailTrace_2098060 : CollatzResearch.WordTrace tailWord_2098060 prefixEnd_2098060 718208814648111042867469 := by
  unfold tailWord_2098060
  simp only [CollatzResearch.WordTrace]
  refine ⟨38261267389547207482893817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51015023186062943310525089 38261267389547207482893817)
  ·
    refine ⟨28695950542160405612170363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38261267389547207482893817 28695950542160405612170363)
    ·
      refine ⟨43043925813240608418255545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28695950542160405612170363 43043925813240608418255545)
      ·
        refine ⟨32282944359930456313691659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43043925813240608418255545 32282944359930456313691659)
        ·
          refine ⟨48424416539895684470537489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32282944359930456313691659 48424416539895684470537489)
          ·
            refine ⟨36318312404921763352903117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48424416539895684470537489 36318312404921763352903117)
            ·
              refine ⟨13619367151845661257338669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36318312404921763352903117 13619367151845661257338669)
              ·
                refine ⟨5107262681942122971502001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13619367151845661257338669 5107262681942122971502001)
                ·
                  refine ⟨3830447011456592228626501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5107262681942122971502001 3830447011456592228626501)
                  ·
                    refine ⟨718208814648111042867469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3830447011456592228626501 718208814648111042867469)
                    ·
                      rfl

theorem cell22_2098060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_2098060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098060 prefixEnd_2098060 := by exact prefixLift 2098060
  have htrace : WordTrace (prefixWord ++ tailWord_2098060) baseStart_2098060 baseEnd_2098060 := by
    simpa [prefixWord, tailWord_2098060, baseEnd_2098060] using wordTrace_append hprefix tailTrace_2098060
  have hstable : (prefixWord ++ tailWord_2098060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098060).length < 2 ^ (prefixWord ++ tailWord_2098060).sum := by decide
  have hdescent : baseEnd_2098060 < baseStart_2098060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098066 : List Nat := [3, 2, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2098066 : Nat := 118140960795 + 2098066 * 2 ^ 59
def prefixEnd_2098066 : Nat := 4983230072969 + 3 ^ 40 * 2098066 * 2
def baseEnd_2098066 : Nat := 718210868570729027217451

theorem tailTrace_2098066 : CollatzResearch.WordTrace tailWord_2098066 prefixEnd_2098066 718210868570729027217451 := by
  unfold tailWord_2098066
  simp only [CollatzResearch.WordTrace]
  refine ⟨19130688404268169497626513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51015169078048451993670701 19130688404268169497626513)
  ·
    refine ⟨14348016303201127123219885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19130688404268169497626513 14348016303201127123219885)
    ·
      refine ⟨5380506113700422671207457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14348016303201127123219885 5380506113700422671207457)
      ·
        refine ⟨4035379585275317003405593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5380506113700422671207457 4035379585275317003405593)
        ·
          refine ⟨3026534688956487752554195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4035379585275317003405593 3026534688956487752554195)
          ·
            refine ⟨4539802033434731628831293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026534688956487752554195 4539802033434731628831293)
            ·
              refine ⟨1702425762538024360811735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4539802033434731628831293 1702425762538024360811735)
              ·
                refine ⟨2553638643807036541217603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702425762538024360811735 2553638643807036541217603)
                ·
                  refine ⟨3830457965710554811826405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2553638643807036541217603 3830457965710554811826405)
                  ·
                    refine ⟨718210868570729027217451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3830457965710554811826405 718210868570729027217451)
                    ·
                      rfl

theorem cell22_2098066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2098066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098066 prefixEnd_2098066 := by exact prefixLift 2098066
  have htrace : WordTrace (prefixWord ++ tailWord_2098066) baseStart_2098066 baseEnd_2098066 := by
    simpa [prefixWord, tailWord_2098066, baseEnd_2098066] using wordTrace_append hprefix tailTrace_2098066
  have hstable : (prefixWord ++ tailWord_2098066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098066).length < 2 ^ (prefixWord ++ tailWord_2098066).sum := by decide
  have hdescent : baseEnd_2098066 < baseStart_2098066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098079 : List Nat := [1, 1, 2, 5, 2, 2, 2, 2, 2, 3]
def baseStart_2098079 : Nat := 118140960795 + 2098079 * 2 ^ 59
def prefixEnd_2098079 : Nat := 4983230072969 + 3 ^ 40 * 2098079 * 2
def baseEnd_2098079 : Nat := 718215318736401326642411

theorem tailTrace_2098079 : CollatzResearch.WordTrace tailWord_2098079 prefixEnd_2098079 718215318736401326642411 := by
  unfold tailWord_2098079
  simp only [CollatzResearch.WordTrace]
  refine ⟨76523227766025581210729291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51015485177350387473819527 76523227766025581210729291)
  ·
    refine ⟨114784841649038371816093937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76523227766025581210729291 114784841649038371816093937)
    ·
      refine ⟨86088631236778778862070453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114784841649038371816093937 86088631236778778862070453)
      ·
        refine ⟨8070809178448010518319105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86088631236778778862070453 8070809178448010518319105)
        ·
          refine ⟨6053106883836007888739329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8070809178448010518319105 6053106883836007888739329)
          ·
            refine ⟨4539830162877005916554497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6053106883836007888739329 4539830162877005916554497)
            ·
              refine ⟨3404872622157754437415873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4539830162877005916554497 3404872622157754437415873)
              ·
                refine ⟨2553654466618315828061905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3404872622157754437415873 2553654466618315828061905)
                ·
                  refine ⟨1915240849963736871046429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2553654466618315828061905 1915240849963736871046429)
                  ·
                    refine ⟨718215318736401326642411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1915240849963736871046429 718215318736401326642411)
                    ·
                      rfl

theorem cell22_2098079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 3].length) (baseStart_2098079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098079 prefixEnd_2098079 := by exact prefixLift 2098079
  have htrace : WordTrace (prefixWord ++ tailWord_2098079) baseStart_2098079 baseEnd_2098079 := by
    simpa [prefixWord, tailWord_2098079, baseEnd_2098079] using wordTrace_append hprefix tailTrace_2098079
  have hstable : (prefixWord ++ tailWord_2098079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098079).length < 2 ^ (prefixWord ++ tailWord_2098079).sum := by decide
  have hdescent : baseEnd_2098079 < baseStart_2098079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098081 : List Nat := [1, 2, 3, 4, 1, 3, 2, 2, 4]
def baseStart_2098081 : Nat := 118140960795 + 2098081 * 2 ^ 59
def prefixEnd_2098081 : Nat := 4983230072969 + 3 ^ 40 * 2098081 * 2
def baseEnd_2098081 : Nat := 239405334459091329364135

theorem tailTrace_2098081 : CollatzResearch.WordTrace tailWord_2098081 prefixEnd_2098081 239405334459091329364135 := by
  unfold tailWord_2098081
  simp only [CollatzResearch.WordTrace]
  refine ⟨76523300712018335552302097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51015533808012223701534731 76523300712018335552302097)
  ·
    refine ⟨57392475534013751664226573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76523300712018335552302097 57392475534013751664226573)
    ·
      refine ⟨21522178325255156874084965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57392475534013751664226573 21522178325255156874084965)
      ·
        refine ⟨4035408435985341913890931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21522178325255156874084965 4035408435985341913890931)
        ·
          refine ⟨6053112653978012870836397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035408435985341913890931 6053112653978012870836397)
          ·
            refine ⟨2269917245241754826563649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6053112653978012870836397 2269917245241754826563649)
            ·
              refine ⟨1702437933931316119922737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2269917245241754826563649 1702437933931316119922737)
              ·
                refine ⟨1276828450448487089942053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1702437933931316119922737 1276828450448487089942053)
                ·
                  refine ⟨239405334459091329364135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1276828450448487089942053 239405334459091329364135)
                  ·
                    rfl

theorem cell22_2098081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 4].length) (baseStart_2098081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098081 prefixEnd_2098081 := by exact prefixLift 2098081
  have htrace : WordTrace (prefixWord ++ tailWord_2098081) baseStart_2098081 baseEnd_2098081 := by
    simpa [prefixWord, tailWord_2098081, baseEnd_2098081] using wordTrace_append hprefix tailTrace_2098081
  have hstable : (prefixWord ++ tailWord_2098081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098081).length < 2 ^ (prefixWord ++ tailWord_2098081).sum := by decide
  have hdescent : baseEnd_2098081 < baseStart_2098081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098137 : List Nat := [1, 2, 1, 2, 5, 1, 3, 2, 5]
def baseStart_2098137 : Nat := 118140960795 + 2098137 * 2 ^ 59
def prefixEnd_2098137 : Nat := 4983230072969 + 3 ^ 40 * 2098137 * 2
def baseEnd_2098137 : Nat := 239411724440569502897411

theorem tailTrace_2098137 : CollatzResearch.WordTrace tailWord_2098137 prefixEnd_2098137 239411724440569502897411 := by
  unfold tailWord_2098137
  simp only [CollatzResearch.WordTrace]
  refine ⟨76525343199815457116340665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51016895466543638077560443 76525343199815457116340665)
  ·
    refine ⟨57394007399861592837255499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76525343199815457116340665 57394007399861592837255499)
    ·
      refine ⟨86091011099792389255883249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57394007399861592837255499 86091011099792389255883249)
      ·
        refine ⟨64568258324844291941912437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86091011099792389255883249 64568258324844291941912437)
        ·
          refine ⟨6053274217954152369554291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64568258324844291941912437 6053274217954152369554291)
          ·
            refine ⟨9079911326931228554331437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053274217954152369554291 9079911326931228554331437)
            ·
              refine ⟨3404966747599210707874289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9079911326931228554331437 3404966747599210707874289)
              ·
                refine ⟨2553725060699408030905717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3404966747599210707874289 2553725060699408030905717)
                ·
                  refine ⟨239411724440569502897411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2553725060699408030905717 239411724440569502897411)
                  ·
                    rfl

theorem cell22_2098137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_2098137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098137 prefixEnd_2098137 := by exact prefixLift 2098137
  have htrace : WordTrace (prefixWord ++ tailWord_2098137) baseStart_2098137 baseEnd_2098137 := by
    simpa [prefixWord, tailWord_2098137, baseEnd_2098137] using wordTrace_append hprefix tailTrace_2098137
  have hstable : (prefixWord ++ tailWord_2098137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098137).length < 2 ^ (prefixWord ++ tailWord_2098137).sum := by decide
  have hdescent : baseEnd_2098137 < baseStart_2098137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098141 : List Nat := [1, 4, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_2098141 : Nat := 118140960795 + 2098141 * 2 ^ 59
def prefixEnd_2098141 : Nat := 4983230072969 + 3 ^ 40 * 2098141 * 2
def baseEnd_2098141 : Nat := 718236542603453831592221

theorem tailTrace_2098141 : CollatzResearch.WordTrace tailWord_2098141 prefixEnd_2098141 718236542603453831592221 := by
  unfold tailWord_2098141
  simp only [CollatzResearch.WordTrace]
  refine ⟨76525489091800965799486277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51016992727867310532990851 76525489091800965799486277)
  ·
    refine ⟨14348529204712681087403677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76525489091800965799486277 14348529204712681087403677)
    ·
      refine ⟨5380698451767255407776379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14348529204712681087403677 5380698451767255407776379)
      ·
        refine ⟨8071047677650883111664569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5380698451767255407776379 8071047677650883111664569)
        ·
          refine ⟨6053285758238162333748427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8071047677650883111664569 6053285758238162333748427)
          ·
            refine ⟨9079928637357243500622641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053285758238162333748427 9079928637357243500622641)
            ·
              refine ⟨6809946478017932625466981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9079928637357243500622641 6809946478017932625466981)
              ·
                refine ⟨1276864964628362367275059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6809946478017932625466981 1276864964628362367275059)
                ·
                  refine ⟨1915297446942543550912589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276864964628362367275059 1915297446942543550912589)
                  ·
                    refine ⟨718236542603453831592221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1915297446942543550912589 718236542603453831592221)
                    ·
                      rfl

theorem cell22_2098141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_2098141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098141 prefixEnd_2098141 := by exact prefixLift 2098141
  have htrace : WordTrace (prefixWord ++ tailWord_2098141) baseStart_2098141 baseEnd_2098141 := by
    simpa [prefixWord, tailWord_2098141, baseEnd_2098141] using wordTrace_append hprefix tailTrace_2098141
  have hstable : (prefixWord ++ tailWord_2098141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098141).length < 2 ^ (prefixWord ++ tailWord_2098141).sum := by decide
  have hdescent : baseEnd_2098141 < baseStart_2098141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098154 : List Nat := [3, 1, 3, 1, 2, 3, 3, 1, 5]
def baseStart_2098154 : Nat := 118140960795 + 2098154 * 2 ^ 59
def prefixEnd_2098154 : Nat := 4983230072969 + 3 ^ 40 * 2098154 * 2
def baseEnd_2098154 : Nat := 239413664256375377005727

theorem tailTrace_2098154 : CollatzResearch.WordTrace tailWord_2098154 prefixEnd_2098154 239413664256375377005727 := by
  unfold tailWord_2098154
  simp only [CollatzResearch.WordTrace]
  refine ⟨19131490810188467254927379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51017308827169246013139677 19131490810188467254927379)
  ·
    refine ⟨28697236215282700882391069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19131490810188467254927379 28697236215282700882391069)
    ·
      refine ⟨10761463580731012830896651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28697236215282700882391069 10761463580731012830896651)
      ·
        refine ⟨16142195371096519246344977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10761463580731012830896651 16142195371096519246344977)
        ·
          refine ⟨12106646528322389434758733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16142195371096519246344977 12106646528322389434758733)
          ·
            refine ⟨4539992448120896038034525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12106646528322389434758733 4539992448120896038034525)
            ·
              refine ⟨1702497168045336014262947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4539992448120896038034525 1702497168045336014262947)
              ·
                refine ⟨2553745752068004021394421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702497168045336014262947 2553745752068004021394421)
                ·
                  refine ⟨239413664256375377005727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2553745752068004021394421 239413664256375377005727)
                  ·
                    rfl

theorem cell22_2098154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_2098154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098154 prefixEnd_2098154 := by exact prefixLift 2098154
  have htrace : WordTrace (prefixWord ++ tailWord_2098154) baseStart_2098154 baseEnd_2098154 := by
    simpa [prefixWord, tailWord_2098154, baseEnd_2098154] using wordTrace_append hprefix tailTrace_2098154
  have hstable : (prefixWord ++ tailWord_2098154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098154).length < 2 ^ (prefixWord ++ tailWord_2098154).sum := by decide
  have hdescent : baseEnd_2098154 < baseStart_2098154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098199 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 6]
def baseStart_2098199 : Nat := 118140960795 + 2098199 * 2 ^ 59
def prefixEnd_2098199 : Nat := 4983230072969 + 3 ^ 40 * 2098199 * 2
def baseEnd_2098199 : Nat := 239418799062920337880681

theorem tailTrace_2098199 : CollatzResearch.WordTrace tailWord_2098199 prefixEnd_2098199 239418799062920337880681 := by
  unfold tailWord_2098199
  simp only [CollatzResearch.WordTrace]
  refine ⟨76527604525590841705097651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51018403017060561136731767 76527604525590841705097651)
  ·
    refine ⟨114791406788386262557646477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76527604525590841705097651 114791406788386262557646477)
    ·
      refine ⟨43046777545644848459117429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114791406788386262557646477 43046777545644848459117429)
      ·
        refine ⟨4035635394904204543042259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43046777545644848459117429 4035635394904204543042259)
        ·
          refine ⟨6053453092356306814563389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035635394904204543042259 6053453092356306814563389)
          ·
            refine ⟨2270044909633615055461271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6053453092356306814563389 2270044909633615055461271)
            ·
              refine ⟨3405067364450422583191907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270044909633615055461271 3405067364450422583191907)
              ·
                refine ⟨5107601046675633874787861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3405067364450422583191907 5107601046675633874787861)
                ·
                  refine ⟨239418799062920337880681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5107601046675633874787861 239418799062920337880681)
                  ·
                    rfl

theorem cell22_2098199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 6].length) (baseStart_2098199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098199 prefixEnd_2098199 := by exact prefixLift 2098199
  have htrace : WordTrace (prefixWord ++ tailWord_2098199) baseStart_2098199 baseEnd_2098199 := by
    simpa [prefixWord, tailWord_2098199, baseEnd_2098199] using wordTrace_append hprefix tailTrace_2098199
  have hstable : (prefixWord ++ tailWord_2098199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098199).length < 2 ^ (prefixWord ++ tailWord_2098199).sum := by decide
  have hdescent : baseEnd_2098199 < baseStart_2098199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098218 : List Nat := [3, 1, 4, 1, 4, 1, 1, 2, 1, 4]
def baseStart_2098218 : Nat := 118140960795 + 2098218 * 2 ^ 59
def prefixEnd_2098218 : Nat := 4983230072969 + 3 ^ 40 * 2098218 * 2
def baseEnd_2098218 : Nat := 718262901277051297416985

theorem tailTrace_2098218 : CollatzResearch.WordTrace tailWord_2098218 prefixEnd_2098218 718262901277051297416985 := by
  unfold tailWord_2098218
  simp only [CollatzResearch.WordTrace]
  refine ⟨19132074378130501987509827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51018865008348005300026205 19132074378130501987509827)
  ·
    refine ⟨28698111567195752981264741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19132074378130501987509827 28698111567195752981264741)
    ·
      refine ⟨5380895918849203683987139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28698111567195752981264741 5380895918849203683987139)
      ·
        refine ⟨8071343878273805525980709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5380895918849203683987139 8071343878273805525980709)
        ·
          refine ⟨1513376977176338536121383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8071343878273805525980709 1513376977176338536121383)
          ·
            refine ⟨2270065465764507804182075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513376977176338536121383 2270065465764507804182075)
            ·
              refine ⟨3405098198646761706273113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270065465764507804182075 3405098198646761706273113)
              ·
                refine ⟨2553823648985071279704835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3405098198646761706273113 2553823648985071279704835)
                ·
                  refine ⟨3830735473477606919557253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2553823648985071279704835 3830735473477606919557253)
                  ·
                    refine ⟨718262901277051297416985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3830735473477606919557253 718262901277051297416985)
                    ·
                      rfl

theorem cell22_2098218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_2098218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098218 prefixEnd_2098218 := by exact prefixLift 2098218
  have htrace : WordTrace (prefixWord ++ tailWord_2098218) baseStart_2098218 baseEnd_2098218 := by
    simpa [prefixWord, tailWord_2098218, baseEnd_2098218] using wordTrace_append hprefix tailTrace_2098218
  have hstable : (prefixWord ++ tailWord_2098218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098218).length < 2 ^ (prefixWord ++ tailWord_2098218).sum := by decide
  have hdescent : baseEnd_2098218 < baseStart_2098218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098246 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2098246 : Nat := 118140960795 + 2098246 * 2 ^ 59
def prefixEnd_2098246 : Nat := 4983230072969 + 3 ^ 40 * 2098246 * 2
def baseEnd_2098246 : Nat := 718272486249268557716899

theorem tailTrace_2098246 : CollatzResearch.WordTrace tailWord_2098246 prefixEnd_2098246 718272486249268557716899 := by
  unfold tailWord_2098246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2391541211138142772876831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51019545837613712488039061 2391541211138142772876831)
  ·
    refine ⟨3587311816707214159315247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2391541211138142772876831 3587311816707214159315247)
    ·
      refine ⟨5380967725060821238972871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3587311816707214159315247 5380967725060821238972871)
      ·
        refine ⟨8071451587591231858459307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5380967725060821238972871 8071451587591231858459307)
        ·
          refine ⟨12107177381386847787688961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8071451587591231858459307 12107177381386847787688961)
          ·
            refine ⟨9080383036040135840766721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12107177381386847787688961 9080383036040135840766721)
            ·
              refine ⟨6810287277030101880575041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9080383036040135840766721 6810287277030101880575041)
              ·
                refine ⟨5107715457772576410431281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6810287277030101880575041 5107715457772576410431281)
                ·
                  refine ⟨3830786593329432307823461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5107715457772576410431281 3830786593329432307823461)
                  ·
                    refine ⟨718272486249268557716899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3830786593329432307823461 718272486249268557716899)
                    ·
                      rfl

theorem cell22_2098246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2098246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098246 prefixEnd_2098246 := by exact prefixLift 2098246
  have htrace : WordTrace (prefixWord ++ tailWord_2098246) baseStart_2098246 baseEnd_2098246 := by
    simpa [prefixWord, tailWord_2098246, baseEnd_2098246] using wordTrace_append hprefix tailTrace_2098246
  have hstable : (prefixWord ++ tailWord_2098246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098246).length < 2 ^ (prefixWord ++ tailWord_2098246).sum := by decide
  have hdescent : baseEnd_2098246 < baseStart_2098246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098272 : List Nat := [2, 1, 1, 3, 2, 2, 1, 5, 5]
def baseStart_2098272 : Nat := 118140960795 + 2098272 * 2 ^ 59
def prefixEnd_2098272 : Nat := 4983230072969 + 3 ^ 40 * 2098272 * 2
def baseEnd_2098272 : Nat := 239427128860204385522273

theorem tailTrace_2098272 : CollatzResearch.WordTrace tailWord_2098272 prefixEnd_2098272 239427128860204385522273 := by
  unfold tailWord_2098272
  simp only [CollatzResearch.WordTrace]
  refine ⟨38265133527163187586252535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51020178036217583448336713 38265133527163187586252535)
  ·
    refine ⟨57397700290744781379378803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38265133527163187586252535 57397700290744781379378803)
    ·
      refine ⟨86096550436117172069068205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57397700290744781379378803 86096550436117172069068205)
      ·
        refine ⟨32286206413543939525900577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86096550436117172069068205 32286206413543939525900577)
        ·
          refine ⟨24214654810157954644425433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32286206413543939525900577 24214654810157954644425433)
          ·
            refine ⟨18160991107618465983319075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24214654810157954644425433 18160991107618465983319075)
            ·
              refine ⟨27241486661427698974978613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18160991107618465983319075 27241486661427698974978613)
              ·
                refine ⟨2553889374508846778904245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27241486661427698974978613 2553889374508846778904245)
                ·
                  refine ⟨239427128860204385522273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2553889374508846778904245 239427128860204385522273)
                  ·
                    rfl

theorem cell22_2098272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_2098272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098272 prefixEnd_2098272 := by exact prefixLift 2098272
  have htrace : WordTrace (prefixWord ++ tailWord_2098272) baseStart_2098272 baseEnd_2098272 := by
    simpa [prefixWord, tailWord_2098272, baseEnd_2098272] using wordTrace_append hprefix tailTrace_2098272
  have hstable : (prefixWord ++ tailWord_2098272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098272).length < 2 ^ (prefixWord ++ tailWord_2098272).sum := by decide
  have hdescent : baseEnd_2098272 < baseStart_2098272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098364 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_2098364 : Nat := 118140960795 + 2098364 * 2 ^ 59
def prefixEnd_2098364 : Nat := 4983230072969 + 3 ^ 40 * 2098364 * 2
def baseEnd_2098364 : Nat := 718312880060755583266537

theorem tailTrace_2098364 : CollatzResearch.WordTrace tailWord_2098364 prefixEnd_2098364 718312880060755583266537 := by
  unfold tailWord_2098364
  simp only [CollatzResearch.WordTrace]
  refine ⟨38266811284996537442427073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51022415046662049923236097 38266811284996537442427073)
  ·
    refine ⟨28700108463747403081820305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38266811284996537442427073 28700108463747403081820305)
    ·
      refine ⟨21525081347810552311365229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28700108463747403081820305 21525081347810552311365229)
      ·
        refine ⟨8071905505428957116761961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21525081347810552311365229 8071905505428957116761961)
        ·
          refine ⟨6053929129071717837571471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8071905505428957116761961 6053929129071717837571471)
          ·
            refine ⟨9080893693607576756357207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053929129071717837571471 9080893693607576756357207)
            ·
              refine ⟨13621340540411365134535811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9080893693607576756357207 13621340540411365134535811)
              ·
                refine ⟨20432010810617047701803717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13621340540411365134535811 20432010810617047701803717)
                ·
                  refine ⟨3831002026990696444088197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20432010810617047701803717 3831002026990696444088197)
                  ·
                    refine ⟨718312880060755583266537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3831002026990696444088197 718312880060755583266537)
                    ·
                      rfl

theorem cell22_2098364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_2098364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098364 prefixEnd_2098364 := by exact prefixLift 2098364
  have htrace : WordTrace (prefixWord ++ tailWord_2098364) baseStart_2098364 baseEnd_2098364 := by
    simpa [prefixWord, tailWord_2098364, baseEnd_2098364] using wordTrace_append hprefix tailTrace_2098364
  have hstable : (prefixWord ++ tailWord_2098364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098364).length < 2 ^ (prefixWord ++ tailWord_2098364).sum := by decide
  have hdescent : baseEnd_2098364 < baseStart_2098364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098366 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_2098366 : Nat := 118140960795 + 2098366 * 2 ^ 59
def prefixEnd_2098366 : Nat := 4983230072969 + 3 ^ 40 * 2098366 * 2
def baseEnd_2098366 : Nat := 718313564701628244716531

theorem tailTrace_2098366 : CollatzResearch.WordTrace tailWord_2098366 prefixEnd_2098366 718313564701628244716531 := by
  unfold tailWord_2098366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9566711939498228653303369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51022463677323886150951301 9566711939498228653303369)
  ·
    refine ⟨7175033954623671489977527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9566711939498228653303369 7175033954623671489977527)
    ·
      refine ⟨10762550931935507234966291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7175033954623671489977527 10762550931935507234966291)
      ·
        refine ⟨16143826397903260852449437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10762550931935507234966291 16143826397903260852449437)
        ·
          refine ⟨6053934899213722819668539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16143826397903260852449437 6053934899213722819668539)
          ·
            refine ⟨9080902348820584229502809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053934899213722819668539 9080902348820584229502809)
            ·
              refine ⟨6810676761615438172127107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9080902348820584229502809 6810676761615438172127107)
              ·
                refine ⟨10216015142423157258190661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6810676761615438172127107 10216015142423157258190661)
                ·
                  refine ⟨1915502839204341985910749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10216015142423157258190661 1915502839204341985910749)
                  ·
                    refine ⟨718313564701628244716531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1915502839204341985910749 718313564701628244716531)
                    ·
                      rfl

theorem cell22_2098366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_2098366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098366 prefixEnd_2098366 := by exact prefixLift 2098366
  have htrace : WordTrace (prefixWord ++ tailWord_2098366) baseStart_2098366 baseEnd_2098366 := by
    simpa [prefixWord, tailWord_2098366, baseEnd_2098366] using wordTrace_append hprefix tailTrace_2098366
  have hstable : (prefixWord ++ tailWord_2098366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098366).length < 2 ^ (prefixWord ++ tailWord_2098366).sum := by decide
  have hdescent : baseEnd_2098366 < baseStart_2098366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098368 : List Nat := [2, 1, 1, 2, 6, 1, 3, 2, 4]
def baseStart_2098368 : Nat := 118140960795 + 2098368 * 2 ^ 59
def prefixEnd_2098368 : Nat := 4983230072969 + 3 ^ 40 * 2098368 * 2
def baseEnd_2098368 : Nat := 239438083114166968722175

theorem tailTrace_2098368 : CollatzResearch.WordTrace tailWord_2098368 prefixEnd_2098368 239438083114166968722175 := by
  unfold tailWord_2098368
  simp only [CollatzResearch.WordTrace]
  refine ⟨38266884230989291783999879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51022512307985722378666505 38266884230989291783999879)
  ·
    refine ⟨57400326346483937675999819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38266884230989291783999879 57400326346483937675999819)
    ·
      refine ⟨86100489519725906513999729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57400326346483937675999819 86100489519725906513999729)
      ·
        refine ⟨64575367139794429885499797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86100489519725906513999729 64575367139794429885499797)
        ·
          refine ⟨3026970334677863900882803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64575367139794429885499797 3026970334677863900882803)
          ·
            refine ⟨4540455502016795851324205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026970334677863900882803 4540455502016795851324205)
            ·
              refine ⟨1702670813256298444246577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4540455502016795851324205 1702670813256298444246577)
              ·
                refine ⟨1277003109942223833184933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1702670813256298444246577 1277003109942223833184933)
                ·
                  refine ⟨239438083114166968722175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1277003109942223833184933 239438083114166968722175)
                  ·
                    rfl

theorem cell22_2098368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 4].length) (baseStart_2098368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098368 prefixEnd_2098368 := by exact prefixLift 2098368
  have htrace : WordTrace (prefixWord ++ tailWord_2098368) baseStart_2098368 baseEnd_2098368 := by
    simpa [prefixWord, tailWord_2098368, baseEnd_2098368] using wordTrace_append hprefix tailTrace_2098368
  have hstable : (prefixWord ++ tailWord_2098368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098368).length < 2 ^ (prefixWord ++ tailWord_2098368).sum := by decide
  have hdescent : baseEnd_2098368 < baseStart_2098368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098374 : List Nat := [6, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2098374 : Nat := 118140960795 + 2098374 * 2 ^ 59
def prefixEnd_2098374 : Nat := 4983230072969 + 3 ^ 40 * 2098374 * 2
def baseEnd_2098374 : Nat := 239438767755039630172169

theorem tailTrace_2098374 : CollatzResearch.WordTrace tailWord_2098374 prefixEnd_2098374 239438767755039630172169 := by
  unfold tailWord_2098374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2391687103123651456022443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51022658199971231061812117 2391687103123651456022443)
  ·
    refine ⟨3587530654685477184033665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2391687103123651456022443 3587530654685477184033665)
    ·
      refine ⟨2690647991014107888025249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3587530654685477184033665 2690647991014107888025249)
      ·
        refine ⟨2017985993260580916018937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2690647991014107888025249 2017985993260580916018937)
        ·
          refine ⟨1513489494945435687014203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2017985993260580916018937 1513489494945435687014203)
          ·
            refine ⟨2270234242418153530521305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513489494945435687014203 2270234242418153530521305)
            ·
              refine ⟨1702675681813615147890979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2270234242418153530521305 1702675681813615147890979)
              ·
                refine ⟨2554013522720422721836469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702675681813615147890979 2554013522720422721836469)
                ·
                  refine ⟨239438767755039630172169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2554013522720422721836469 239438767755039630172169)
                  ·
                    rfl

theorem cell22_2098374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2098374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098374 prefixEnd_2098374 := by exact prefixLift 2098374
  have htrace : WordTrace (prefixWord ++ tailWord_2098374) baseStart_2098374 baseEnd_2098374 := by
    simpa [prefixWord, tailWord_2098374, baseEnd_2098374] using wordTrace_append hprefix tailTrace_2098374
  have hstable : (prefixWord ++ tailWord_2098374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098374).length < 2 ^ (prefixWord ++ tailWord_2098374).sum := by decide
  have hdescent : baseEnd_2098374 < baseStart_2098374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098394 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 5, 3]
def baseStart_2098394 : Nat := 118140960795 + 2098394 * 2 ^ 59
def prefixEnd_2098394 : Nat := 4983230072969 + 3 ^ 40 * 2098394 * 2
def baseEnd_2098394 : Nat := 718323149673845505016445

theorem tailTrace_2098394 : CollatzResearch.WordTrace tailWord_2098394 prefixEnd_2098394 718323149673845505016445 := by
  unfold tailWord_2098394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19133679189971097502111559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51023144506589593338964157 19133679189971097502111559)
  ·
    refine ⟨28700518784956646253167339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19133679189971097502111559 28700518784956646253167339)
    ·
      refine ⟨43050778177434969379751009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28700518784956646253167339 43050778177434969379751009)
      ·
        refine ⟨32288083633076227034813257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43050778177434969379751009 32288083633076227034813257)
        ·
          refine ⟨24216062724807170276109943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32288083633076227034813257 24216062724807170276109943)
          ·
            refine ⟨36324094087210755414164915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24216062724807170276109943 36324094087210755414164915)
            ·
              refine ⟨54486141130816133121247373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36324094087210755414164915 54486141130816133121247373)
              ·
                refine ⟨20432302924056049920467765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54486141130816133121247373 20432302924056049920467765)
                ·
                  refine ⟨1915528399130254680043853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20432302924056049920467765 1915528399130254680043853)
                  ·
                    refine ⟨718323149673845505016445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1915528399130254680043853 718323149673845505016445)
                    ·
                      rfl

theorem cell22_2098394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_2098394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098394 prefixEnd_2098394 := by exact prefixLift 2098394
  have htrace : WordTrace (prefixWord ++ tailWord_2098394) baseStart_2098394 baseEnd_2098394 := by
    simpa [prefixWord, tailWord_2098394, baseEnd_2098394] using wordTrace_append hprefix tailTrace_2098394
  have hstable : (prefixWord ++ tailWord_2098394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098394).length < 2 ^ (prefixWord ++ tailWord_2098394).sum := by decide
  have hdescent : baseEnd_2098394 < baseStart_2098394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098501 : List Nat := [1, 3, 1, 1, 1, 2, 1, 7, 2, 3]
def baseStart_2098501 : Nat := 118140960795 + 2098501 * 2 ^ 59
def prefixEnd_2098501 : Nat := 4983230072969 + 3 ^ 40 * 2098501 * 2
def baseEnd_2098501 : Nat := 718359777960532892591117

theorem tailTrace_2098501 : CollatzResearch.WordTrace tailWord_2098501 prefixEnd_2098501 718359777960532892591117 := by
  unfold tailWord_2098501
  simp only [CollatzResearch.WordTrace]
  refine ⟨76538619370496747282591357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51025746246997831521727571 76538619370496747282591357)
  ·
    refine ⟨28701982263936280230971759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76538619370496747282591357 28701982263936280230971759)
    ·
      refine ⟨43052973395904420346457639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28701982263936280230971759 43052973395904420346457639)
      ·
        refine ⟨64579460093856630519686459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43052973395904420346457639 64579460093856630519686459)
        ·
          refine ⟨96869190140784945779529689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64579460093856630519686459 96869190140784945779529689)
          ·
            refine ⟨72651892605588709334647267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96869190140784945779529689 72651892605588709334647267)
            ·
              refine ⟨108977838908383064001970901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72651892605588709334647267 108977838908383064001970901)
              ·
                refine ⟨2554168099415228062546193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108977838908383064001970901 2554168099415228062546193)
                ·
                  refine ⟨1915626074561421046909645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2554168099415228062546193 1915626074561421046909645)
                  ·
                    refine ⟨718359777960532892591117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1915626074561421046909645 718359777960532892591117)
                    ·
                      rfl

theorem cell22_2098501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_2098501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098501 prefixEnd_2098501 := by exact prefixLift 2098501
  have htrace : WordTrace (prefixWord ++ tailWord_2098501) baseStart_2098501 baseEnd_2098501 := by
    simpa [prefixWord, tailWord_2098501, baseEnd_2098501] using wordTrace_append hprefix tailTrace_2098501
  have hstable : (prefixWord ++ tailWord_2098501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098501).length < 2 ^ (prefixWord ++ tailWord_2098501).sum := by decide
  have hdescent : baseEnd_2098501 < baseStart_2098501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098516 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2098516 : Nat := 118140960795 + 2098516 * 2 ^ 59
def prefixEnd_2098516 : Nat := 4983230072969 + 3 ^ 40 * 2098516 * 2
def baseEnd_2098516 : Nat := 718364912767077853466071

theorem tailTrace_2098516 : CollatzResearch.WordTrace tailWord_2098516 prefixEnd_2098516 718364912767077853466071 := by
  unfold tailWord_2098516
  simp only [CollatzResearch.WordTrace]
  refine ⟨38269583232721202422193701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51026110976961603229591601 38269583232721202422193701)
  ·
    refine ⟨7175546856135225454161319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38269583232721202422193701 7175546856135225454161319)
    ·
      refine ⟨10763320284202838181241979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7175546856135225454161319 10763320284202838181241979)
      ·
        refine ⟨16144980426304257271862969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10763320284202838181241979 16144980426304257271862969)
        ·
          refine ⟨12108735319728192953897227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16144980426304257271862969 12108735319728192953897227)
          ·
            refine ⟨18163102979592289430845841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12108735319728192953897227 18163102979592289430845841)
            ·
              refine ⟨13622327234694217073134381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18163102979592289430845841 13622327234694217073134381)
              ·
                refine ⟨5108372713010331402425393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13622327234694217073134381 5108372713010331402425393)
                ·
                  refine ⟨3831279534757748551819045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5108372713010331402425393 3831279534757748551819045)
                  ·
                    refine ⟨718364912767077853466071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3831279534757748551819045 718364912767077853466071)
                    ·
                      rfl

theorem cell22_2098516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2098516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098516 prefixEnd_2098516 := by exact prefixLift 2098516
  have htrace : WordTrace (prefixWord ++ tailWord_2098516) baseStart_2098516 baseEnd_2098516 := by
    simpa [prefixWord, tailWord_2098516, baseEnd_2098516] using wordTrace_append hprefix tailTrace_2098516
  have hstable : (prefixWord ++ tailWord_2098516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098516).length < 2 ^ (prefixWord ++ tailWord_2098516).sum := by decide
  have hdescent : baseEnd_2098516 < baseStart_2098516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098544 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 2, 6]
def baseStart_2098544 : Nat := 118140960795 + 2098544 * 2 ^ 59
def prefixEnd_2098544 : Nat := 4983230072969 + 3 ^ 40 * 2098544 * 2
def baseEnd_2098544 : Nat := 718374497739295113765985

theorem tailTrace_2098544 : CollatzResearch.WordTrace tailWord_2098544 prefixEnd_2098544 718374497739295113765985 := by
  unfold tailWord_2098544
  simp only [CollatzResearch.WordTrace]
  refine ⟨38270093854670482813203343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51026791806227310417604457 38270093854670482813203343)
  ·
    refine ⟨57405140782005724219805015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38270093854670482813203343 57405140782005724219805015)
    ·
      refine ⟨86107711173008586329707523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57405140782005724219805015 86107711173008586329707523)
      ·
        refine ⟨129161566759512879494561285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86107711173008586329707523 129161566759512879494561285)
        ·
          refine ⟨24217793767408664905230241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129161566759512879494561285 24217793767408664905230241)
          ·
            refine ⟨18163345325556498678922681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24217793767408664905230241 18163345325556498678922681)
            ·
              refine ⟨13622508994167374009192011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18163345325556498678922681 13622508994167374009192011)
              ·
                refine ⟨20433763491251061013788017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13622508994167374009192011 20433763491251061013788017)
                ·
                  refine ⟨15325322618438295760341013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20433763491251061013788017 15325322618438295760341013)
                  ·
                    refine ⟨718374497739295113765985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15325322618438295760341013 718374497739295113765985)
                    ·
                      rfl

theorem cell22_2098544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_2098544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098544 prefixEnd_2098544 := by exact prefixLift 2098544
  have htrace : WordTrace (prefixWord ++ tailWord_2098544) baseStart_2098544 baseEnd_2098544 := by
    simpa [prefixWord, tailWord_2098544, baseEnd_2098544] using wordTrace_append hprefix tailTrace_2098544
  have hstable : (prefixWord ++ tailWord_2098544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098544).length < 2 ^ (prefixWord ++ tailWord_2098544).sum := by decide
  have hdescent : baseEnd_2098544 < baseStart_2098544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098621 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 6]
def baseStart_2098621 : Nat := 118140960795 + 2098621 * 2 ^ 59
def prefixEnd_2098621 : Nat := 4983230072969 + 3 ^ 40 * 2098621 * 2
def baseEnd_2098621 : Nat := 239466952137630859863583

theorem tailTrace_2098621 : CollatzResearch.WordTrace tailWord_2098621 prefixEnd_2098621 239466952137630859863583 := by
  unfold tailWord_2098621
  simp only [CollatzResearch.WordTrace]
  refine ⟨76542996130062007776959717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51028664086708005184639811 76542996130062007776959717)
  ·
    refine ⟨14351811774386626458179947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76542996130062007776959717 14351811774386626458179947)
    ·
      refine ⟨21527717661579939687269921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14351811774386626458179947 21527717661579939687269921)
      ·
        refine ⟨16145788246184954765452441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21527717661579939687269921 16145788246184954765452441)
        ·
          refine ⟨12109341184638716074089331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16145788246184954765452441 12109341184638716074089331)
          ·
            refine ⟨18164011776958074111133997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12109341184638716074089331 18164011776958074111133997)
            ·
              refine ⟨6811504416359277791675249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18164011776958074111133997 6811504416359277791675249)
              ·
                refine ⟨5108628312269458343756437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6811504416359277791675249 5108628312269458343756437)
                ·
                  refine ⟨239466952137630859863583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5108628312269458343756437 239466952137630859863583)
                  ·
                    rfl

theorem cell22_2098621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_2098621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098621 prefixEnd_2098621 := by exact prefixLift 2098621
  have htrace : WordTrace (prefixWord ++ tailWord_2098621) baseStart_2098621 baseEnd_2098621 := by
    simpa [prefixWord, tailWord_2098621, baseEnd_2098621] using wordTrace_append hprefix tailTrace_2098621
  have hstable : (prefixWord ++ tailWord_2098621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098621).length < 2 ^ (prefixWord ++ tailWord_2098621).sum := by decide
  have hdescent : baseEnd_2098621 < baseStart_2098621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098638 : List Nat := [4, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_2098638 : Nat := 118140960795 + 2098638 * 2 ^ 59
def prefixEnd_2098638 : Nat := 4983230072969 + 3 ^ 40 * 2098638 * 2
def baseEnd_2098638 : Nat := 239468891953436733971899

theorem tailTrace_2098638 : CollatzResearch.WordTrace tailWord_2098638 prefixEnd_2098638 239468891953436733971899 := by
  unfold tailWord_2098638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9567952021375052460041071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51029077447333613120219045 9567952021375052460041071)
  ·
    refine ⟨14351928032062578690061607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9567952021375052460041071 14351928032062578690061607)
    ·
      refine ⟨21527892048093868035092411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14351928032062578690061607 21527892048093868035092411)
      ·
        refine ⟨32291838072140802052638617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21527892048093868035092411 32291838072140802052638617)
        ·
          refine ⟨24218878554105601539478963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32291838072140802052638617 24218878554105601539478963)
          ·
            refine ⟨36328317831158402309218445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24218878554105601539478963 36328317831158402309218445)
            ·
              refine ⟨13623119186684400865956917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36328317831158402309218445 13623119186684400865956917)
              ·
                refine ⟨1277167423751662581183461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13623119186684400865956917 1277167423751662581183461)
                ·
                  refine ⟨239468891953436733971899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1277167423751662581183461 239468891953436733971899)
                  ·
                    rfl

theorem cell22_2098638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_2098638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098638 prefixEnd_2098638 := by exact prefixLift 2098638
  have htrace : WordTrace (prefixWord ++ tailWord_2098638) baseStart_2098638 baseEnd_2098638 := by
    simpa [prefixWord, tailWord_2098638, baseEnd_2098638] using wordTrace_append hprefix tailTrace_2098638
  have hstable : (prefixWord ++ tailWord_2098638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098638).length < 2 ^ (prefixWord ++ tailWord_2098638).sum := by decide
  have hdescent : baseEnd_2098638 < baseStart_2098638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098788 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_2098788 : Nat := 118140960795 + 2098788 * 2 ^ 59
def prefixEnd_2098788 : Nat := 4983230072969 + 3 ^ 40 * 2098788 * 2
def baseEnd_2098788 : Nat := 718458023925759810665237

theorem tailTrace_2098788 : CollatzResearch.WordTrace tailWord_2098788 prefixEnd_2098788 718458023925759810665237 := by
  unfold tailWord_2098788
  simp only [CollatzResearch.WordTrace]
  refine ⟨38274543560228497649144509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51032724746971330198859345 38274543560228497649144509)
  ·
    refine ⟨14352953835085686618429191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38274543560228497649144509 14352953835085686618429191)
    ·
      refine ⟨21529430752628529927643787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14352953835085686618429191 21529430752628529927643787)
      ·
        refine ⟨32294146128942794891465681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21529430752628529927643787 32294146128942794891465681)
        ·
          refine ⟨24220609596707096168599261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32294146128942794891465681 24220609596707096168599261)
          ·
            refine ⟨9082728598765161063224723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24220609596707096168599261 9082728598765161063224723)
            ·
              refine ⟨13624092898147741594837085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9082728598765161063224723 13624092898147741594837085)
              ·
                refine ⟨5109034836805403098063907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13624092898147741594837085 5109034836805403098063907)
                ·
                  refine ⟨7663552255208104647095861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5109034836805403098063907 7663552255208104647095861)
                  ·
                    refine ⟨718458023925759810665237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7663552255208104647095861 718458023925759810665237)
                    ·
                      rfl

theorem cell22_2098788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_2098788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098788 prefixEnd_2098788 := by exact prefixLift 2098788
  have htrace : WordTrace (prefixWord ++ tailWord_2098788) baseStart_2098788 baseEnd_2098788 := by
    simpa [prefixWord, tailWord_2098788, baseEnd_2098788] using wordTrace_append hprefix tailTrace_2098788
  have hstable : (prefixWord ++ tailWord_2098788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098788).length < 2 ^ (prefixWord ++ tailWord_2098788).sum := by decide
  have hdescent : baseEnd_2098788 < baseStart_2098788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098801 : List Nat := [1, 2, 2, 2, 1, 1, 1, 12]
def baseStart_2098801 : Nat := 118140960795 + 2098801 * 2 ^ 59
def prefixEnd_2098801 : Nat := 4983230072969 + 3 ^ 40 * 2098801 * 2
def baseEnd_2098801 : Nat := 79829163787936901121133

theorem tailTrace_2098801 : CollatzResearch.WordTrace tailWord_2098801 prefixEnd_2098801 79829163787936901121133 := by
  unfold tailWord_2098801
  simp only [CollatzResearch.WordTrace]
  refine ⟨76549561269409898518512257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51033040846273265679008171 76549561269409898518512257)
  ·
    refine ⟨57412170952057423888884193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76549561269409898518512257 57412170952057423888884193)
    ·
      refine ⟨43059128214043067916663145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57412170952057423888884193 43059128214043067916663145)
      ·
        refine ⟨32294346160532300937497359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43059128214043067916663145 32294346160532300937497359)
        ·
          refine ⟨48441519240798451406246039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32294346160532300937497359 48441519240798451406246039)
          ·
            refine ⟨72662278861197677109369059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48441519240798451406246039 72662278861197677109369059)
            ·
              refine ⟨108993418291796515664053589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72662278861197677109369059 108993418291796515664053589)
              ·
                refine ⟨79829163787936901121133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 108993418291796515664053589 79829163787936901121133)
                ·
                  rfl

theorem cell22_2098801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 12].length) (baseStart_2098801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098801 prefixEnd_2098801 := by exact prefixLift 2098801
  have htrace : WordTrace (prefixWord ++ tailWord_2098801) baseStart_2098801 baseEnd_2098801 := by
    simpa [prefixWord, tailWord_2098801, baseEnd_2098801] using wordTrace_append hprefix tailTrace_2098801
  have hstable : (prefixWord ++ tailWord_2098801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098801).length < 2 ^ (prefixWord ++ tailWord_2098801).sum := by decide
  have hdescent : baseEnd_2098801 < baseStart_2098801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098805 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2098805 : Nat := 118140960795 + 2098805 * 2 ^ 59
def prefixEnd_2098805 : Nat := 4983230072969 + 3 ^ 40 * 2098805 * 2
def baseEnd_2098805 : Nat := 718463843373177432990185

theorem tailTrace_2098805 : CollatzResearch.WordTrace tailWord_2098805 prefixEnd_2098805 718463843373177432990185 := by
  unfold tailWord_2098805
  simp only [CollatzResearch.WordTrace]
  refine ⟨76549707161395407201657869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51033138107596938134438579 76549707161395407201657869)
  ·
    refine ⟨28706140185523277700621701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76549707161395407201657869 28706140185523277700621701)
    ·
      refine ⟨5382401284785614568866569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28706140185523277700621701 5382401284785614568866569)
      ·
        refine ⟨4036800963589210926649927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5382401284785614568866569 4036800963589210926649927)
        ·
          refine ⟨6055201445383816389974891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4036800963589210926649927 6055201445383816389974891)
          ·
            refine ⟨9082802168075724584962337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6055201445383816389974891 9082802168075724584962337)
            ·
              refine ⟨6812101626056793438721753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9082802168075724584962337 6812101626056793438721753)
              ·
                refine ⟨5109076219542595079041315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6812101626056793438721753 5109076219542595079041315)
                ·
                  refine ⟨7663614329313892618561973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5109076219542595079041315 7663614329313892618561973)
                  ·
                    refine ⟨718463843373177432990185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7663614329313892618561973 718463843373177432990185)
                    ·
                      rfl

theorem cell22_2098805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2098805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098805 prefixEnd_2098805 := by exact prefixLift 2098805
  have htrace : WordTrace (prefixWord ++ tailWord_2098805) baseStart_2098805 baseEnd_2098805 := by
    simpa [prefixWord, tailWord_2098805, baseEnd_2098805] using wordTrace_append hprefix tailTrace_2098805
  have hstable : (prefixWord ++ tailWord_2098805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098805).length < 2 ^ (prefixWord ++ tailWord_2098805).sum := by decide
  have hdescent : baseEnd_2098805 < baseStart_2098805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098897 : List Nat := [1, 2, 2, 1, 2, 6, 2, 1, 5]
def baseStart_2098897 : Nat := 118140960795 + 2098897 * 2 ^ 59
def prefixEnd_2098897 : Nat := 4983230072969 + 3 ^ 40 * 2098897 * 2
def baseEnd_2098897 : Nat := 239498445617773286563301

theorem tailTrace_2098897 : CollatzResearch.WordTrace tailWord_2098897 prefixEnd_2098897 239498445617773286563301 := by
  unfold tailWord_2098897
  simp only [CollatzResearch.WordTrace]
  refine ⟨76553062677062106914006945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51035375118041404609337963 76553062677062106914006945)
  ·
    refine ⟨57414797007796580185505209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76553062677062106914006945 57414797007796580185505209)
    ·
      refine ⟨43061097755847435139128907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57414797007796580185505209 43061097755847435139128907)
      ·
        refine ⟨64591646633771152708693361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43061097755847435139128907 64591646633771152708693361)
        ·
          refine ⟨48443734975328364531520021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64591646633771152708693361 48443734975328364531520021)
          ·
            refine ⟨2270800076968517087415001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48443734975328364531520021 2270800076968517087415001)
            ·
              refine ⟨1703100057726387815561251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2270800076968517087415001 1703100057726387815561251)
              ·
                refine ⟨2554650086589581723341877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703100057726387815561251 2554650086589581723341877)
                ·
                  refine ⟨239498445617773286563301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2554650086589581723341877 239498445617773286563301)
                  ·
                    rfl

theorem cell22_2098897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 5].length) (baseStart_2098897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098897 prefixEnd_2098897 := by exact prefixLift 2098897
  have htrace : WordTrace (prefixWord ++ tailWord_2098897) baseStart_2098897 baseEnd_2098897 := by
    simpa [prefixWord, tailWord_2098897, baseEnd_2098897] using wordTrace_append hprefix tailTrace_2098897
  have hstable : (prefixWord ++ tailWord_2098897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098897).length < 2 ^ (prefixWord ++ tailWord_2098897).sum := by decide
  have hdescent : baseEnd_2098897 < baseStart_2098897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098923 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 3, 5]
def baseStart_2098923 : Nat := 118140960795 + 2098923 * 2 ^ 59
def prefixEnd_2098923 : Nat := 4983230072969 + 3 ^ 40 * 2098923 * 2
def baseEnd_2098923 : Nat := 718504237184664458539823

theorem tailTrace_2098923 : CollatzResearch.WordTrace tailWord_2098923 prefixEnd_2098923 718504237184664458539823 := by
  unfold tailWord_2098923
  simp only [CollatzResearch.WordTrace]
  refine ⟨76554010974967913354453423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51036007316645275569635615 76554010974967913354453423)
  ·
    refine ⟨114831016462451870031680135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76554010974967913354453423 114831016462451870031680135)
    ·
      refine ⟨172246524693677805047520203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114831016462451870031680135 172246524693677805047520203)
      ·
        refine ⟨258369787040516707571280305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172246524693677805047520203 258369787040516707571280305)
        ·
          refine ⟨193777340280387530678460229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258369787040516707571280305 193777340280387530678460229)
          ·
            refine ⟨36333251302572662002211293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193777340280387530678460229 36333251302572662002211293)
            ·
              refine ⟨13624969238464748250829235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36333251302572662002211293 13624969238464748250829235)
              ·
                refine ⟨20437453857697122376243853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13624969238464748250829235 20437453857697122376243853)
                ·
                  refine ⟨7664045196636420891091445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20437453857697122376243853 7664045196636420891091445)
                  ·
                    refine ⟨718504237184664458539823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7664045196636420891091445 718504237184664458539823)
                    ·
                      rfl

theorem cell22_2098923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_2098923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098923 prefixEnd_2098923 := by exact prefixLift 2098923
  have htrace : WordTrace (prefixWord ++ tailWord_2098923) baseStart_2098923 baseEnd_2098923 := by
    simpa [prefixWord, tailWord_2098923, baseEnd_2098923] using wordTrace_append hprefix tailTrace_2098923
  have hstable : (prefixWord ++ tailWord_2098923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098923).length < 2 ^ (prefixWord ++ tailWord_2098923).sum := by decide
  have hdescent : baseEnd_2098923 < baseStart_2098923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098927 : List Nat := [1, 1, 2, 1, 5, 1, 5, 1, 1, 4]
def baseStart_2098927 : Nat := 118140960795 + 2098927 * 2 ^ 59
def prefixEnd_2098927 : Nat := 4983230072969 + 3 ^ 40 * 2098927 * 2
def baseEnd_2098927 : Nat := 718505606466409781439811

theorem tailTrace_2098927 : CollatzResearch.WordTrace tailWord_2098927 prefixEnd_2098927 718505606466409781439811 := by
  unfold tailWord_2098927
  simp only [CollatzResearch.WordTrace]
  refine ⟨76554156866953422037599035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51036104577968948025066023 76554156866953422037599035)
  ·
    refine ⟨114831235300430133056398553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76554156866953422037599035 114831235300430133056398553)
    ·
      refine ⟨86123426475322599792298915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114831235300430133056398553 86123426475322599792298915)
      ·
        refine ⟨129185139712983899688448373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86123426475322599792298915 129185139712983899688448373)
        ·
          refine ⟨12111106848092240595792035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129185139712983899688448373 12111106848092240595792035)
          ·
            refine ⟨18166660272138360893688053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12111106848092240595792035 18166660272138360893688053)
            ·
              refine ⟨1703124400512971333783255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18166660272138360893688053 1703124400512971333783255)
              ·
                refine ⟨2554686600769457000674883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703124400512971333783255 2554686600769457000674883)
                ·
                  refine ⟨3832029901154185501012325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554686600769457000674883 3832029901154185501012325)
                  ·
                    refine ⟨718505606466409781439811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3832029901154185501012325 718505606466409781439811)
                    ·
                      rfl

theorem cell22_2098927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 1, 4].length) (baseStart_2098927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098927 prefixEnd_2098927 := by exact prefixLift 2098927
  have htrace : WordTrace (prefixWord ++ tailWord_2098927) baseStart_2098927 baseEnd_2098927 := by
    simpa [prefixWord, tailWord_2098927, baseEnd_2098927] using wordTrace_append hprefix tailTrace_2098927
  have hstable : (prefixWord ++ tailWord_2098927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098927).length < 2 ^ (prefixWord ++ tailWord_2098927).sum := by decide
  have hdescent : baseEnd_2098927 < baseStart_2098927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2098938 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_2098938 : Nat := 118140960795 + 2098938 * 2 ^ 59
def prefixEnd_2098938 : Nat := 4983230072969 + 3 ^ 40 * 2098938 * 2
def baseEnd_2098938 : Nat := 718509371991209419414777

theorem tailTrace_2098938 : CollatzResearch.WordTrace tailWord_2098938 prefixEnd_2098938 718509371991209419414777 := by
  unfold tailWord_2098938
  simp only [CollatzResearch.WordTrace]
  refine ⟨19138639517478392729062367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51036372046609047277499645 19138639517478392729062367)
  ·
    refine ⟨28707959276217589093593551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19138639517478392729062367 28707959276217589093593551)
    ·
      refine ⟨43061938914326383640390327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28707959276217589093593551 43061938914326383640390327)
      ·
        refine ⟨64592908371489575460585491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43061938914326383640390327 64592908371489575460585491)
        ·
          refine ⟨96889362557234363190878237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64592908371489575460585491 96889362557234363190878237)
          ·
            refine ⟨36333510958962886196579339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96889362557234363190878237 36333510958962886196579339)
            ·
              refine ⟨54500266438444329294869009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36333510958962886196579339 54500266438444329294869009)
              ·
                refine ⟨40875199828833246971151757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54500266438444329294869009 40875199828833246971151757)
                ·
                  refine ⟨15328199935812467614181909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40875199828833246971151757 15328199935812467614181909)
                  ·
                    refine ⟨718509371991209419414777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15328199935812467614181909 718509371991209419414777)
                    ·
                      rfl

theorem cell22_2098938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_2098938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2098938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2098938 prefixEnd_2098938 := by exact prefixLift 2098938
  have htrace : WordTrace (prefixWord ++ tailWord_2098938) baseStart_2098938 baseEnd_2098938 := by
    simpa [prefixWord, tailWord_2098938, baseEnd_2098938] using wordTrace_append hprefix tailTrace_2098938
  have hstable : (prefixWord ++ tailWord_2098938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2098938).length < 2 ^ (prefixWord ++ tailWord_2098938).sum := by decide
  have hdescent : baseEnd_2098938 < baseStart_2098938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2098938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099002 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 3, 3]
def baseStart_2099002 : Nat := 118140960795 + 2099002 * 2 ^ 59
def prefixEnd_2099002 : Nat := 4983230072969 + 3 ^ 40 * 2099002 * 2
def baseEnd_2099002 : Nat := 718531280499134585814581

theorem tailTrace_2099002 : CollatzResearch.WordTrace tailWord_2099002 prefixEnd_2099002 718531280499134585814581 := by
  unfold tailWord_2099002
  simp only [CollatzResearch.WordTrace]
  refine ⟨19139223085420427461644815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51037928227787806564386173 19139223085420427461644815)
  ·
    refine ⟨28708834628130641192467223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19139223085420427461644815 28708834628130641192467223)
    ·
      refine ⟨43063251942195961788700835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28708834628130641192467223 43063251942195961788700835)
      ·
        refine ⟨64594877913293942683051253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43063251942195961788700835 64594877913293942683051253)
        ·
          refine ⟨6055769804371307126536055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64594877913293942683051253 6055769804371307126536055)
          ·
            refine ⟨9083654706556960689804083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6055769804371307126536055 9083654706556960689804083)
            ·
              refine ⟨13625482059835441034706125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9083654706556960689804083 13625482059835441034706125)
              ·
                refine ⟨5109555772438290388014797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13625482059835441034706125 5109555772438290388014797)
                ·
                  refine ⟨1916083414664358895505549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5109555772438290388014797 1916083414664358895505549)
                  ·
                    refine ⟨718531280499134585814581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1916083414664358895505549 718531280499134585814581)
                    ·
                      rfl

theorem cell22_2099002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_2099002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099002 prefixEnd_2099002 := by exact prefixLift 2099002
  have htrace : WordTrace (prefixWord ++ tailWord_2099002) baseStart_2099002 baseEnd_2099002 := by
    simpa [prefixWord, tailWord_2099002, baseEnd_2099002] using wordTrace_append hprefix tailTrace_2099002
  have hstable : (prefixWord ++ tailWord_2099002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099002).length < 2 ^ (prefixWord ++ tailWord_2099002).sum := by decide
  have hdescent : baseEnd_2099002 < baseStart_2099002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099015 : List Nat := [1, 1, 4, 1, 2, 1, 2, 5, 5]
def baseStart_2099015 : Nat := 118140960795 + 2099015 * 2 ^ 59
def prefixEnd_2099015 : Nat := 4983230072969 + 3 ^ 40 * 2099015 * 2
def baseEnd_2099015 : Nat := 239511910221602295079847

theorem tailTrace_2099015 : CollatzResearch.WordTrace tailWord_2099015 prefixEnd_2099015 239511910221602295079847 := by
  unfold tailWord_2099015
  simp only [CollatzResearch.WordTrace]
  refine ⟨76557366490634613066802499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51038244327089742044534999 76557366490634613066802499)
  ·
    refine ⟨114836049735951919600203749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76557366490634613066802499 114836049735951919600203749)
    ·
      refine ⟨21531759325490984925038203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114836049735951919600203749 21531759325490984925038203)
      ·
        refine ⟨32297638988236477387557305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21531759325490984925038203 32297638988236477387557305)
        ·
          refine ⟨24223229241177358040667979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32297638988236477387557305 24223229241177358040667979)
          ·
            refine ⟨36334843861766037061001969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24223229241177358040667979 36334843861766037061001969)
            ·
              refine ⟨27251132896324527795751477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36334843861766037061001969 27251132896324527795751477)
              ·
                refine ⟨2554793709030424480851701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27251132896324527795751477 2554793709030424480851701)
                ·
                  refine ⟨239511910221602295079847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2554793709030424480851701 239511910221602295079847)
                  ·
                    rfl

theorem cell22_2099015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 5].length) (baseStart_2099015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099015 prefixEnd_2099015 := by exact prefixLift 2099015
  have htrace : WordTrace (prefixWord ++ tailWord_2099015) baseStart_2099015 baseEnd_2099015 := by
    simpa [prefixWord, tailWord_2099015, baseEnd_2099015] using wordTrace_append hprefix tailTrace_2099015
  have hstable : (prefixWord ++ tailWord_2099015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099015).length < 2 ^ (prefixWord ++ tailWord_2099015).sum := by decide
  have hdescent : baseEnd_2099015 < baseStart_2099015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099045 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_2099045 : Nat := 118140960795 + 2099045 * 2 ^ 59
def prefixEnd_2099045 : Nat := 4983230072969 + 3 ^ 40 * 2099045 * 2
def baseEnd_2099045 : Nat := 718546000277896806989449

theorem tailTrace_2099045 : CollatzResearch.WordTrace tailWord_2099045 prefixEnd_2099045 718546000277896806989449 := by
  unfold tailWord_2099045
  simp only [CollatzResearch.WordTrace]
  refine ⟨76558460680525928190394589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51038973787017285460263059 76558460680525928190394589)
  ·
    refine ⟨28709422755197223071397971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76558460680525928190394589 28709422755197223071397971)
    ·
      refine ⟨43064134132795834607096957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28709422755197223071397971 43064134132795834607096957)
      ·
        refine ⟨16149050299798437977661359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43064134132795834607096957 16149050299798437977661359)
        ·
          refine ⟨24223575449697656966492039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16149050299798437977661359 24223575449697656966492039)
          ·
            refine ⟨36335363174546485449738059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24223575449697656966492039 36335363174546485449738059)
            ·
              refine ⟨54503044761819728174607089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36335363174546485449738059 54503044761819728174607089)
              ·
                refine ⟨40877283571364796130955317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54503044761819728174607089 40877283571364796130955317)
                ·
                  refine ⟨3832245334815449637277061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40877283571364796130955317 3832245334815449637277061)
                  ·
                    refine ⟨718546000277896806989449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3832245334815449637277061 718546000277896806989449)
                    ·
                      rfl

theorem cell22_2099045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_2099045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099045 prefixEnd_2099045 := by exact prefixLift 2099045
  have htrace : WordTrace (prefixWord ++ tailWord_2099045) baseStart_2099045 baseEnd_2099045 := by
    simpa [prefixWord, tailWord_2099045, baseEnd_2099045] using wordTrace_append hprefix tailTrace_2099045
  have hstable : (prefixWord ++ tailWord_2099045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099045).length < 2 ^ (prefixWord ++ tailWord_2099045).sum := by decide
  have hdescent : baseEnd_2099045 < baseStart_2099045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099092 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2099092 : Nat := 118140960795 + 2099092 * 2 ^ 59
def prefixEnd_2099092 : Nat := 4983230072969 + 3 ^ 40 * 2099092 * 2
def baseEnd_2099092 : Nat := 718562089338404351064305

theorem tailTrace_2099092 : CollatzResearch.WordTrace tailWord_2099092 prefixEnd_2099092 718562089338404351064305 := by
  unfold tailWord_2099092
  simp only [CollatzResearch.WordTrace]
  refine ⟨38280087455677827608677765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51040116607570436811570353 38280087455677827608677765)
  ·
    refine ⟨7177516397939592676627081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38280087455677827608677765 7177516397939592676627081)
    ·
      refine ⟨5383137298454694507470311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7177516397939592676627081 5383137298454694507470311)
      ·
        refine ⟨8074705947682041761205467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5383137298454694507470311 8074705947682041761205467)
        ·
          refine ⟨12112058921523062641808201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8074705947682041761205467 12112058921523062641808201)
          ·
            refine ⟨9084044191142296981356151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12112058921523062641808201 9084044191142296981356151)
            ·
              refine ⟨13626066286713445472034227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9084044191142296981356151 13626066286713445472034227)
              ·
                refine ⟨20439099430070168208051341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13626066286713445472034227 20439099430070168208051341)
                ·
                  refine ⟨7664662286276313078019253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20439099430070168208051341 7664662286276313078019253)
                  ·
                    refine ⟨718562089338404351064305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7664662286276313078019253 718562089338404351064305)
                    ·
                      rfl

theorem cell22_2099092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2099092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099092 prefixEnd_2099092 := by exact prefixLift 2099092
  have htrace : WordTrace (prefixWord ++ tailWord_2099092) baseStart_2099092 baseEnd_2099092 := by
    simpa [prefixWord, tailWord_2099092, baseEnd_2099092] using wordTrace_append hprefix tailTrace_2099092
  have hstable : (prefixWord ++ tailWord_2099092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099092).length < 2 ^ (prefixWord ++ tailWord_2099092).sum := by decide
  have hdescent : baseEnd_2099092 < baseStart_2099092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099105 : List Nat := [1, 2, 3, 4, 12]
def baseStart_2099105 : Nat := 118140960795 + 2099105 * 2 ^ 59
def prefixEnd_2099105 : Nat := 4983230072969 + 3 ^ 40 * 2099105 * 2
def baseEnd_2099105 : Nat := 2957063948576447121355

theorem tailTrace_2099105 : CollatzResearch.WordTrace tailWord_2099105 prefixEnd_2099105 2957063948576447121355 := by
  unfold tailWord_2099105
  simp only [CollatzResearch.WordTrace]
  refine ⟨76560649060308558437578769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51040432706872372291719179 76560649060308558437578769)
  ·
    refine ⟨57420486795231418828184077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76560649060308558437578769 57420486795231418828184077)
    ·
      refine ⟨21532682548211782060569029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57420486795231418828184077 21532682548211782060569029)
      ·
        refine ⟨4037377977789709136356693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21532682548211782060569029 4037377977789709136356693)
        ·
          refine ⟨2957063948576447121355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4037377977789709136356693 2957063948576447121355)
          ·
            rfl

theorem cell22_2099105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 12].length) (baseStart_2099105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099105 prefixEnd_2099105 := by exact prefixLift 2099105
  have htrace : WordTrace (prefixWord ++ tailWord_2099105) baseStart_2099105 baseEnd_2099105 := by
    simpa [prefixWord, tailWord_2099105, baseEnd_2099105] using wordTrace_append hprefix tailTrace_2099105
  have hstable : (prefixWord ++ tailWord_2099105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099105).length < 2 ^ (prefixWord ++ tailWord_2099105).sum := by decide
  have hdescent : baseEnd_2099105 < baseStart_2099105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099111 : List Nat := [1, 1, 6, 1, 2, 1, 4, 2, 4]
def baseStart_2099111 : Nat := 118140960795 + 2099111 * 2 ^ 59
def prefixEnd_2099111 : Nat := 4983230072969 + 3 ^ 40 * 2099111 * 2
def baseEnd_2099111 : Nat := 239522864475564878279749

theorem tailTrace_2099111 : CollatzResearch.WordTrace tailWord_2099111 prefixEnd_2099111 239522864475564878279749 := by
  unfold tailWord_2099111
  simp only [CollatzResearch.WordTrace]
  refine ⟨76560867898286821462297187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51040578598857880974864791 76560867898286821462297187)
  ·
    refine ⟨114841301847430232193445781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76560867898286821462297187 114841301847430232193445781)
    ·
      refine ⟨5383186024098292134067771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114841301847430232193445781 5383186024098292134067771)
      ·
        refine ⟨8074779036147438201101657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5383186024098292134067771 8074779036147438201101657)
        ·
          refine ⟨6056084277110578650826243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8074779036147438201101657 6056084277110578650826243)
          ·
            refine ⟨9084126415665867976239365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6056084277110578650826243 9084126415665867976239365)
            ·
              refine ⟨1703273702937350245544881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9084126415665867976239365 1703273702937350245544881)
              ·
                refine ⟨1277455277203012684158661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1703273702937350245544881 1277455277203012684158661)
                ·
                  refine ⟨239522864475564878279749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1277455277203012684158661 239522864475564878279749)
                  ·
                    rfl

theorem cell22_2099111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 4].length) (baseStart_2099111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099111 prefixEnd_2099111 := by exact prefixLift 2099111
  have htrace : WordTrace (prefixWord ++ tailWord_2099111) baseStart_2099111 baseEnd_2099111 := by
    simpa [prefixWord, tailWord_2099111, baseEnd_2099111] using wordTrace_append hprefix tailTrace_2099111
  have hstable : (prefixWord ++ tailWord_2099111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099111).length < 2 ^ (prefixWord ++ tailWord_2099111).sum := by decide
  have hdescent : baseEnd_2099111 < baseStart_2099111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099135 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 2, 6]
def baseStart_2099135 : Nat := 118140960795 + 2099135 * 2 ^ 59
def prefixEnd_2099135 : Nat := 4983230072969 + 3 ^ 40 * 2099135 * 2
def baseEnd_2099135 : Nat := 718576809117166572239173

theorem tailTrace_2099135 : CollatzResearch.WordTrace tailWord_2099135 prefixEnd_2099135 718576809117166572239173 := by
  unfold tailWord_2099135
  simp only [CollatzResearch.WordTrace]
  refine ⟨76561743250199873561170859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51041162166799915707447239 76561743250199873561170859)
  ·
    refine ⟨114842614875299810341756289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76561743250199873561170859 114842614875299810341756289)
    ·
      refine ⟨86131961156474857756317217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114842614875299810341756289 86131961156474857756317217)
      ·
        refine ⟨64598970867356143317237913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86131961156474857756317217 64598970867356143317237913)
        ·
          refine ⟨48449228150517107487928435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64598970867356143317237913 48449228150517107487928435)
          ·
            refine ⟨72673842225775661231892653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48449228150517107487928435 72673842225775661231892653)
            ·
              refine ⟨27252690834665872961959745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72673842225775661231892653 27252690834665872961959745)
              ·
                refine ⟨20439518125999404721469809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27252690834665872961959745 20439518125999404721469809)
                ·
                  refine ⟨15329638594499553541102357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20439518125999404721469809 15329638594499553541102357)
                  ·
                    refine ⟨718576809117166572239173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15329638594499553541102357 718576809117166572239173)
                    ·
                      rfl

theorem cell22_2099135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_2099135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099135 prefixEnd_2099135 := by exact prefixLift 2099135
  have htrace : WordTrace (prefixWord ++ tailWord_2099135) baseStart_2099135 baseEnd_2099135 := by
    simpa [prefixWord, tailWord_2099135, baseEnd_2099135] using wordTrace_append hprefix tailTrace_2099135
  have hstable : (prefixWord ++ tailWord_2099135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099135).length < 2 ^ (prefixWord ++ tailWord_2099135).sum := by decide
  have hdescent : baseEnd_2099135 < baseStart_2099135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099167 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 7]
def baseStart_2099167 : Nat := 118140960795 + 2099167 * 2 ^ 59
def prefixEnd_2099167 : Nat := 4983230072969 + 3 ^ 40 * 2099167 * 2
def baseEnd_2099167 : Nat := 239529254457043051813025

theorem tailTrace_2099167 : CollatzResearch.WordTrace tailWord_2099167 prefixEnd_2099167 239529254457043051813025 := by
  unfold tailWord_2099167
  simp only [CollatzResearch.WordTrace]
  refine ⟨76562910386083943026335755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51041940257389295350890503 76562910386083943026335755)
  ·
    refine ⟨114844365579125914539503633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76562910386083943026335755 114844365579125914539503633)
    ·
      refine ⟨86133274184344435904627725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114844365579125914539503633 86133274184344435904627725)
      ·
        refine ⟨32299977819129163464235397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86133274184344435904627725 32299977819129163464235397)
        ·
          refine ⟨6056245841086718149544137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32299977819129163464235397 6056245841086718149544137)
          ·
            refine ⟨4542184380815038612158103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6056245841086718149544137 4542184380815038612158103)
            ·
              refine ⟨6813276571222557918237155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4542184380815038612158103 6813276571222557918237155)
              ·
                refine ⟨10219914856833836877355733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6813276571222557918237155 10219914856833836877355733)
                ·
                  refine ⟨239529254457043051813025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10219914856833836877355733 239529254457043051813025)
                  ·
                    rfl

theorem cell22_2099167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 7].length) (baseStart_2099167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099167 prefixEnd_2099167 := by exact prefixLift 2099167
  have htrace : WordTrace (prefixWord ++ tailWord_2099167) baseStart_2099167 baseEnd_2099167 := by
    simpa [prefixWord, tailWord_2099167, baseEnd_2099167] using wordTrace_append hprefix tailTrace_2099167
  have hstable : (prefixWord ++ tailWord_2099167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099167).length < 2 ^ (prefixWord ++ tailWord_2099167).sum := by decide
  have hdescent : baseEnd_2099167 < baseStart_2099167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099171 : List Nat := [1, 1, 1, 6, 1, 2, 2, 4, 1, 3]
def baseStart_2099171 : Nat := 118140960795 + 2099171 * 2 ^ 59
def prefixEnd_2099171 : Nat := 4983230072969 + 3 ^ 40 * 2099171 * 2
def baseEnd_2099171 : Nat := 718589132652874478339063

theorem tailTrace_2099171 : CollatzResearch.WordTrace tailWord_2099171 prefixEnd_2099171 718589132652874478339063 := by
  unfold tailWord_2099171
  simp only [CollatzResearch.WordTrace]
  refine ⟨76563056278069451709481367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51042037518712967806320911 76563056278069451709481367)
  ·
    refine ⟨114844584417104177564222051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76563056278069451709481367 114844584417104177564222051)
    ·
      refine ⟨172266876625656266346333077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114844584417104177564222051 172266876625656266346333077)
      ·
        refine ⟨8075009841827637484984363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 172266876625656266346333077 8075009841827637484984363)
        ·
          refine ⟨12112514762741456227476545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8075009841827637484984363 12112514762741456227476545)
          ·
            refine ⟨9084386072056092170607409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12112514762741456227476545 9084386072056092170607409)
            ·
              refine ⟨6813289554042069127955557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9084386072056092170607409 6813289554042069127955557)
              ·
                refine ⟨1277491791382887961491667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6813289554042069127955557 1277491791382887961491667)
                ·
                  refine ⟨1916237687074331942237501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277491791382887961491667 1916237687074331942237501)
                  ·
                    refine ⟨718589132652874478339063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1916237687074331942237501 718589132652874478339063)
                    ·
                      rfl

theorem cell22_2099171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 1, 3].length) (baseStart_2099171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099171 prefixEnd_2099171 := by exact prefixLift 2099171
  have htrace : WordTrace (prefixWord ++ tailWord_2099171) baseStart_2099171 baseEnd_2099171 := by
    simpa [prefixWord, tailWord_2099171, baseEnd_2099171] using wordTrace_append hprefix tailTrace_2099171
  have hstable : (prefixWord ++ tailWord_2099171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099171).length < 2 ^ (prefixWord ++ tailWord_2099171).sum := by decide
  have hdescent : baseEnd_2099171 < baseStart_2099171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099197 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_2099197 : Nat := 118140960795 + 2099197 * 2 ^ 59
def prefixEnd_2099197 : Nat := 4983230072969 + 3 ^ 40 * 2099197 * 2
def baseEnd_2099197 : Nat := 718598032984219077188983

theorem tailTrace_2099197 : CollatzResearch.WordTrace tailWord_2099197 prefixEnd_2099197 718598032984219077188983 := by
  unfold tailWord_2099197
  simp only [CollatzResearch.WordTrace]
  refine ⟨76564004575975258149927845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51042669717316838766618563 76564004575975258149927845)
  ·
    refine ⟨14355750857995360903111471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76564004575975258149927845 14355750857995360903111471)
    ·
      refine ⟨21533626286993041354667207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14355750857995360903111471 21533626286993041354667207)
      ·
        refine ⟨32300439430489562032000811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21533626286993041354667207 32300439430489562032000811)
        ·
          refine ⟨48450659145734343048001217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32300439430489562032000811 48450659145734343048001217)
          ·
            refine ⟨36337994359300757286000913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48450659145734343048001217 36337994359300757286000913)
            ·
              refine ⟨27253495769475567964500685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36337994359300757286000913 27253495769475567964500685)
              ·
                refine ⟨10220060913553337986687757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27253495769475567964500685 10220060913553337986687757)
                ·
                  refine ⟨3832522842582501745007909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10220060913553337986687757 3832522842582501745007909)
                  ·
                    refine ⟨718598032984219077188983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3832522842582501745007909 718598032984219077188983)
                    ·
                      rfl

theorem cell22_2099197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_2099197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099197 prefixEnd_2099197 := by exact prefixLift 2099197
  have htrace : WordTrace (prefixWord ++ tailWord_2099197) baseStart_2099197 baseEnd_2099197 := by
    simpa [prefixWord, tailWord_2099197, baseEnd_2099197] using wordTrace_append hprefix tailTrace_2099197
  have hstable : (prefixWord ++ tailWord_2099197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099197).length < 2 ^ (prefixWord ++ tailWord_2099197).sum := by decide
  have hdescent : baseEnd_2099197 < baseStart_2099197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099214 : List Nat := [4, 1, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_2099214 : Nat := 118140960795 + 2099214 * 2 ^ 59
def prefixEnd_2099214 : Nat := 4983230072969 + 3 ^ 40 * 2099214 * 2
def baseEnd_2099214 : Nat := 718603852431636699513931

theorem tailTrace_2099214 : CollatzResearch.WordTrace tailWord_2099214 prefixEnd_2099214 718603852431636699513931 := by
  unfold tailWord_2099214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9570578077114208756662087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51043083077942446702197797 9570578077114208756662087)
  ·
    refine ⟨14355867115671313134993131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9570578077114208756662087 14355867115671313134993131)
    ·
      refine ⟨21533800673506969702489697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14355867115671313134993131 21533800673506969702489697)
      ·
        refine ⟨16150350505130227276867273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21533800673506969702489697 16150350505130227276867273)
        ·
          refine ⟨12112762878847670457650455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16150350505130227276867273 12112762878847670457650455)
          ·
            refine ⟨18169144318271505686475683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12112762878847670457650455 18169144318271505686475683)
            ·
              refine ⟨27253716477407258529713525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18169144318271505686475683 27253716477407258529713525)
              ·
                refine ⟨2555035919756930487160643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27253716477407258529713525 2555035919756930487160643)
                ·
                  refine ⟨3832553879635395730740965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2555035919756930487160643 3832553879635395730740965)
                  ·
                    refine ⟨718603852431636699513931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3832553879635395730740965 718603852431636699513931)
                    ·
                      rfl

theorem cell22_2099214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_2099214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099214 prefixEnd_2099214 := by exact prefixLift 2099214
  have htrace : WordTrace (prefixWord ++ tailWord_2099214) baseStart_2099214 baseEnd_2099214 := by
    simpa [prefixWord, tailWord_2099214, baseEnd_2099214] using wordTrace_append hprefix tailTrace_2099214
  have hstable : (prefixWord ++ tailWord_2099214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099214).length < 2 ^ (prefixWord ++ tailWord_2099214).sum := by decide
  have hdescent : baseEnd_2099214 < baseStart_2099214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099229 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 6]
def baseStart_2099229 : Nat := 118140960795 + 2099229 * 2 ^ 59
def prefixEnd_2099229 : Nat := 4983230072969 + 3 ^ 40 * 2099229 * 2
def baseEnd_2099229 : Nat := 239536329079393886796295

theorem tailTrace_2099229 : CollatzResearch.WordTrace tailWord_2099229 prefixEnd_2099229 239536329079393886796295 := by
  unfold tailWord_2099229
  simp only [CollatzResearch.WordTrace]
  refine ⟨76565171711859327615092741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51043447807906218410061827 76565171711859327615092741)
  ·
    refine ⟨14355969695973623927829889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76565171711859327615092741 14355969695973623927829889)
    ·
      refine ⟨10766977271980217945872417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14355969695973623927829889 10766977271980217945872417)
      ·
        refine ⟨8075232953985163459404313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10766977271980217945872417 8075232953985163459404313)
        ·
          refine ⟨6056424715488872594553235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8075232953985163459404313 6056424715488872594553235)
          ·
            refine ⟨9084637073233308891829853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6056424715488872594553235 9084637073233308891829853)
            ·
              refine ⟨3406738902462490834436195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9084637073233308891829853 3406738902462490834436195)
              ·
                refine ⟨5110108353693736251654293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406738902462490834436195 5110108353693736251654293)
                ·
                  refine ⟨239536329079393886796295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5110108353693736251654293 239536329079393886796295)
                  ·
                    rfl

theorem cell22_2099229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_2099229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099229 prefixEnd_2099229 := by exact prefixLift 2099229
  have htrace : WordTrace (prefixWord ++ tailWord_2099229) baseStart_2099229 baseEnd_2099229 := by
    simpa [prefixWord, tailWord_2099229, baseEnd_2099229] using wordTrace_append hprefix tailTrace_2099229
  have hstable : (prefixWord ++ tailWord_2099229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099229).length < 2 ^ (prefixWord ++ tailWord_2099229).sum := by decide
  have hdescent : baseEnd_2099229 < baseStart_2099229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099287 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 2, 6]
def baseStart_2099287 : Nat := 118140960795 + 2099287 * 2 ^ 59
def prefixEnd_2099287 : Nat := 4983230072969 + 3 ^ 40 * 2099287 * 2
def baseEnd_2099287 : Nat := 718628841823488842438707

theorem tailTrace_2099287 : CollatzResearch.WordTrace tailWord_2099287 prefixEnd_2099287 718628841823488842438707 := by
  unfold tailWord_2099287
  simp only [CollatzResearch.WordTrace]
  refine ⟨76567287145649203520704115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51044858097099469013802743 76567287145649203520704115)
  ·
    refine ⟨114850930718473805281056173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76567287145649203520704115 114850930718473805281056173)
    ·
      refine ⟨43069099019427676980396065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114850930718473805281056173 43069099019427676980396065)
      ·
        refine ⟨32301824264570757735297049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43069099019427676980396065 32301824264570757735297049)
        ·
          refine ⟨24226368198428068301472787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32301824264570757735297049 24226368198428068301472787)
          ·
            refine ⟨36339552297642102452209181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24226368198428068301472787 36339552297642102452209181)
            ·
              refine ⟨13627332111615788419578443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36339552297642102452209181 13627332111615788419578443)
              ·
                refine ⟨20440998167423682629367665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13627332111615788419578443 20440998167423682629367665)
                ·
                  refine ⟨15330748625567761972025749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20440998167423682629367665 15330748625567761972025749)
                  ·
                    refine ⟨718628841823488842438707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15330748625567761972025749 718628841823488842438707)
                    ·
                      rfl

theorem cell22_2099287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_2099287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099287 prefixEnd_2099287 := by exact prefixLift 2099287
  have htrace : WordTrace (prefixWord ++ tailWord_2099287) baseStart_2099287 baseEnd_2099287 := by
    simpa [prefixWord, tailWord_2099287, baseEnd_2099287] using wordTrace_append hprefix tailTrace_2099287
  have hstable : (prefixWord ++ tailWord_2099287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099287).length < 2 ^ (prefixWord ++ tailWord_2099287).sum := by decide
  have hdescent : baseEnd_2099287 < baseStart_2099287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099289 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 3, 3]
def baseStart_2099289 : Nat := 118140960795 + 2099289 * 2 ^ 59
def prefixEnd_2099289 : Nat := 4983230072969 + 3 ^ 40 * 2099289 * 2
def baseEnd_2099289 : Nat := 718629526464361503888701

theorem tailTrace_2099289 : CollatzResearch.WordTrace tailWord_2099289 prefixEnd_2099289 718629526464361503888701 := by
  unfold tailWord_2099289
  simp only [CollatzResearch.WordTrace]
  refine ⟨76567360091641957862276921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51044906727761305241517947 76567360091641957862276921)
  ·
    refine ⟨57425520068731468396707691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76567360091641957862276921 57425520068731468396707691)
    ·
      refine ⟨86138280103097202595061537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57425520068731468396707691 86138280103097202595061537)
      ·
        refine ⟨64603710077322901946296153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86138280103097202595061537 64603710077322901946296153)
        ·
          refine ⟨48452782557992176459722115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64603710077322901946296153 48452782557992176459722115)
          ·
            refine ⟨72679173836988264689583173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48452782557992176459722115 72679173836988264689583173)
            ·
              refine ⟨13627345094435299629296845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72679173836988264689583173 13627345094435299629296845)
              ·
                refine ⟨5110254410413237360986317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13627345094435299629296845 5110254410413237360986317)
                ·
                  refine ⟨1916345403904964010369869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5110254410413237360986317 1916345403904964010369869)
                  ·
                    refine ⟨718629526464361503888701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1916345403904964010369869 718629526464361503888701)
                    ·
                      rfl

theorem cell22_2099289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 3].length) (baseStart_2099289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099289 prefixEnd_2099289 := by exact prefixLift 2099289
  have htrace : WordTrace (prefixWord ++ tailWord_2099289) baseStart_2099289 baseEnd_2099289 := by
    simpa [prefixWord, tailWord_2099289, baseEnd_2099289] using wordTrace_append hprefix tailTrace_2099289
  have hstable : (prefixWord ++ tailWord_2099289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099289).length < 2 ^ (prefixWord ++ tailWord_2099289).sum := by decide
  have hdescent : baseEnd_2099289 < baseStart_2099289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099336 : List Nat := [2, 1, 3, 4, 1, 1, 3, 2, 5]
def baseStart_2099336 : Nat := 118140960795 + 2099336 * 2 ^ 59
def prefixEnd_2099336 : Nat := 4983230072969 + 3 ^ 40 * 2099336 * 2
def baseEnd_2099336 : Nat := 239548538508289682654519

theorem tailTrace_2099336 : CollatzResearch.WordTrace tailWord_2099336 prefixEnd_2099336 239548538508289682654519 := by
  unfold tailWord_2099336
  simp only [CollatzResearch.WordTrace]
  refine ⟨38284537161235842444618931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51046049548314456592825241 38284537161235842444618931)
  ·
    refine ⟨57426805741853763666928397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38284537161235842444618931 57426805741853763666928397)
    ·
      refine ⟨21535052153195161375098149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57426805741853763666928397 21535052153195161375098149)
      ·
        refine ⟨4037822278724092757830903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21535052153195161375098149 4037822278724092757830903)
        ·
          refine ⟨6056733418086139136746355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4037822278724092757830903 6056733418086139136746355)
          ·
            refine ⟨9085100127129208705119533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6056733418086139136746355 9085100127129208705119533)
            ·
              refine ⟨3406912547673453264419825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9085100127129208705119533 3406912547673453264419825)
              ·
                refine ⟨2555184410755089948314869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3406912547673453264419825 2555184410755089948314869)
                ·
                  refine ⟨239548538508289682654519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2555184410755089948314869 239548538508289682654519)
                  ·
                    rfl

theorem cell22_2099336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_2099336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099336 prefixEnd_2099336 := by exact prefixLift 2099336
  have htrace : WordTrace (prefixWord ++ tailWord_2099336) baseStart_2099336 baseEnd_2099336 := by
    simpa [prefixWord, tailWord_2099336, baseEnd_2099336] using wordTrace_append hprefix tailTrace_2099336
  have hstable : (prefixWord ++ tailWord_2099336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099336).length < 2 ^ (prefixWord ++ tailWord_2099336).sum := by decide
  have hdescent : baseEnd_2099336 < baseStart_2099336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099374 : List Nat := [4, 1, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2099374 : Nat := 118140960795 + 2099374 * 2 ^ 59
def prefixEnd_2099374 : Nat := 4983230072969 + 3 ^ 40 * 2099374 * 2
def baseEnd_2099374 : Nat := 718658623701449615513441

theorem tailTrace_2099374 : CollatzResearch.WordTrace tailWord_2099374 prefixEnd_2099374 718658623701449615513441 := by
  unfold tailWord_2099374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9571307537041752172390147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51046973530889344919414117 9571307537041752172390147)
  ·
    refine ⟨14356961305562628258585221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9571307537041752172390147 14356961305562628258585221)
    ·
      refine ⟨2691930244792992798484729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14356961305562628258585221 2691930244792992798484729)
      ·
        refine ⟨2018947683594744598863547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2691930244792992798484729 2018947683594744598863547)
        ·
          refine ⟨3028421525392116898295321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018947683594744598863547 3028421525392116898295321)
          ·
            refine ⟨2271316144044087673721491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3028421525392116898295321 2271316144044087673721491)
            ·
              refine ⟨3406974216066131510582237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271316144044087673721491 3406974216066131510582237)
              ·
                refine ⟨1277615331024799316468339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3406974216066131510582237 1277615331024799316468339)
                ·
                  refine ⟨1916422996537198974702509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277615331024799316468339 1916422996537198974702509)
                  ·
                    refine ⟨718658623701449615513441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1916422996537198974702509 718658623701449615513441)
                    ·
                      rfl

theorem cell22_2099374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2099374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099374 prefixEnd_2099374 := by exact prefixLift 2099374
  have htrace : WordTrace (prefixWord ++ tailWord_2099374) baseStart_2099374 baseEnd_2099374 := by
    simpa [prefixWord, tailWord_2099374, baseEnd_2099374] using wordTrace_append hprefix tailTrace_2099374
  have hstable : (prefixWord ++ tailWord_2099374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099374).length < 2 ^ (prefixWord ++ tailWord_2099374).sum := by decide
  have hdescent : baseEnd_2099374 < baseStart_2099374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099505 : List Nat := [1, 2, 2, 3, 5, 1, 1, 2, 5]
def baseStart_2099505 : Nat := 118140960795 + 2099505 * 2 ^ 59
def prefixEnd_2099505 : Nat := 4983230072969 + 3 ^ 40 * 2099505 * 2
def baseEnd_2099505 : Nat := 239567822559536313496013

theorem tailTrace_2099505 : CollatzResearch.WordTrace tailWord_2099505 prefixEnd_2099505 239567822559536313496013 := by
  unfold tailWord_2099505
  simp only [CollatzResearch.WordTrace]
  refine ⟨76575238258859426752139969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51050158839239617834759979 76575238258859426752139969)
  ·
    refine ⟨57431428694144570064104977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76575238258859426752139969 57431428694144570064104977)
    ·
      refine ⟨43073571520608427548078733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57431428694144570064104977 43073571520608427548078733)
      ·
        refine ⟨16152589320228160330529525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43073571520608427548078733 16152589320228160330529525)
        ·
          refine ⟨1514305248771390030987143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16152589320228160330529525 1514305248771390030987143)
          ·
            refine ⟨2271457873157085046480715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514305248771390030987143 2271457873157085046480715)
            ·
              refine ⟨3407186809735627569721073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271457873157085046480715 3407186809735627569721073)
              ·
                refine ⟨2555390107301720677290805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3407186809735627569721073 2555390107301720677290805)
                ·
                  refine ⟨239567822559536313496013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2555390107301720677290805 239567822559536313496013)
                  ·
                    rfl

theorem cell22_2099505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 5].length) (baseStart_2099505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099505 prefixEnd_2099505 := by exact prefixLift 2099505
  have htrace : WordTrace (prefixWord ++ tailWord_2099505) baseStart_2099505 baseEnd_2099505 := by
    simpa [prefixWord, tailWord_2099505, baseEnd_2099505] using wordTrace_append hprefix tailTrace_2099505
  have hstable : (prefixWord ++ tailWord_2099505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099505).length < 2 ^ (prefixWord ++ tailWord_2099505).sum := by decide
  have hdescent : baseEnd_2099505 < baseStart_2099505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099516 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 6]
def baseStart_2099516 : Nat := 118140960795 + 2099516 * 2 ^ 59
def prefixEnd_2099516 : Nat := 4983230072969 + 3 ^ 40 * 2099516 * 2
def baseEnd_2099516 : Nat := 239569077734469526154335

theorem tailTrace_2099516 : CollatzResearch.WordTrace tailWord_2099516 prefixEnd_2099516 239569077734469526154335 := by
  unfold tailWord_2099516
  simp only [CollatzResearch.WordTrace]
  refine ⟨38287819730909787815395201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51050426307879717087193601 38287819730909787815395201)
  ·
    refine ⟨28715864798182340861546401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38287819730909787815395201 28715864798182340861546401)
    ·
      refine ⟨21536898598636755646159801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28715864798182340861546401 21536898598636755646159801)
      ·
        refine ⟨16152673948977566734619851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21536898598636755646159801 16152673948977566734619851)
        ·
          refine ⟨24229010923466350101929777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16152673948977566734619851 24229010923466350101929777)
          ·
            refine ⟨18171758192599762576447333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24229010923466350101929777 18171758192599762576447333)
            ·
              refine ⟨3407204661112455483083875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18171758192599762576447333 3407204661112455483083875)
              ·
                refine ⟨5110806991668683224625813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3407204661112455483083875 5110806991668683224625813)
                ·
                  refine ⟨239569077734469526154335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5110806991668683224625813 239569077734469526154335)
                  ·
                    rfl

theorem cell22_2099516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_2099516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099516 prefixEnd_2099516 := by exact prefixLift 2099516
  have htrace : WordTrace (prefixWord ++ tailWord_2099516) baseStart_2099516 baseEnd_2099516 := by
    simpa [prefixWord, tailWord_2099516, baseEnd_2099516] using wordTrace_append hprefix tailTrace_2099516
  have hstable : (prefixWord ++ tailWord_2099516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099516).length < 2 ^ (prefixWord ++ tailWord_2099516).sum := by decide
  have hdescent : baseEnd_2099516 < baseStart_2099516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099546 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_2099546 : Nat := 118140960795 + 2099546 * 2 ^ 59
def prefixEnd_2099546 : Nat := 4983230072969 + 3 ^ 40 * 2099546 * 2
def baseEnd_2099546 : Nat := 718717502816498500212913

theorem tailTrace_2099546 : CollatzResearch.WordTrace tailWord_2099546 prefixEnd_2099546 718717502816498500212913 := by
  unfold tailWord_2099546
  simp only [CollatzResearch.WordTrace]
  refine ⟨19144183412927722688595623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51051155767807260502921661 19144183412927722688595623)
  ·
    refine ⟨28716275119391584032893435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19144183412927722688595623 28716275119391584032893435)
    ·
      refine ⟨43074412679087376049340153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28716275119391584032893435 43074412679087376049340153)
      ·
        refine ⟨32305809509315532037005115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43074412679087376049340153 32305809509315532037005115)
        ·
          refine ⟨48458714263973298055507673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32305809509315532037005115 48458714263973298055507673)
          ·
            refine ⟨36344035697979973541630755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48458714263973298055507673 36344035697979973541630755)
            ·
              refine ⟨54516053546969960312446133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36344035697979973541630755 54516053546969960312446133)
              ·
                refine ⟨5110880020028433779291825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54516053546969960312446133 5110880020028433779291825)
                ·
                  refine ⟨3833160015021325334468869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5110880020028433779291825 3833160015021325334468869)
                  ·
                    refine ⟨718717502816498500212913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3833160015021325334468869 718717502816498500212913)
                    ·
                      rfl

theorem cell22_2099546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_2099546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099546 prefixEnd_2099546 := by exact prefixLift 2099546
  have htrace : WordTrace (prefixWord ++ tailWord_2099546) baseStart_2099546 baseEnd_2099546 := by
    simpa [prefixWord, tailWord_2099546, baseEnd_2099546] using wordTrace_append hprefix tailTrace_2099546
  have hstable : (prefixWord ++ tailWord_2099546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099546).length < 2 ^ (prefixWord ++ tailWord_2099546).sum := by decide
  have hdescent : baseEnd_2099546 < baseStart_2099546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099621 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_2099621 : Nat := 118140960795 + 2099621 * 2 ^ 59
def prefixEnd_2099621 : Nat := 4983230072969 + 3 ^ 40 * 2099621 * 2
def baseEnd_2099621 : Nat := 718743176849223304587683

theorem tailTrace_2099621 : CollatzResearch.WordTrace tailWord_2099621 prefixEnd_2099621 718743176849223304587683 := by
  unfold tailWord_2099621
  simp only [CollatzResearch.WordTrace]
  refine ⟨76579469126439178563362717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51052979417626119042241811 76579469126439178563362717)
  ·
    refine ⟨28717300922414691961261019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76579469126439178563362717 28717300922414691961261019)
    ·
      refine ⟨43075951383622037941891529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28717300922414691961261019 43075951383622037941891529)
      ·
        refine ⟨32306963537716528456418647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43075951383622037941891529 32306963537716528456418647)
        ·
          refine ⟨48460445306574792684627971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32306963537716528456418647 48460445306574792684627971)
          ·
            refine ⟨72690667959862189026941957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48460445306574792684627971 72690667959862189026941957)
            ·
              refine ⟨13629500242474160442551617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72690667959862189026941957 13629500242474160442551617)
              ·
                refine ⟨10222125181855620331913713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13629500242474160442551617 10222125181855620331913713)
                ·
                  refine ⟨7666593886391715248935285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10222125181855620331913713 7666593886391715248935285)
                  ·
                    refine ⟨718743176849223304587683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7666593886391715248935285 718743176849223304587683)
                    ·
                      rfl

theorem cell22_2099621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_2099621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099621 prefixEnd_2099621 := by exact prefixLift 2099621
  have htrace : WordTrace (prefixWord ++ tailWord_2099621) baseStart_2099621 baseEnd_2099621 := by
    simpa [prefixWord, tailWord_2099621, baseEnd_2099621] using wordTrace_append hprefix tailTrace_2099621
  have hstable : (prefixWord ++ tailWord_2099621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099621).length < 2 ^ (prefixWord ++ tailWord_2099621).sum := by decide
  have hdescent : baseEnd_2099621 < baseStart_2099621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099623 : List Nat := [1, 1, 6, 1, 1, 2, 1, 4, 5]
def baseStart_2099623 : Nat := 118140960795 + 2099623 * 2 ^ 59
def prefixEnd_2099623 : Nat := 4983230072969 + 3 ^ 40 * 2099623 * 2
def baseEnd_2099623 : Nat := 239581287163365322012559

theorem tailTrace_2099623 : CollatzResearch.WordTrace tailWord_2099623 prefixEnd_2099623 239581287163365322012559 := by
  unfold tailWord_2099623
  simp only [CollatzResearch.WordTrace]
  refine ⟨76579542072431932904935523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51053028048287955269957015 76579542072431932904935523)
  ·
    refine ⟨114869313108647899357403285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76579542072431932904935523 114869313108647899357403285)
    ·
      refine ⟨5384499051967870282378279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114869313108647899357403285 5384499051967870282378279)
      ·
        refine ⟨8076748577951805423567419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5384499051967870282378279 8076748577951805423567419)
        ·
          refine ⟨12115122866927708135351129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8076748577951805423567419 12115122866927708135351129)
          ·
            refine ⟨9086342150195781101513347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12115122866927708135351129 9086342150195781101513347)
            ·
              refine ⟨13629513225293671652270021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9086342150195781101513347 13629513225293671652270021)
              ·
                refine ⟨2555533729742563434800629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13629513225293671652270021 2555533729742563434800629)
                ·
                  refine ⟨239581287163365322012559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2555533729742563434800629 239581287163365322012559)
                  ·
                    rfl

theorem cell22_2099623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 5].length) (baseStart_2099623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099623 prefixEnd_2099623 := by exact prefixLift 2099623
  have htrace : WordTrace (prefixWord ++ tailWord_2099623) baseStart_2099623 baseEnd_2099623 := by
    simpa [prefixWord, tailWord_2099623, baseEnd_2099623] using wordTrace_append hprefix tailTrace_2099623
  have hstable : (prefixWord ++ tailWord_2099623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099623).length < 2 ^ (prefixWord ++ tailWord_2099623).sum := by decide
  have hdescent : baseEnd_2099623 < baseStart_2099623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099685 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 6]
def baseStart_2099685 : Nat := 118140960795 + 2099685 * 2 ^ 59
def prefixEnd_2099685 : Nat := 4983230072969 + 3 ^ 40 * 2099685 * 2
def baseEnd_2099685 : Nat := 239588361785716156995829

theorem tailTrace_2099685 : CollatzResearch.WordTrace tailWord_2099685 prefixEnd_2099685 239588361785716156995829 := by
  unfold tailWord_2099685
  simp only [CollatzResearch.WordTrace]
  refine ⟨76581803398207317493692509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51054535598804878329128339 76581803398207317493692509)
  ·
    refine ⟨28718176274327744060134691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76581803398207317493692509 28718176274327744060134691)
    ·
      refine ⟨43077264411491616090202037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28718176274327744060134691 43077264411491616090202037)
      ·
        refine ⟨4038493538577339008456441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43077264411491616090202037 4038493538577339008456441)
        ·
          refine ⟨3028870153933004256342331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4038493538577339008456441 3028870153933004256342331)
          ·
            refine ⟨4543305230899506384513497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3028870153933004256342331 4543305230899506384513497)
            ·
              refine ⟨3407478923174629788385123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4543305230899506384513497 3407478923174629788385123)
              ·
                refine ⟨5111218384761944682577685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3407478923174629788385123 5111218384761944682577685)
                ·
                  refine ⟨239588361785716156995829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5111218384761944682577685 239588361785716156995829)
                  ·
                    rfl

theorem cell22_2099685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_2099685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099685 prefixEnd_2099685 := by exact prefixLift 2099685
  have htrace : WordTrace (prefixWord ++ tailWord_2099685) baseStart_2099685 baseEnd_2099685 := by
    simpa [prefixWord, tailWord_2099685, baseEnd_2099685] using wordTrace_append hprefix tailTrace_2099685
  have hstable : (prefixWord ++ tailWord_2099685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099685).length < 2 ^ (prefixWord ++ tailWord_2099685).sum := by decide
  have hdescent : baseEnd_2099685 < baseStart_2099685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099696 : List Nat := [2, 1, 1, 1, 3, 3, 2, 9]
def baseStart_2099696 : Nat := 118140960795 + 2099696 * 2 ^ 59
def prefixEnd_2099696 : Nat := 4983230072969 + 3 ^ 40 * 2099696 * 2
def baseEnd_2099696 : Nat := 79863205653549789884717

theorem tailTrace_2099696 : CollatzResearch.WordTrace tailWord_2099696 prefixEnd_2099696 79863205653549789884717 := by
  unfold tailWord_2099696
  simp only [CollatzResearch.WordTrace]
  refine ⟨38291102300583733186171471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51054803067444977581561961 38291102300583733186171471)
  ·
    refine ⟨57436653450875599779257207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38291102300583733186171471 57436653450875599779257207)
    ·
      refine ⟨86154980176313399668885811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57436653450875599779257207 86154980176313399668885811)
      ·
        refine ⟨129232470264470099503328717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86154980176313399668885811 129232470264470099503328717)
        ·
          refine ⟨48462176349176287313748269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129232470264470099503328717 48462176349176287313748269)
          ·
            refine ⟨18173316130941107742655601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48462176349176287313748269 18173316130941107742655601)
            ·
              refine ⟨13629987098205830806991701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18173316130941107742655601 13629987098205830806991701)
              ·
                refine ⟨79863205653549789884717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13629987098205830806991701 79863205653549789884717)
                ·
                  rfl

theorem cell22_2099696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 9].length) (baseStart_2099696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099696 prefixEnd_2099696 := by exact prefixLift 2099696
  have htrace : WordTrace (prefixWord ++ tailWord_2099696) baseStart_2099696 baseEnd_2099696 := by
    simpa [prefixWord, tailWord_2099696, baseEnd_2099696] using wordTrace_append hprefix tailTrace_2099696
  have hstable : (prefixWord ++ tailWord_2099696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099696).length < 2 ^ (prefixWord ++ tailWord_2099696).sum := by decide
  have hdescent : baseEnd_2099696 < baseStart_2099696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099711 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 2, 7]
def baseStart_2099711 : Nat := 118140960795 + 2099711 * 2 ^ 59
def prefixEnd_2099711 : Nat := 4983230072969 + 3 ^ 40 * 2099711 * 2
def baseEnd_2099711 : Nat := 718773985688493069837407

theorem tailTrace_2099711 : CollatzResearch.WordTrace tailWord_2099711 prefixEnd_2099711 718773985688493069837407 := by
  unfold tailWord_2099711
  simp only [CollatzResearch.WordTrace]
  refine ⟨76582751696113123934138987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51055167797408749289425991 76582751696113123934138987)
  ·
    refine ⟨114874127544169685901208481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76582751696113123934138987 114874127544169685901208481)
    ·
      refine ⟨86155595658127264425906361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114874127544169685901208481 86155595658127264425906361)
      ·
        refine ⟨64616696743595448319429771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86155595658127264425906361 64616696743595448319429771)
        ·
          refine ⟨96925045115393172479144657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64616696743595448319429771 96925045115393172479144657)
          ·
            refine ⟨72693783836544879359358493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96925045115393172479144657 72693783836544879359358493)
            ·
              refine ⟨27260168938704329759759435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72693783836544879359358493 27260168938704329759759435)
              ·
                refine ⟨40890253408056494639639153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27260168938704329759759435 40890253408056494639639153)
                ·
                  refine ⟨30667690056042370979729365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40890253408056494639639153 30667690056042370979729365)
                  ·
                    refine ⟨718773985688493069837407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30667690056042370979729365 718773985688493069837407)
                    ·
                      rfl

theorem cell22_2099711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_2099711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099711 prefixEnd_2099711 := by exact prefixLift 2099711
  have htrace : WordTrace (prefixWord ++ tailWord_2099711) baseStart_2099711 baseEnd_2099711 := by
    simpa [prefixWord, tailWord_2099711, baseEnd_2099711] using wordTrace_append hprefix tailTrace_2099711
  have hstable : (prefixWord ++ tailWord_2099711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099711).length < 2 ^ (prefixWord ++ tailWord_2099711).sum := by decide
  have hdescent : baseEnd_2099711 < baseStart_2099711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099713 : List Nat := [1, 2, 4, 1, 3, 2, 1, 8]
def baseStart_2099713 : Nat := 118140960795 + 2099713 * 2 ^ 59
def prefixEnd_2099713 : Nat := 4983230072969 + 3 ^ 40 * 2099713 * 2
def baseEnd_2099713 : Nat := 79863852258818414587489

theorem tailTrace_2099713 : CollatzResearch.WordTrace tailWord_2099713 prefixEnd_2099713 79863852258818414587489 := by
  unfold tailWord_2099713
  simp only [CollatzResearch.WordTrace]
  refine ⟨76582824642105878275711793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51055216428070585517141195 76582824642105878275711793)
  ·
    refine ⟨57437118481579408706783845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76582824642105878275711793 57437118481579408706783845)
    ·
      refine ⟨10769459715296139132521971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57437118481579408706783845 10769459715296139132521971)
      ·
        refine ⟨16154189572944208698782957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10769459715296139132521971 16154189572944208698782957)
        ·
          refine ⟨6057821089854078262043609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16154189572944208698782957 6057821089854078262043609)
          ·
            refine ⟨4543365817390558696532707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6057821089854078262043609 4543365817390558696532707)
            ·
              refine ⟨6815048726085838044799061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4543365817390558696532707 6815048726085838044799061)
              ·
                refine ⟨79863852258818414587489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6815048726085838044799061 79863852258818414587489)
                ·
                  rfl

theorem cell22_2099713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 8].length) (baseStart_2099713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099713 prefixEnd_2099713 := by exact prefixLift 2099713
  have htrace : WordTrace (prefixWord ++ tailWord_2099713) baseStart_2099713 baseEnd_2099713 := by
    simpa [prefixWord, tailWord_2099713, baseEnd_2099713] using wordTrace_append hprefix tailTrace_2099713
  have hstable : (prefixWord ++ tailWord_2099713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099713).length < 2 ^ (prefixWord ++ tailWord_2099713).sum := by decide
  have hdescent : baseEnd_2099713 < baseStart_2099713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099719 : List Nat := [1, 1, 4, 3, 4, 1, 1, 3, 4]
def baseStart_2099719 : Nat := 118140960795 + 2099719 * 2 ^ 59
def prefixEnd_2099719 : Nat := 4983230072969 + 3 ^ 40 * 2099719 * 2
def baseEnd_2099719 : Nat := 239592241417327905212461

theorem tailTrace_2099719 : CollatzResearch.WordTrace tailWord_2099719 prefixEnd_2099719 239592241417327905212461 := by
  unfold tailWord_2099719
  simp only [CollatzResearch.WordTrace]
  refine ⟨76583043480084141300430211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51055362320056094200286807 76583043480084141300430211)
  ·
    refine ⟨114874565220126211950645317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76583043480084141300430211 114874565220126211950645317)
    ·
      refine ⟨21538980978773664740745997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114874565220126211950645317 21538980978773664740745997)
      ·
        refine ⟨8077117867040124277779749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21538980978773664740745997 8077117867040124277779749)
        ·
          refine ⟨1514459600070023302083703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8077117867040124277779749 1514459600070023302083703)
          ·
            refine ⟨2271689400105034953125555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514459600070023302083703 2271689400105034953125555)
            ·
              refine ⟨3407534100157552429688333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271689400105034953125555 3407534100157552429688333)
              ·
                refine ⟨1277825287559082161133125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3407534100157552429688333 1277825287559082161133125)
                ·
                  refine ⟨239592241417327905212461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1277825287559082161133125 239592241417327905212461)
                  ·
                    rfl

theorem cell22_2099719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 4].length) (baseStart_2099719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099719 prefixEnd_2099719 := by exact prefixLift 2099719
  have htrace : WordTrace (prefixWord ++ tailWord_2099719) baseStart_2099719 baseEnd_2099719 := by
    simpa [prefixWord, tailWord_2099719, baseEnd_2099719] using wordTrace_append hprefix tailTrace_2099719
  have hstable : (prefixWord ++ tailWord_2099719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099719).length < 2 ^ (prefixWord ++ tailWord_2099719).sum := by decide
  have hdescent : baseEnd_2099719 < baseStart_2099719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099732 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2099732 : Nat := 118140960795 + 2099732 * 2 ^ 59
def prefixEnd_2099732 : Nat := 4983230072969 + 3 ^ 40 * 2099732 * 2
def baseEnd_2099732 : Nat := 718781174417656015062343

theorem tailTrace_2099732 : CollatzResearch.WordTrace tailWord_2099732 prefixEnd_2099732 718781174417656015062343 := by
  unfold tailWord_2099732
  simp only [CollatzResearch.WordTrace]
  refine ⟨38291758814518522260326725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51055678419358029680435633 38291758814518522260326725)
  ·
    refine ⟨7179704777722222923811261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38291758814518522260326725 7179704777722222923811261)
    ·
      refine ⟨2692389291645833596429223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7179704777722222923811261 2692389291645833596429223)
      ·
        refine ⟨4038583937468750394643835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2692389291645833596429223 4038583937468750394643835)
        ·
          refine ⟨6057875906203125591965753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4038583937468750394643835 6057875906203125591965753)
          ·
            refine ⟨4543406929652344193974315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6057875906203125591965753 4543406929652344193974315)
            ·
              refine ⟨6815110394478516290961473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4543406929652344193974315 6815110394478516290961473)
              ·
                refine ⟨5111332795858887218221105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6815110394478516290961473 5111332795858887218221105)
                ·
                  refine ⟨3833499596894165413665829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5111332795858887218221105 3833499596894165413665829)
                  ·
                    refine ⟨718781174417656015062343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3833499596894165413665829 718781174417656015062343)
                    ·
                      rfl

theorem cell22_2099732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2099732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099732 prefixEnd_2099732 := by exact prefixLift 2099732
  have htrace : WordTrace (prefixWord ++ tailWord_2099732) baseStart_2099732 baseEnd_2099732 := by
    simpa [prefixWord, tailWord_2099732, baseEnd_2099732] using wordTrace_append hprefix tailTrace_2099732
  have hstable : (prefixWord ++ tailWord_2099732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099732).length < 2 ^ (prefixWord ++ tailWord_2099732).sum := by decide
  have hdescent : baseEnd_2099732 < baseStart_2099732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099796 : List Nat := [2, 4, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_2099796 : Nat := 118140960795 + 2099796 * 2 ^ 59
def prefixEnd_2099796 : Nat := 4983230072969 + 3 ^ 40 * 2099796 * 2
def baseEnd_2099796 : Nat := 718803082925581181462147

theorem tailTrace_2099796 : CollatzResearch.WordTrace tailWord_2099796 prefixEnd_2099796 718803082925581181462147 := by
  unfold tailWord_2099796
  simp only [CollatzResearch.WordTrace]
  refine ⟨38292925950402591725491621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51057234600536788967322161 38292925950402591725491621)
  ·
    refine ⟨7179923615700485948529679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38292925950402591725491621 7179923615700485948529679)
    ·
      refine ⟨10769885423550728922794519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7179923615700485948529679 10769885423550728922794519)
      ·
        refine ⟨16154828135326093384191779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10769885423550728922794519 16154828135326093384191779)
        ·
          refine ⟨24232242202989140076287669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16154828135326093384191779 24232242202989140076287669)
          ·
            refine ⟨2271772706530231882151969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24232242202989140076287669 2271772706530231882151969)
            ·
              refine ⟨1703829529897673911613977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2271772706530231882151969 1703829529897673911613977)
              ·
                refine ⟨1277872147423255433710483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1703829529897673911613977 1277872147423255433710483)
                ·
                  refine ⟨1916808221134883150565725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277872147423255433710483 1916808221134883150565725)
                  ·
                    refine ⟨718803082925581181462147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1916808221134883150565725 718803082925581181462147)
                    ·
                      rfl

theorem cell22_2099796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_2099796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099796 prefixEnd_2099796 := by exact prefixLift 2099796
  have htrace : WordTrace (prefixWord ++ tailWord_2099796) baseStart_2099796 baseEnd_2099796 := by
    simpa [prefixWord, tailWord_2099796, baseEnd_2099796] using wordTrace_append hprefix tailTrace_2099796
  have hstable : (prefixWord ++ tailWord_2099796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099796).length < 2 ^ (prefixWord ++ tailWord_2099796).sum := by decide
  have hdescent : baseEnd_2099796 < baseStart_2099796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099914 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 3, 3]
def baseStart_2099914 : Nat := 118140960795 + 2099914 * 2 ^ 59
def prefixEnd_2099914 : Nat := 4983230072969 + 3 ^ 40 * 2099914 * 2
def baseEnd_2099914 : Nat := 718843476737068207011785

theorem tailTrace_2099914 : CollatzResearch.WordTrace tailWord_2099914 prefixEnd_2099914 718843476737068207011785 := by
  unfold tailWord_2099914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19147538928594422400944699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51060103809585126402519197 19147538928594422400944699)
  ·
    refine ⟨28721308392891633601417049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19147538928594422400944699 28721308392891633601417049)
    ·
      refine ⟨21540981294668725201062787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28721308392891633601417049 21540981294668725201062787)
      ·
        refine ⟨32311471942003087801594181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21540981294668725201062787 32311471942003087801594181)
        ·
          refine ⟨6058400989125578962798909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32311471942003087801594181 6058400989125578962798909)
          ·
            refine ⟨2271900370922092111049591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6058400989125578962798909 2271900370922092111049591)
            ·
              refine ⟨3407850556383138166574387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271900370922092111049591 3407850556383138166574387)
              ·
                refine ⟨5111775834574707249861581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3407850556383138166574387 5111775834574707249861581)
                ·
                  refine ⟨1916915937965515218698093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5111775834574707249861581 1916915937965515218698093)
                  ·
                    refine ⟨718843476737068207011785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1916915937965515218698093 718843476737068207011785)
                    ·
                      rfl

theorem cell22_2099914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_2099914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099914 prefixEnd_2099914 := by exact prefixLift 2099914
  have htrace : WordTrace (prefixWord ++ tailWord_2099914) baseStart_2099914 baseEnd_2099914 := by
    simpa [prefixWord, tailWord_2099914, baseEnd_2099914] using wordTrace_append hprefix tailTrace_2099914
  have hstable : (prefixWord ++ tailWord_2099914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099914).length < 2 ^ (prefixWord ++ tailWord_2099914).sum := by decide
  have hdescent : baseEnd_2099914 < baseStart_2099914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099927 : List Nat := [1, 1, 3, 2, 1, 4, 4, 1, 5]
def baseStart_2099927 : Nat := 118140960795 + 2099927 * 2 ^ 59
def prefixEnd_2099927 : Nat := 4983230072969 + 3 ^ 40 * 2099927 * 2
def baseEnd_2099927 : Nat := 239615975634246835478915

theorem tailTrace_2099927 : CollatzResearch.WordTrace tailWord_2099927 prefixEnd_2099927 239615975634246835478915 := by
  unfold tailWord_2099927
  simp only [CollatzResearch.WordTrace]
  refine ⟨76590629863330592824002035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51060419908887061882668023 76590629863330592824002035)
  ·
    refine ⟨114885944794995889236003053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76590629863330592824002035 114885944794995889236003053)
    ·
      refine ⟨43082229298123458463501145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114885944794995889236003053 43082229298123458463501145)
      ·
        refine ⟨32311671973592593847625859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43082229298123458463501145 32311671973592593847625859)
        ·
          refine ⟨48467507960388890771438789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32311671973592593847625859 48467507960388890771438789)
          ·
            refine ⟨9087657742572917019644773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48467507960388890771438789 9087657742572917019644773)
            ·
              refine ⟨1703935826732421941183395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9087657742572917019644773 1703935826732421941183395)
              ·
                refine ⟨2555903740098632911775093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703935826732421941183395 2555903740098632911775093)
                ·
                  refine ⟨239615975634246835478915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2555903740098632911775093 239615975634246835478915)
                  ·
                    rfl

theorem cell22_2099927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 5].length) (baseStart_2099927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099927 prefixEnd_2099927 := by exact prefixLift 2099927
  have htrace : WordTrace (prefixWord ++ tailWord_2099927) baseStart_2099927 baseEnd_2099927 := by
    simpa [prefixWord, tailWord_2099927, baseEnd_2099927] using wordTrace_append hprefix tailTrace_2099927
  have hstable : (prefixWord ++ tailWord_2099927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099927).length < 2 ^ (prefixWord ++ tailWord_2099927).sum := by decide
  have hdescent : baseEnd_2099927 < baseStart_2099927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099985 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 4, 4]
def baseStart_2099985 : Nat := 118140960795 + 2099985 * 2 ^ 59
def prefixEnd_2099985 : Nat := 4983230072969 + 3 ^ 40 * 2099985 * 2
def baseEnd_2099985 : Nat := 718867781488047688486567

theorem tailTrace_2099985 : CollatzResearch.WordTrace tailWord_2099985 prefixEnd_2099985 718867781488047688486567 := by
  unfold tailWord_2099985
  simp only [CollatzResearch.WordTrace]
  refine ⟨76592745297120468729613409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51061830198080312486408939 76592745297120468729613409)
  ·
    refine ⟨57444558972840351547210057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76592745297120468729613409 57444558972840351547210057)
    ·
      refine ⟨43083419229630263660407543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57444558972840351547210057 43083419229630263660407543)
      ·
        refine ⟨64625128844445395490611315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43083419229630263660407543 64625128844445395490611315)
        ·
          refine ⟨96937693266668093235916973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64625128844445395490611315 96937693266668093235916973)
          ·
            refine ⟨36351634975000534963468865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96937693266668093235916973 36351634975000534963468865)
            ·
              refine ⟨27263726231250401222601649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36351634975000534963468865 27263726231250401222601649)
              ·
                refine ⟨20447794673437800916951237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27263726231250401222601649 20447794673437800916951237)
                ·
                  refine ⟨3833961501269587671928357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20447794673437800916951237 3833961501269587671928357)
                  ·
                    refine ⟨718867781488047688486567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3833961501269587671928357 718867781488047688486567)
                    ·
                      rfl

theorem cell22_2099985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_2099985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099985 prefixEnd_2099985 := by exact prefixLift 2099985
  have htrace : WordTrace (prefixWord ++ tailWord_2099985) baseStart_2099985 baseEnd_2099985 := by
    simpa [prefixWord, tailWord_2099985, baseEnd_2099985] using wordTrace_append hprefix tailTrace_2099985
  have hstable : (prefixWord ++ tailWord_2099985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099985).length < 2 ^ (prefixWord ++ tailWord_2099985).sum := by decide
  have hdescent : baseEnd_2099985 < baseStart_2099985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099987 : List Nat := [1, 1, 1, 2, 1, 3, 3, 5, 2, 3]
def baseStart_2099987 : Nat := 118140960795 + 2099987 * 2 ^ 59
def prefixEnd_2099987 : Nat := 4983230072969 + 3 ^ 40 * 2099987 * 2
def baseEnd_2099987 : Nat := 718868466128920349936561

theorem tailTrace_2099987 : CollatzResearch.WordTrace tailWord_2099987 prefixEnd_2099987 718868466128920349936561 := by
  unfold tailWord_2099987
  simp only [CollatzResearch.WordTrace]
  refine ⟨76592818243113223071186215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51061878828742148714124143 76592818243113223071186215)
  ·
    refine ⟨114889227364669834606779323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76592818243113223071186215 114889227364669834606779323)
    ·
      refine ⟨172333841047004751910168985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114889227364669834606779323 172333841047004751910168985)
      ·
        refine ⟨129250380785253563932626739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172333841047004751910168985 129250380785253563932626739)
        ·
          refine ⟨193875571177880345898940109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129250380785253563932626739 193875571177880345898940109)
          ·
            refine ⟨72703339191705129712102541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193875571177880345898940109 72703339191705129712102541)
            ·
              refine ⟨27263752196889423642038453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72703339191705129712102541 27263752196889423642038453)
              ·
                refine ⟨2555976768458383466441105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27263752196889423642038453 2555976768458383466441105)
                ·
                  refine ⟨1916982576343787599830829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2555976768458383466441105 1916982576343787599830829)
                  ·
                    refine ⟨718868466128920349936561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1916982576343787599830829 718868466128920349936561)
                    ·
                      rfl

theorem cell22_2099987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 3].length) (baseStart_2099987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2099987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2099987 prefixEnd_2099987 := by exact prefixLift 2099987
  have htrace : WordTrace (prefixWord ++ tailWord_2099987) baseStart_2099987 baseEnd_2099987 := by
    simpa [prefixWord, tailWord_2099987, baseEnd_2099987] using wordTrace_append hprefix tailTrace_2099987
  have hstable : (prefixWord ++ tailWord_2099987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099987).length < 2 ^ (prefixWord ++ tailWord_2099987).sum := by decide
  have hdescent : baseEnd_2099987 < baseStart_2099987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100002 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2100002 : Nat := 118140960795 + 2100002 * 2 ^ 59
def prefixEnd_2100002 : Nat := 4983230072969 + 3 ^ 40 * 2100002 * 2
def baseEnd_2100002 : Nat := 718873600935465310811515

theorem tailTrace_2100002 : CollatzResearch.WordTrace tailWord_2100002 prefixEnd_2100002 718873600935465310811515 := by
  unfold tailWord_2100002
  simp only [CollatzResearch.WordTrace]
  refine ⟨19148341334514720158245565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51062243558705920421988173 19148341334514720158245565)
  ·
    refine ⟨7180628000443020059342087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19148341334514720158245565 7180628000443020059342087)
    ·
      refine ⟨10770942000664530089013131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7180628000443020059342087 10770942000664530089013131)
      ·
        refine ⟨16156413000996795133519697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10770942000664530089013131 16156413000996795133519697)
        ·
          refine ⟨12117309750747596350139773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16156413000996795133519697 12117309750747596350139773)
          ·
            refine ⟨4543991156530348631302415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12117309750747596350139773 4543991156530348631302415)
            ·
              refine ⟨6815986734795522946953623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4543991156530348631302415 6815986734795522946953623)
              ·
                refine ⟨10223980102193284420430435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6815986734795522946953623 10223980102193284420430435)
                ·
                  refine ⟨15335970153289926630645653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10223980102193284420430435 15335970153289926630645653)
                  ·
                    refine ⟨718873600935465310811515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15335970153289926630645653 718873600935465310811515)
                    ·
                      rfl

theorem cell22_2100002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2100002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100002 prefixEnd_2100002 := by exact prefixLift 2100002
  have htrace : WordTrace (prefixWord ++ tailWord_2100002) baseStart_2100002 baseEnd_2100002 := by
    simpa [prefixWord, tailWord_2100002, baseEnd_2100002] using wordTrace_append hprefix tailTrace_2100002
  have hstable : (prefixWord ++ tailWord_2100002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100002).length < 2 ^ (prefixWord ++ tailWord_2100002).sum := by decide
  have hdescent : baseEnd_2100002 < baseStart_2100002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100021 : List Nat := [1, 3, 3, 1, 3, 3, 1, 2, 2, 3]
def baseStart_2100021 : Nat := 118140960795 + 2100021 * 2 ^ 59
def prefixEnd_2100021 : Nat := 4983230072969 + 3 ^ 40 * 2100021 * 2
def baseEnd_2100021 : Nat := 718880105023755594586457

theorem tailTrace_2100021 : CollatzResearch.WordTrace tailWord_2100021 prefixEnd_2100021 718880105023755594586457 := by
  unfold tailWord_2100021
  simp only [CollatzResearch.WordTrace]
  refine ⟨76594058324990046877923917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51062705549993364585282611 76594058324990046877923917)
  ·
    refine ⟨28722771871871267579221469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76594058324990046877923917 28722771871871267579221469)
    ·
      refine ⟨10771039451951725342208051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28722771871871267579221469 10771039451951725342208051)
      ·
        refine ⟨16156559177927588013312077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10771039451951725342208051 16156559177927588013312077)
        ·
          refine ⟨6058709691722845504992029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16156559177927588013312077 6058709691722845504992029)
          ·
            refine ⟨2272016134396067064372011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6058709691722845504992029 2272016134396067064372011)
            ·
              refine ⟨3408024201594100596558017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272016134396067064372011 3408024201594100596558017)
              ·
                refine ⟨2556018151195575447418513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3408024201594100596558017 2556018151195575447418513)
                ·
                  refine ⟨1917013613396681585563885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2556018151195575447418513 1917013613396681585563885)
                  ·
                    refine ⟨718880105023755594586457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917013613396681585563885 718880105023755594586457)
                    ·
                      rfl

theorem cell22_2100021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_2100021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100021 prefixEnd_2100021 := by exact prefixLift 2100021
  have htrace : WordTrace (prefixWord ++ tailWord_2100021) baseStart_2100021 baseEnd_2100021 := by
    simpa [prefixWord, tailWord_2100021, baseEnd_2100021] using wordTrace_append hprefix tailTrace_2100021
  have hstable : (prefixWord ++ tailWord_2100021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100021).length < 2 ^ (prefixWord ++ tailWord_2100021).sum := by decide
  have hdescent : baseEnd_2100021 < baseStart_2100021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100038 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_2100038 : Nat := 118140960795 + 2100038 * 2 ^ 59
def prefixEnd_2100038 : Nat := 4983230072969 + 3 ^ 40 * 2100038 * 2
def baseEnd_2100038 : Nat := 718885924471173216911405

theorem tailTrace_2100038 : CollatzResearch.WordTrace tailWord_2100038 prefixEnd_2100038 718885924471173216911405 := by
  unfold tailWord_2100038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393583698935264336915399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51063118910618972520861845 2393583698935264336915399)
  ·
    refine ⟨3590375548402896505373099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2393583698935264336915399 3590375548402896505373099)
    ·
      refine ⟨5385563322604344758059649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3590375548402896505373099 5385563322604344758059649)
      ·
        refine ⟨4039172491953258568544737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5385563322604344758059649 4039172491953258568544737)
        ·
          refine ⟨3029379368964943926408553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4039172491953258568544737 3029379368964943926408553)
          ·
            refine ⟨2272034526723707944806415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3029379368964943926408553 2272034526723707944806415)
            ·
              refine ⟨3408051790085561917209623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272034526723707944806415 3408051790085561917209623)
              ·
                refine ⟨5112077685128342875814435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3408051790085561917209623 5112077685128342875814435)
                ·
                  refine ⟨7668116527692514313721653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5112077685128342875814435 7668116527692514313721653)
                  ·
                    refine ⟨718885924471173216911405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7668116527692514313721653 718885924471173216911405)
                    ·
                      rfl

theorem cell22_2100038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_2100038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100038 prefixEnd_2100038 := by exact prefixLift 2100038
  have htrace : WordTrace (prefixWord ++ tailWord_2100038) baseStart_2100038 baseEnd_2100038 := by
    simpa [prefixWord, tailWord_2100038, baseEnd_2100038] using wordTrace_append hprefix tailTrace_2100038
  have hstable : (prefixWord ++ tailWord_2100038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100038).length < 2 ^ (prefixWord ++ tailWord_2100038).sum := by decide
  have hdescent : baseEnd_2100038 < baseStart_2100038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100137 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 2, 4]
def baseStart_2100137 : Nat := 118140960795 + 2100137 * 2 ^ 59
def prefixEnd_2100137 : Nat := 4983230072969 + 3 ^ 40 * 2100137 * 2
def baseEnd_2100137 : Nat := 718919814194369958686101

theorem tailTrace_2100137 : CollatzResearch.WordTrace tailWord_2100137 prefixEnd_2100137 718919814194369958686101 := by
  unfold tailWord_2100137
  simp only [CollatzResearch.WordTrace]
  refine ⟨76598289192569798689146665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51065526128379865792764443 76598289192569798689146665)
  ·
    refine ⟨57448716894427349016859999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76598289192569798689146665 57448716894427349016859999)
    ·
      refine ⟨86173075341641023525289999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57448716894427349016859999 86173075341641023525289999)
      ·
        refine ⟨129259613012461535287934999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86173075341641023525289999 129259613012461535287934999)
        ·
          refine ⟨193889419518692302931902499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129259613012461535287934999 193889419518692302931902499)
          ·
            refine ⟨290834129278038454397853749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193889419518692302931902499 290834129278038454397853749)
            ·
              refine ⟨27265699619816105099798789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290834129278038454397853749 27265699619816105099798789)
              ·
                refine ⟨5112318678715519706212273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27265699619816105099798789 5112318678715519706212273)
                ·
                  refine ⟨3834239009036639779659205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5112318678715519706212273 3834239009036639779659205)
                  ·
                    refine ⟨718919814194369958686101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3834239009036639779659205 718919814194369958686101)
                    ·
                      rfl

theorem cell22_2100137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_2100137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100137 prefixEnd_2100137 := by exact prefixLift 2100137
  have htrace : WordTrace (prefixWord ++ tailWord_2100137) baseStart_2100137 baseEnd_2100137 := by
    simpa [prefixWord, tailWord_2100137, baseEnd_2100137] using wordTrace_append hprefix tailTrace_2100137
  have hstable : (prefixWord ++ tailWord_2100137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100137).length < 2 ^ (prefixWord ++ tailWord_2100137).sum := by decide
  have hdescent : baseEnd_2100137 < baseStart_2100137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100152 : List Nat := [2, 1, 2, 1, 2, 4, 3, 7]
def baseStart_2100152 : Nat := 118140960795 + 2100152 * 2 ^ 59
def prefixEnd_2100152 : Nat := 4983230072969 + 3 ^ 40 * 2100152 * 2
def baseEnd_2100152 : Nat := 79880549888990546617895

theorem tailTrace_2100152 : CollatzResearch.WordTrace tailWord_2100152 prefixEnd_2100152 79880549888990546617895 := by
  unfold tailWord_2100152
  simp only [CollatzResearch.WordTrace]
  refine ⟨38299418143757728125471355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51065890858343637500628473 38299418143757728125471355)
  ·
    refine ⟨57449127215636592188207033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38299418143757728125471355 57449127215636592188207033)
    ·
      refine ⟨43086845411727444141155275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57449127215636592188207033 43086845411727444141155275)
      ·
        refine ⟨64630268117591166211732913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43086845411727444141155275 64630268117591166211732913)
        ·
          refine ⟨48472701088193374658799685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64630268117591166211732913 48472701088193374658799685)
          ·
            refine ⟨9088631454036257748524941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48472701088193374658799685 9088631454036257748524941)
            ·
              refine ⟨3408236795263596655696853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9088631454036257748524941 3408236795263596655696853)
              ·
                refine ⟨79880549888990546617895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3408236795263596655696853 79880549888990546617895)
                ·
                  rfl

theorem cell22_2100152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 7].length) (baseStart_2100152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100152 prefixEnd_2100152 := by exact prefixLift 2100152
  have htrace : WordTrace (prefixWord ++ tailWord_2100152) baseStart_2100152 baseEnd_2100152 := by
    simpa [prefixWord, tailWord_2100152, baseEnd_2100152] using wordTrace_append hprefix tailTrace_2100152
  have hstable : (prefixWord ++ tailWord_2100152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100152).length < 2 ^ (prefixWord ++ tailWord_2100152).sum := by decide
  have hdescent : baseEnd_2100152 < baseStart_2100152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100259 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 6]
def baseStart_2100259 : Nat := 118140960795 + 2100259 * 2 ^ 59
def prefixEnd_2100259 : Nat := 4983230072969 + 3 ^ 40 * 2100259 * 2
def baseEnd_2100259 : Nat := 239653859095867435711909

theorem tailTrace_2100259 : CollatzResearch.WordTrace tailWord_2100259 prefixEnd_2100259 239653859095867435711909 := by
  unfold tailWord_2100259
  simp only [CollatzResearch.WordTrace]
  refine ⟨76602738898127813525087831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51068492598751875683391887 76602738898127813525087831)
  ·
    refine ⟨114904108347191720287631747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76602738898127813525087831 114904108347191720287631747)
    ·
      refine ⟨172356162520787580431447621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114904108347191720287631747 172356162520787580431447621)
      ·
        refine ⟨32316780472647671330896429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172356162520787580431447621 32316780472647671330896429)
        ·
          refine ⟨12118792677242876749086161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32316780472647671330896429 12118792677242876749086161)
          ·
            refine ⟨9089094507932157561814621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12118792677242876749086161 9089094507932157561814621)
            ·
              refine ⟨3408410440474559085680483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9089094507932157561814621 3408410440474559085680483)
              ·
                refine ⟨5112615660711838628520725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3408410440474559085680483 5112615660711838628520725)
                ·
                  refine ⟨239653859095867435711909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5112615660711838628520725 239653859095867435711909)
                  ·
                    rfl

theorem cell22_2100259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 6].length) (baseStart_2100259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100259 prefixEnd_2100259 := by exact prefixLift 2100259
  have htrace : WordTrace (prefixWord ++ tailWord_2100259) baseStart_2100259 baseEnd_2100259 := by
    simpa [prefixWord, tailWord_2100259, baseEnd_2100259] using wordTrace_append hprefix tailTrace_2100259
  have hstable : (prefixWord ++ tailWord_2100259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100259).length < 2 ^ (prefixWord ++ tailWord_2100259).sum := by decide
  have hdescent : baseEnd_2100259 < baseStart_2100259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100274 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_2100274 : Nat := 118140960795 + 2100274 * 2 ^ 59
def prefixEnd_2100274 : Nat := 4983230072969 + 3 ^ 40 * 2100274 * 2
def baseEnd_2100274 : Nat := 718966712094147268010681

theorem tailTrace_2100274 : CollatzResearch.WordTrace tailWord_2100274 prefixEnd_2100274 718966712094147268010681 := by
  unfold tailWord_2100274
  simp only [CollatzResearch.WordTrace]
  refine ⟨19150821498268367771720969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51068857328715647391255917 19150821498268367771720969)
  ·
    refine ⟨14363116123701275828790727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19150821498268367771720969 14363116123701275828790727)
    ·
      refine ⟨21544674185551913743186091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14363116123701275828790727 21544674185551913743186091)
      ·
        refine ⟨32317011278327870614779137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21544674185551913743186091 32317011278327870614779137)
        ·
          refine ⟨24237758458745902961084353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32317011278327870614779137 24237758458745902961084353)
          ·
            refine ⟨18178318844059427220813265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24237758458745902961084353 18178318844059427220813265)
            ·
              refine ⟨13633739133044570415609949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18178318844059427220813265 13633739133044570415609949)
              ·
                refine ⟨5112652174891713905853731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13633739133044570415609949 5112652174891713905853731)
                ·
                  refine ⟨7668978262337570858780597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5112652174891713905853731 7668978262337570858780597)
                  ·
                    refine ⟨718966712094147268010681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7668978262337570858780597 718966712094147268010681)
                    ·
                      rfl

theorem cell22_2100274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_2100274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100274 prefixEnd_2100274 := by exact prefixLift 2100274
  have htrace : WordTrace (prefixWord ++ tailWord_2100274) baseStart_2100274 baseEnd_2100274 := by
    simpa [prefixWord, tailWord_2100274, baseEnd_2100274] using wordTrace_append hprefix tailTrace_2100274
  have hstable : (prefixWord ++ tailWord_2100274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100274).length < 2 ^ (prefixWord ++ tailWord_2100274).sum := by decide
  have hdescent : baseEnd_2100274 < baseStart_2100274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100278 : List Nat := [5, 1, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_2100278 : Nat := 118140960795 + 2100278 * 2 ^ 59
def prefixEnd_2100278 : Nat := 4983230072969 + 3 ^ 40 * 2100278 * 2
def baseEnd_2100278 : Nat := 718968081375892590910669

theorem tailTrace_2100278 : CollatzResearch.WordTrace tailWord_2100278 prefixEnd_2100278 718968081375892590910669 := by
  unfold tailWord_2100278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4787714492816186235626843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51068954590039319846686325 4787714492816186235626843)
  ·
    refine ⟨7181571739224279353440265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4787714492816186235626843 7181571739224279353440265)
    ·
      refine ⟨5386178804418209515080199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7181571739224279353440265 5386178804418209515080199)
      ·
        refine ⟨8079268206627314272620299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5386178804418209515080199 8079268206627314272620299)
        ·
          refine ⟨12118902309940971408930449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8079268206627314272620299 12118902309940971408930449)
          ·
            refine ⟨9089176732455728556697837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12118902309940971408930449 9089176732455728556697837)
            ·
              refine ⟨3408441274670898208761689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9089176732455728556697837 3408441274670898208761689)
              ·
                refine ⟨2556330956003173656571267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3408441274670898208761689 2556330956003173656571267)
                ·
                  refine ⟨3834496434004760484856901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2556330956003173656571267 3834496434004760484856901)
                  ·
                    refine ⟨718968081375892590910669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3834496434004760484856901 718968081375892590910669)
                    ·
                      rfl

theorem cell22_2100278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_2100278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100278 prefixEnd_2100278 := by exact prefixLift 2100278
  have htrace : WordTrace (prefixWord ++ tailWord_2100278) baseStart_2100278 baseEnd_2100278 := by
    simpa [prefixWord, tailWord_2100278, baseEnd_2100278] using wordTrace_append hprefix tailTrace_2100278
  have hstable : (prefixWord ++ tailWord_2100278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100278).length < 2 ^ (prefixWord ++ tailWord_2100278).sum := by decide
  have hdescent : baseEnd_2100278 < baseStart_2100278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100306 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_2100306 : Nat := 118140960795 + 2100306 * 2 ^ 59
def prefixEnd_2100306 : Nat := 4983230072969 + 3 ^ 40 * 2100306 * 2
def baseEnd_2100306 : Nat := 718977666348109851210583

theorem tailTrace_2100306 : CollatzResearch.WordTrace tailWord_2100306 prefixEnd_2100306 718977666348109851210583 := by
  unfold tailWord_2100306
  simp only [CollatzResearch.WordTrace]
  refine ⟨19151113282239385138012193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51069635419305027034699181 19151113282239385138012193)
  ·
    refine ⟨14363334961679538853509145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19151113282239385138012193 14363334961679538853509145)
    ·
      refine ⟨10772501221259654140131859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14363334961679538853509145 10772501221259654140131859)
      ·
        refine ⟨16158751831889481210197789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10772501221259654140131859 16158751831889481210197789)
        ·
          refine ⟨6059531936958555453824171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16158751831889481210197789 6059531936958555453824171)
          ·
            refine ⟨9089297905437833180736257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6059531936958555453824171 9089297905437833180736257)
            ·
              refine ⟨6816973429078374885552193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9089297905437833180736257 6816973429078374885552193)
              ·
                refine ⟨5112730071808781164164145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6816973429078374885552193 5112730071808781164164145)
                ·
                  refine ⟨3834547553856585873123109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5112730071808781164164145 3834547553856585873123109)
                  ·
                    refine ⟨718977666348109851210583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3834547553856585873123109 718977666348109851210583)
                    ·
                      rfl

theorem cell22_2100306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_2100306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100306 prefixEnd_2100306 := by exact prefixLift 2100306
  have htrace : WordTrace (prefixWord ++ tailWord_2100306) baseStart_2100306 baseEnd_2100306 := by
    simpa [prefixWord, tailWord_2100306, baseEnd_2100306] using wordTrace_append hprefix tailTrace_2100306
  have hstable : (prefixWord ++ tailWord_2100306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100306).length < 2 ^ (prefixWord ++ tailWord_2100306).sum := by decide
  have hdescent : baseEnd_2100306 < baseStart_2100306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100336 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 3, 3]
def baseStart_2100336 : Nat := 118140960795 + 2100336 * 2 ^ 59
def prefixEnd_2100336 : Nat := 4983230072969 + 3 ^ 40 * 2100336 * 2
def baseEnd_2100336 : Nat := 718987935961199772960491

theorem tailTrace_2100336 : CollatzResearch.WordTrace tailWord_2100336 prefixEnd_2100336 718987935961199772960491 := by
  unfold tailWord_2100336
  simp only [CollatzResearch.WordTrace]
  refine ⟨38302773659424427837820431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51070364879232570450427241 38302773659424427837820431)
  ·
    refine ⟨57454160489136641756730647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38302773659424427837820431 57454160489136641756730647)
    ·
      refine ⟨86181240733704962635095971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57454160489136641756730647 86181240733704962635095971)
      ·
        refine ⟨129271861100557443952643957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86181240733704962635095971 129271861100557443952643957)
        ·
          refine ⟨12119236978177260370560371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129271861100557443952643957 12119236978177260370560371)
          ·
            refine ⟨18178855467265890555840557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12119236978177260370560371 18178855467265890555840557)
            ·
              refine ⟨6817070800224708958440209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18178855467265890555840557 6817070800224708958440209)
              ·
                refine ⟨5112803100168531718830157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6817070800224708958440209 5112803100168531718830157)
                ·
                  refine ⟨1917301162563199394561309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5112803100168531718830157 1917301162563199394561309)
                  ·
                    refine ⟨718987935961199772960491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917301162563199394561309 718987935961199772960491)
                    ·
                      rfl

theorem cell22_2100336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 3, 3].length) (baseStart_2100336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100336 prefixEnd_2100336 := by exact prefixLift 2100336
  have htrace : WordTrace (prefixWord ++ tailWord_2100336) baseStart_2100336 baseEnd_2100336 := by
    simpa [prefixWord, tailWord_2100336, baseEnd_2100336] using wordTrace_append hprefix tailTrace_2100336
  have hstable : (prefixWord ++ tailWord_2100336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100336).length < 2 ^ (prefixWord ++ tailWord_2100336).sum := by decide
  have hdescent : baseEnd_2100336 < baseStart_2100336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100349 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 7]
def baseStart_2100349 : Nat := 118140960795 + 2100349 * 2 ^ 59
def prefixEnd_2100349 : Nat := 4983230072969 + 3 ^ 40 * 2100349 * 2
def baseEnd_2100349 : Nat := 239664128708957357461817

theorem tailTrace_2100349 : CollatzResearch.WordTrace tailWord_2100349 prefixEnd_2100349 239664128708957357461817 := by
  unfold tailWord_2100349
  simp only [CollatzResearch.WordTrace]
  refine ⟨76606021467801758895864101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51070680978534505930576067 76606021467801758895864101)
  ·
    refine ⟨14363629025212829792974519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76606021467801758895864101 14363629025212829792974519)
    ·
      refine ⟨21545443537819244689461779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14363629025212829792974519 21545443537819244689461779)
      ·
        refine ⟨32318165306728867034192669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21545443537819244689461779 32318165306728867034192669)
        ·
          refine ⟨12119311990023325137822251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32318165306728867034192669 12119311990023325137822251)
          ·
            refine ⟨18178967985034987706733377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12119311990023325137822251 18178967985034987706733377)
            ·
              refine ⟨13634225988776240780050033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18178967985034987706733377 13634225988776240780050033)
              ·
                refine ⟨10225669491582180585037525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13634225988776240780050033 10225669491582180585037525)
                ·
                  refine ⟨239664128708957357461817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10225669491582180585037525 239664128708957357461817)
                  ·
                    rfl

theorem cell22_2100349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_2100349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100349 prefixEnd_2100349 := by exact prefixLift 2100349
  have htrace : WordTrace (prefixWord ++ tailWord_2100349) baseStart_2100349 baseEnd_2100349 := by
    simpa [prefixWord, tailWord_2100349, baseEnd_2100349] using wordTrace_append hprefix tailTrace_2100349
  have hstable : (prefixWord ++ tailWord_2100349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100349).length < 2 ^ (prefixWord ++ tailWord_2100349).sum := by decide
  have hdescent : baseEnd_2100349 < baseStart_2100349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100366 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_2100366 : Nat := 118140960795 + 2100366 * 2 ^ 59
def prefixEnd_2100366 : Nat := 4983230072969 + 3 ^ 40 * 2100366 * 2
def baseEnd_2100366 : Nat := 239666068524763231570133

theorem tailTrace_2100366 : CollatzResearch.WordTrace tailWord_2100366 prefixEnd_2100366 239666068524763231570133 := by
  unfold tailWord_2100366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9575830188592521349904119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51071094339160113866155301 9575830188592521349904119)
  ·
    refine ⟨14363745282888782024856179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9575830188592521349904119 14363745282888782024856179)
    ·
      refine ⟨21545617924333173037284269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14363745282888782024856179 21545617924333173037284269)
      ·
        refine ⟨8079606721624939888981601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21545617924333173037284269 8079606721624939888981601)
        ·
          refine ⟨6059705041218704916736201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8079606721624939888981601 6059705041218704916736201)
          ·
            refine ⟨4544778780914028687552151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6059705041218704916736201 4544778780914028687552151)
            ·
              refine ⟨6817168171371043031328227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4544778780914028687552151 6817168171371043031328227)
              ·
                refine ⟨10225752257056564546992341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6817168171371043031328227 10225752257056564546992341)
                ·
                  refine ⟨239666068524763231570133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10225752257056564546992341 239666068524763231570133)
                  ·
                    rfl

theorem cell22_2100366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_2100366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100366 prefixEnd_2100366 := by exact prefixLift 2100366
  have htrace : WordTrace (prefixWord ++ tailWord_2100366) baseStart_2100366 baseEnd_2100366 := by
    simpa [prefixWord, tailWord_2100366, baseEnd_2100366] using wordTrace_append hprefix tailTrace_2100366
  have hstable : (prefixWord ++ tailWord_2100366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100366).length < 2 ^ (prefixWord ++ tailWord_2100366).sum := by decide
  have hdescent : baseEnd_2100366 < baseStart_2100366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100370 : List Nat := [3, 2, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2100370 : Nat := 118140960795 + 2100370 * 2 ^ 59
def prefixEnd_2100370 : Nat := 4983230072969 + 3 ^ 40 * 2100370 * 2
def baseEnd_2100370 : Nat := 718999574856035017610387

theorem tailTrace_2100370 : CollatzResearch.WordTrace tailWord_2100370 prefixEnd_2100370 718999574856035017610387 := by
  unfold tailWord_2100370
  simp only [CollatzResearch.WordTrace]
  refine ⟨19151696850181419870594641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51071191600483786321585709 19151696850181419870594641)
  ·
    refine ⟨14363772637636064902945981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19151696850181419870594641 14363772637636064902945981)
    ·
      refine ⟨5386414739113524338604743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14363772637636064902945981 5386414739113524338604743)
      ·
        refine ⟨8079622108670286507907115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5386414739113524338604743 8079622108670286507907115)
        ·
          refine ⟨12119433163005429761860673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8079622108670286507907115 12119433163005429761860673)
          ·
            refine ⟨9089574872254072321395505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12119433163005429761860673 9089574872254072321395505)
            ·
              refine ⟨6817181154190554241046629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9089574872254072321395505 6817181154190554241046629)
              ·
                refine ⟨1278221466410728920196243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6817181154190554241046629 1278221466410728920196243)
                ·
                  refine ⟨1917332199616093380294365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1278221466410728920196243 1917332199616093380294365)
                  ·
                    refine ⟨718999574856035017610387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917332199616093380294365 718999574856035017610387)
                    ·
                      rfl

theorem cell22_2100370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2100370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100370 prefixEnd_2100370 := by exact prefixLift 2100370
  have htrace : WordTrace (prefixWord ++ tailWord_2100370) baseStart_2100370 baseEnd_2100370 := by
    simpa [prefixWord, tailWord_2100370, baseEnd_2100370] using wordTrace_append hprefix tailTrace_2100370
  have hstable : (prefixWord ++ tailWord_2100370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100370).length < 2 ^ (prefixWord ++ tailWord_2100370).sum := by decide
  have hdescent : baseEnd_2100370 < baseStart_2100370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100411 : List Nat := [1, 1, 1, 1, 1, 2, 4, 7, 4]
def baseStart_2100411 : Nat := 118140960795 + 2100411 * 2 ^ 59
def prefixEnd_2100411 : Nat := 4983230072969 + 3 ^ 40 * 2100411 * 2
def baseEnd_2100411 : Nat := 239671203331308192445087

theorem tailTrace_2100411 : CollatzResearch.WordTrace tailWord_2100411 prefixEnd_2100411 239671203331308192445087 := by
  unfold tailWord_2100411
  simp only [CollatzResearch.WordTrace]
  refine ⟨76608282793577143484621087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51072188529051428989747391 76608282793577143484621087)
  ·
    refine ⟨114912424190365715226931631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76608282793577143484621087 114912424190365715226931631)
    ·
      refine ⟨172368636285548572840397447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114912424190365715226931631 172368636285548572840397447)
      ·
        refine ⟨258552954428322859260596171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172368636285548572840397447 258552954428322859260596171)
        ·
          refine ⟨387829431642484288890894257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258552954428322859260596171 387829431642484288890894257)
          ·
            refine ⟨290872073731863216668170693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387829431642484288890894257 290872073731863216668170693)
            ·
              refine ⟨54538513824724353125282005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 290872073731863216668170693 54538513824724353125282005)
              ·
                refine ⟨1278246417766977026373797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54538513824724353125282005 1278246417766977026373797)
                ·
                  refine ⟨239671203331308192445087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278246417766977026373797 239671203331308192445087)
                  ·
                    rfl

theorem cell22_2100411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 4].length) (baseStart_2100411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100411 prefixEnd_2100411 := by exact prefixLift 2100411
  have htrace : WordTrace (prefixWord ++ tailWord_2100411) baseStart_2100411 baseEnd_2100411 := by
    simpa [prefixWord, tailWord_2100411, baseEnd_2100411] using wordTrace_append hprefix tailTrace_2100411
  have hstable : (prefixWord ++ tailWord_2100411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100411).length < 2 ^ (prefixWord ++ tailWord_2100411).sum := by decide
  have hdescent : baseEnd_2100411 < baseStart_2100411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100439 : List Nat := [1, 1, 3, 2, 1, 2, 3, 9]
def baseStart_2100439 : Nat := 118140960795 + 2100439 * 2 ^ 59
def prefixEnd_2100439 : Nat := 4983230072969 + 3 ^ 40 * 2100439 * 2
def baseEnd_2100439 : Nat := 79891466107349093070575

theorem tailTrace_2100439 : CollatzResearch.WordTrace tailWord_2100439 prefixEnd_2100439 79891466107349093070575 := by
  unfold tailWord_2100439
  simp only [CollatzResearch.WordTrace]
  refine ⟨76609304037475704266640371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51072869358317136177760247 76609304037475704266640371)
  ·
    refine ⟨114913956056213556399960557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76609304037475704266640371 114913956056213556399960557)
    ·
      refine ⟨43092733521080083649985209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114913956056213556399960557 43092733521080083649985209)
      ·
        refine ⟨32319550140810062737488907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43092733521080083649985209 32319550140810062737488907)
        ·
          refine ⟨48479325211215094106233361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32319550140810062737488907 48479325211215094106233361)
          ·
            refine ⟨36359493908411320579675021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48479325211215094106233361 36359493908411320579675021)
            ·
              refine ⟨13634810215654245217378133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36359493908411320579675021 13634810215654245217378133)
              ·
                refine ⟨79891466107349093070575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13634810215654245217378133 79891466107349093070575)
                ·
                  rfl

theorem cell22_2100439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 9].length) (baseStart_2100439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100439 prefixEnd_2100439 := by exact prefixLift 2100439
  have htrace : WordTrace (prefixWord ++ tailWord_2100439) baseStart_2100439 baseEnd_2100439 := by
    simpa [prefixWord, tailWord_2100439, baseEnd_2100439] using wordTrace_append hprefix tailTrace_2100439
  have hstable : (prefixWord ++ tailWord_2100439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100439).length < 2 ^ (prefixWord ++ tailWord_2100439).sum := by decide
  have hdescent : baseEnd_2100439 < baseStart_2100439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100458 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_2100458 : Nat := 118140960795 + 2100458 * 2 ^ 59
def prefixEnd_2100458 : Nat := 4983230072969 + 3 ^ 40 * 2100458 * 2
def baseEnd_2100458 : Nat := 719029699054432121410117

theorem tailTrace_2100458 : CollatzResearch.WordTrace tailWord_2100458 prefixEnd_2100458 719029699054432121410117 := by
  unfold tailWord_2100458
  simp only [CollatzResearch.WordTrace]
  refine ⟨19152499256101717627895507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51073331349604580341054685 19152499256101717627895507)
  ·
    refine ⟨28728748884152576441843261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19152499256101717627895507 28728748884152576441843261)
    ·
      refine ⟨10773280831557216165691223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28728748884152576441843261 10773280831557216165691223)
      ·
        refine ⟨16159921247335824248536835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10773280831557216165691223 16159921247335824248536835)
        ·
          refine ⟨24239881871003736372805253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16159921247335824248536835 24239881871003736372805253)
          ·
            refine ⟨4544977850813200569900985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24239881871003736372805253 4544977850813200569900985)
            ·
              refine ⟨3408733388109900427425739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4544977850813200569900985 3408733388109900427425739)
              ·
                refine ⟨5113100082164850641138609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3408733388109900427425739 5113100082164850641138609)
                ·
                  refine ⟨3834825061623637980853957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5113100082164850641138609 3834825061623637980853957)
                  ·
                    refine ⟨719029699054432121410117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3834825061623637980853957 719029699054432121410117)
                    ·
                      rfl

theorem cell22_2100458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_2100458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100458 prefixEnd_2100458 := by exact prefixLift 2100458
  have htrace : WordTrace (prefixWord ++ tailWord_2100458) baseStart_2100458 baseEnd_2100458 := by
    simpa [prefixWord, tailWord_2100458, baseEnd_2100458] using wordTrace_append hprefix tailTrace_2100458
  have hstable : (prefixWord ++ tailWord_2100458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100458).length < 2 ^ (prefixWord ++ tailWord_2100458).sum := by decide
  have hdescent : baseEnd_2100458 < baseStart_2100458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100471 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 5, 3]
def baseStart_2100471 : Nat := 118140960795 + 2100471 * 2 ^ 59
def prefixEnd_2100471 : Nat := 4983230072969 + 3 ^ 40 * 2100471 * 2
def baseEnd_2100471 : Nat := 719034149220104420835077

theorem tailTrace_2100471 : CollatzResearch.WordTrace tailWord_2100471 prefixEnd_2100471 719034149220104420835077 := by
  unfold tailWord_2100471
  simp only [CollatzResearch.WordTrace]
  refine ⟨76610471173359773731805267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51073647448906515821203511 76610471173359773731805267)
  ·
    refine ⟨114915706760039660597707901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76610471173359773731805267 114915706760039660597707901)
    ·
      refine ⟨43093390035014872724140463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114915706760039660597707901 43093390035014872724140463)
      ·
        refine ⟨64640085052522309086210695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43093390035014872724140463 64640085052522309086210695)
        ·
          refine ⟨96960127578783463629316043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64640085052522309086210695 96960127578783463629316043)
          ·
            refine ⟨145440191368175195443974065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96960127578783463629316043 145440191368175195443974065)
            ·
              refine ⟨109080143526131396582980549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145440191368175195443974065 109080143526131396582980549)
              ·
                refine ⟨20452526911149636859308853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109080143526131396582980549 20452526911149636859308853)
                ·
                  refine ⟨1917424397920278455560205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20452526911149636859308853 1917424397920278455560205)
                  ·
                    refine ⟨719034149220104420835077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917424397920278455560205 719034149220104420835077)
                    ·
                      rfl

theorem cell22_2100471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_2100471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100471 prefixEnd_2100471 := by exact prefixLift 2100471
  have htrace : WordTrace (prefixWord ++ tailWord_2100471) baseStart_2100471 baseEnd_2100471 := by
    simpa [prefixWord, tailWord_2100471, baseEnd_2100471] using wordTrace_append hprefix tailTrace_2100471
  have hstable : (prefixWord ++ tailWord_2100471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100471).length < 2 ^ (prefixWord ++ tailWord_2100471).sum := by decide
  have hdescent : baseEnd_2100471 < baseStart_2100471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100516 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_2100516 : Nat := 118140960795 + 2100516 * 2 ^ 59
def prefixEnd_2100516 : Nat := 4983230072969 + 3 ^ 40 * 2100516 * 2
def baseEnd_2100516 : Nat := 719049553639739303459939

theorem tailTrace_2100516 : CollatzResearch.WordTrace tailWord_2100516 prefixEnd_2100516 719049553639739303459939 := by
  unfold tailWord_2100516
  simp only [CollatzResearch.WordTrace]
  refine ⟨38306056229098373208596701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51074741638797830944795601 38306056229098373208596701)
  ·
    refine ⟨14364771085911889953223763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38306056229098373208596701 14364771085911889953223763)
    ·
      refine ⟨21547156628867834929835645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14364771085911889953223763 21547156628867834929835645)
      ·
        refine ⟨8080183735825438098688367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21547156628867834929835645 8080183735825438098688367)
        ·
          refine ⟨12120275603738157148032551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8080183735825438098688367 12120275603738157148032551)
          ·
            refine ⟨18180413405607235722048827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12120275603738157148032551 18180413405607235722048827)
            ·
              refine ⟨27270620108410853583073241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18180413405607235722048827 27270620108410853583073241)
              ·
                refine ⟨20452965081308140187304931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27270620108410853583073241 20452965081308140187304931)
                ·
                  refine ⟨30679447621962210280957397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20452965081308140187304931 30679447621962210280957397)
                  ·
                    refine ⟨719049553639739303459939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30679447621962210280957397 719049553639739303459939)
                    ·
                      rfl

theorem cell22_2100516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_2100516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100516 prefixEnd_2100516 := by exact prefixLift 2100516
  have htrace : WordTrace (prefixWord ++ tailWord_2100516) baseStart_2100516 baseEnd_2100516 := by
    simpa [prefixWord, tailWord_2100516, baseEnd_2100516] using wordTrace_append hprefix tailTrace_2100516
  have hstable : (prefixWord ++ tailWord_2100516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100516).length < 2 ^ (prefixWord ++ tailWord_2100516).sum := by decide
  have hdescent : baseEnd_2100516 < baseStart_2100516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100522 : List Nat := [3, 1, 4, 2, 1, 1, 1, 5, 1, 3]
def baseStart_2100522 : Nat := 118140960795 + 2100522 * 2 ^ 59
def prefixEnd_2100522 : Nat := 4983230072969 + 3 ^ 40 * 2100522 * 2
def baseEnd_2100522 : Nat := 719051607562357287809921

theorem tailTrace_2100522 : CollatzResearch.WordTrace tailWord_2100522 prefixEnd_2100522 719051607562357287809921 := by
  unfold tailWord_2100522
  simp only [CollatzResearch.WordTrace]
  refine ⟨19153082824043752360477955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51074887530783339627941213 19153082824043752360477955)
  ·
    refine ⟨28729624236065628540716933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19153082824043752360477955 28729624236065628540716933)
    ·
      refine ⟨5386804544262305351384425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28729624236065628540716933 5386804544262305351384425)
      ·
        refine ⟨4040103408196729013538319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5386804544262305351384425 4040103408196729013538319)
        ·
          refine ⟨6060155112295093520307479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4040103408196729013538319 6060155112295093520307479)
          ·
            refine ⟨9090232668442640280461219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6060155112295093520307479 9090232668442640280461219)
            ·
              refine ⟨13635349002663960420691829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9090232668442640280461219 13635349002663960420691829)
              ·
                refine ⟨1278313968999746289439859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13635349002663960420691829 1278313968999746289439859)
                ·
                  refine ⟨1917470953499619434159789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1278313968999746289439859 1917470953499619434159789)
                  ·
                    refine ⟨719051607562357287809921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917470953499619434159789 719051607562357287809921)
                    ·
                      rfl

theorem cell22_2100522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_2100522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100522 prefixEnd_2100522 := by exact prefixLift 2100522
  have htrace : WordTrace (prefixWord ++ tailWord_2100522) baseStart_2100522 baseEnd_2100522 := by
    simpa [prefixWord, tailWord_2100522, baseEnd_2100522] using wordTrace_append hprefix tailTrace_2100522
  have hstable : (prefixWord ++ tailWord_2100522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100522).length < 2 ^ (prefixWord ++ tailWord_2100522).sum := by decide
  have hdescent : baseEnd_2100522 < baseStart_2100522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100565 : List Nat := [1, 3, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_2100565 : Nat := 118140960795 + 2100565 * 2 ^ 59
def prefixEnd_2100565 : Nat := 4983230072969 + 3 ^ 40 * 2100565 * 2
def baseEnd_2100565 : Nat := 719066327341119508984789

theorem tailTrace_2100565 : CollatzResearch.WordTrace tailWord_2100565 prefixEnd_2100565 719066327341119508984789 := by
  unfold tailWord_2100565
  simp only [CollatzResearch.WordTrace]
  refine ⟨76613899635019227785727149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51075933090012818523818099 76613899635019227785727149)
  ·
    refine ⟨28730212363132210419647681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76613899635019227785727149 28730212363132210419647681)
    ·
      refine ⟨21547659272349157814735761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28730212363132210419647681 21547659272349157814735761)
      ·
        refine ⟨16160744454261868361051821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21547659272349157814735761 16160744454261868361051821)
        ·
          refine ⟨6060279170348200635394433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16160744454261868361051821 6060279170348200635394433)
          ·
            refine ⟨4545209377761150476545825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6060279170348200635394433 4545209377761150476545825)
            ·
              refine ⟨3408907033320862857409369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4545209377761150476545825 3408907033320862857409369)
              ·
                refine ⟨2556680274990647143057027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3408907033320862857409369 2556680274990647143057027)
                ·
                  refine ⟨3835020412485970714585541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2556680274990647143057027 3835020412485970714585541)
                  ·
                    refine ⟨719066327341119508984789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3835020412485970714585541 719066327341119508984789)
                    ·
                      rfl

theorem cell22_2100565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_2100565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100565 prefixEnd_2100565 := by exact prefixLift 2100565
  have htrace : WordTrace (prefixWord ++ tailWord_2100565) baseStart_2100565 baseEnd_2100565 := by
    simpa [prefixWord, tailWord_2100565, baseEnd_2100565] using wordTrace_append hprefix tailTrace_2100565
  have hstable : (prefixWord ++ tailWord_2100565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100565).length < 2 ^ (prefixWord ++ tailWord_2100565).sum := by decide
  have hdescent : baseEnd_2100565 < baseStart_2100565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100573 : List Nat := [1, 4, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2100573 : Nat := 118140960795 + 2100573 * 2 ^ 59
def prefixEnd_2100573 : Nat := 4983230072969 + 3 ^ 40 * 2100573 * 2
def baseEnd_2100573 : Nat := 719069065904610154784765

theorem tailTrace_2100573 : CollatzResearch.WordTrace tailWord_2100573 prefixEnd_2100573 719069065904610154784765 := by
  unfold tailWord_2100573
  simp only [CollatzResearch.WordTrace]
  refine ⟨76614191418990245152018373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51076127612660163434678915 76614191418990245152018373)
  ·
    refine ⟨14365160891060670966003445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76614191418990245152018373 14365160891060670966003445)
    ·
      refine ⟨1346733833536937903062823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14365160891060670966003445 1346733833536937903062823)
      ·
        refine ⟨2020100750305406854594235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346733833536937903062823 2020100750305406854594235)
        ·
          refine ⟨3030151125458110281891353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2020100750305406854594235 3030151125458110281891353)
          ·
            refine ⟨2272613344093582711418515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3030151125458110281891353 2272613344093582711418515)
            ·
              refine ⟨3408920016140374067127773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272613344093582711418515 3408920016140374067127773)
              ·
                refine ⟨1278345006052640275172915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3408920016140374067127773 1278345006052640275172915)
                ·
                  refine ⟨1917517509078960412759373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1278345006052640275172915 1917517509078960412759373)
                  ·
                    refine ⟨719069065904610154784765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917517509078960412759373 719069065904610154784765)
                    ·
                      rfl

theorem cell22_2100573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2100573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100573 prefixEnd_2100573 := by exact prefixLift 2100573
  have htrace : WordTrace (prefixWord ++ tailWord_2100573) baseStart_2100573 baseEnd_2100573 := by
    simpa [prefixWord, tailWord_2100573, baseEnd_2100573] using wordTrace_append hprefix tailTrace_2100573
  have hstable : (prefixWord ++ tailWord_2100573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100573).length < 2 ^ (prefixWord ++ tailWord_2100573).sum := by decide
  have hdescent : baseEnd_2100573 < baseStart_2100573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100578 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2100578 : Nat := 118140960795 + 2100578 * 2 ^ 59
def prefixEnd_2100578 : Nat := 4983230072969 + 3 ^ 40 * 2100578 * 2
def baseEnd_2100578 : Nat := 719070777506791808409749

theorem tailTrace_2100578 : CollatzResearch.WordTrace tailWord_2100578 prefixEnd_2100578 719070777506791808409749 := by
  unfold tailWord_2100578
  simp only [CollatzResearch.WordTrace]
  refine ⟨19153593445993032751487597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51076249189314754003966925 19153593445993032751487597)
  ·
    refine ⟨7182597542247387281807849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19153593445993032751487597 7182597542247387281807849)
    ·
      refine ⟨5386948156685540461355887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7182597542247387281807849 5386948156685540461355887)
      ·
        refine ⟨8080422235028310692033831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5386948156685540461355887 8080422235028310692033831)
        ·
          refine ⟨12120633352542466038050747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8080422235028310692033831 12120633352542466038050747)
          ·
            refine ⟨18180950028813699057076121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12120633352542466038050747 18180950028813699057076121)
            ·
              refine ⟨13635712521610274292807091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18180950028813699057076121 13635712521610274292807091)
              ·
                refine ⟨20453568782415411439210637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13635712521610274292807091 20453568782415411439210637)
                ·
                  refine ⟨7670088293405779289703989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20453568782415411439210637 7670088293405779289703989)
                  ·
                    refine ⟨719070777506791808409749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7670088293405779289703989 719070777506791808409749)
                    ·
                      rfl

theorem cell22_2100578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2100578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100578 prefixEnd_2100578 := by exact prefixLift 2100578
  have htrace : WordTrace (prefixWord ++ tailWord_2100578) baseStart_2100578 baseEnd_2100578 := by
    simpa [prefixWord, tailWord_2100578, baseEnd_2100578] using wordTrace_append hprefix tailTrace_2100578
  have hstable : (prefixWord ++ tailWord_2100578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100578).length < 2 ^ (prefixWord ++ tailWord_2100578).sum := by decide
  have hdescent : baseEnd_2100578 < baseStart_2100578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100580 : List Nat := [2, 3, 1, 1, 3, 2, 3, 3, 4]
def baseStart_2100580 : Nat := 118140960795 + 2100580 * 2 ^ 59
def prefixEnd_2100580 : Nat := 4983230072969 + 3 ^ 40 * 2100580 * 2
def baseEnd_2100580 : Nat := 239690487382554823286581

theorem tailTrace_2100580 : CollatzResearch.WordTrace tailWord_2100580 prefixEnd_2100580 239690487382554823286581 := by
  unfold tailWord_2100580
  simp only [CollatzResearch.WordTrace]
  refine ⟨38307223364982442673761597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51076297819976590231682129 38307223364982442673761597)
  ·
    refine ⟨14365208761868416002660599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38307223364982442673761597 14365208761868416002660599)
    ·
      refine ⟨21547813142802624003990899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14365208761868416002660599 21547813142802624003990899)
      ·
        refine ⟨32321719714203936005986349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21547813142802624003990899 32321719714203936005986349)
        ·
          refine ⟨12120644892826476002244881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32321719714203936005986349 12120644892826476002244881)
          ·
            refine ⟨9090483669619857001683661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12120644892826476002244881 9090483669619857001683661)
            ·
              refine ⟨3408931376107446375631373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9090483669619857001683661 3408931376107446375631373)
              ·
                refine ⟨1278349266040292390861765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3408931376107446375631373 1278349266040292390861765)
                ·
                  refine ⟨239690487382554823286581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278349266040292390861765 239690487382554823286581)
                  ·
                    rfl

theorem cell22_2100580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_2100580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100580 prefixEnd_2100580 := by exact prefixLift 2100580
  have htrace : WordTrace (prefixWord ++ tailWord_2100580) baseStart_2100580 baseEnd_2100580 := by
    simpa [prefixWord, tailWord_2100580, baseEnd_2100580] using wordTrace_append hprefix tailTrace_2100580
  have hstable : (prefixWord ++ tailWord_2100580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100580).length < 2 ^ (prefixWord ++ tailWord_2100580).sum := by decide
  have hdescent : baseEnd_2100580 < baseStart_2100580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100597 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 6]
def baseStart_2100597 : Nat := 118140960795 + 2100597 * 2 ^ 59
def prefixEnd_2100597 : Nat := 4983230072969 + 3 ^ 40 * 2100597 * 2
def baseEnd_2100597 : Nat := 239692427198360697394897

theorem tailTrace_2100597 : CollatzResearch.WordTrace tailWord_2100597 prefixEnd_2100597 239692427198360697394897 := by
  unfold tailWord_2100597
  simp only [CollatzResearch.WordTrace]
  refine ⟨76615066770903297250892045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51076711180602198167261363 76615066770903297250892045)
  ·
    refine ⟨28730650039088736469084517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76615066770903297250892045 28730650039088736469084517)
    ·
      refine ⟨5386996882329138087953347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28730650039088736469084517 5386996882329138087953347)
      ·
        refine ⟨8080495323493707131930021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5386996882329138087953347 8080495323493707131930021)
        ·
          refine ⟨1515092873155070087236879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8080495323493707131930021 1515092873155070087236879)
          ·
            refine ⟨2272639309732605130855319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515092873155070087236879 2272639309732605130855319)
            ·
              refine ⟨3408958964598907696282979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272639309732605130855319 3408958964598907696282979)
              ·
                refine ⟨5113438446898361544424469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3408958964598907696282979 5113438446898361544424469)
                ·
                  refine ⟨239692427198360697394897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5113438446898361544424469 239692427198360697394897)
                  ·
                    rfl

theorem cell22_2100597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_2100597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100597 prefixEnd_2100597 := by exact prefixLift 2100597
  have htrace : WordTrace (prefixWord ++ tailWord_2100597) baseStart_2100597 baseEnd_2100597 := by
    simpa [prefixWord, tailWord_2100597, baseEnd_2100597] using wordTrace_append hprefix tailTrace_2100597
  have hstable : (prefixWord ++ tailWord_2100597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100597).length < 2 ^ (prefixWord ++ tailWord_2100597).sum := by decide
  have hdescent : baseEnd_2100597 < baseStart_2100597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100612 : List Nat := [2, 3, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_2100612 : Nat := 118140960795 + 2100612 * 2 ^ 59
def prefixEnd_2100612 : Nat := 4983230072969 + 3 ^ 40 * 2100612 * 2
def baseEnd_2100612 : Nat := 719082416401627053059645

theorem tailTrace_2100612 : CollatzResearch.WordTrace tailWord_2100612 prefixEnd_2100612 719082416401627053059645 := by
  unfold tailWord_2100612
  simp only [CollatzResearch.WordTrace]
  refine ⟨38307806932924477406344045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51077075910565969875125393 38307806932924477406344045)
  ·
    refine ⟨14365427599846679027379017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38307806932924477406344045 14365427599846679027379017)
    ·
      refine ⟨10774070699885009270534263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14365427599846679027379017 10774070699885009270534263)
      ·
        refine ⟨16161106049827513905801395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10774070699885009270534263 16161106049827513905801395)
        ·
          refine ⟨24241659074741270858702093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16161106049827513905801395 24241659074741270858702093)
          ·
            refine ⟨9090622153027976572013285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24241659074741270858702093 9090622153027976572013285)
            ·
              refine ⟨1704491653692745607252491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9090622153027976572013285 1704491653692745607252491)
              ·
                refine ⟨2556737480539118410878737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704491653692745607252491 2556737480539118410878737)
                ·
                  refine ⟨1917553110404338808159053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2556737480539118410878737 1917553110404338808159053)
                  ·
                    refine ⟨719082416401627053059645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917553110404338808159053 719082416401627053059645)
                    ·
                      rfl

theorem cell22_2100612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_2100612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100612 prefixEnd_2100612 := by exact prefixLift 2100612
  have htrace : WordTrace (prefixWord ++ tailWord_2100612) baseStart_2100612 baseEnd_2100612 := by
    simpa [prefixWord, tailWord_2100612, baseEnd_2100612] using wordTrace_append hprefix tailTrace_2100612
  have hstable : (prefixWord ++ tailWord_2100612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100612).length < 2 ^ (prefixWord ++ tailWord_2100612).sum := by decide
  have hdescent : baseEnd_2100612 < baseStart_2100612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100657 : List Nat := [1, 2, 2, 4, 1, 1, 3, 4, 1, 3]
def baseStart_2100657 : Nat := 118140960795 + 2100657 * 2 ^ 59
def prefixEnd_2100657 : Nat := 4983230072969 + 3 ^ 40 * 2100657 * 2
def baseEnd_2100657 : Nat := 719097820821261935684507

theorem tailTrace_2100657 : CollatzResearch.WordTrace tailWord_2100657 prefixEnd_2100657 719097820821261935684507 := by
  unfold tailWord_2100657
  simp only [CollatzResearch.WordTrace]
  refine ⟨76617255150685927498076225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51078170100457284998717483 76617255150685927498076225)
  ·
    refine ⟨57462941363014445623557169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76617255150685927498076225 57462941363014445623557169)
    ·
      refine ⟨43097206022260834217667877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57462941363014445623557169 43097206022260834217667877)
      ·
        refine ⟨8080726129173906415812727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43097206022260834217667877 8080726129173906415812727)
        ·
          refine ⟨12121089193760859623719091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8080726129173906415812727 12121089193760859623719091)
          ·
            refine ⟨18181633790641289435578637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12121089193760859623719091 18181633790641289435578637)
            ·
              refine ⟨6818112671490483538341989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18181633790641289435578637 6818112671490483538341989)
              ·
                refine ⟨1278396125904465663439123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6818112671490483538341989 1278396125904465663439123)
                ·
                  refine ⟨1917594188856698495158685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1278396125904465663439123 1917594188856698495158685)
                  ·
                    refine ⟨719097820821261935684507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917594188856698495158685 719097820821261935684507)
                    ·
                      rfl

theorem cell22_2100657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_2100657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100657 prefixEnd_2100657 := by exact prefixLift 2100657
  have htrace : WordTrace (prefixWord ++ tailWord_2100657) baseStart_2100657 baseEnd_2100657 := by
    simpa [prefixWord, tailWord_2100657, baseEnd_2100657] using wordTrace_append hprefix tailTrace_2100657
  have hstable : (prefixWord ++ tailWord_2100657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100657).length < 2 ^ (prefixWord ++ tailWord_2100657).sum := by decide
  have hdescent : baseEnd_2100657 < baseStart_2100657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100683 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 3, 4]
def baseStart_2100683 : Nat := 118140960795 + 2100683 * 2 ^ 59
def prefixEnd_2100683 : Nat := 4983230072969 + 3 ^ 40 * 2100683 * 2
def baseEnd_2100683 : Nat := 719106721152606534534427

theorem tailTrace_2100683 : CollatzResearch.WordTrace tailWord_2100683 prefixEnd_2100683 719106721152606534534427 := by
  unfold tailWord_2100683
  simp only [CollatzResearch.WordTrace]
  refine ⟨76618203448591733938522703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51078802299061155959015135 76618203448591733938522703)
  ·
    refine ⟨114927305172887600907784055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76618203448591733938522703 114927305172887600907784055)
    ·
      refine ⟨172390957759331401361676083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114927305172887600907784055 172390957759331401361676083)
      ·
        refine ⟨258586436638997102042514125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172390957759331401361676083 258586436638997102042514125)
        ·
          refine ⟨96969913739623913265942797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258586436638997102042514125 96969913739623913265942797)
          ·
            refine ⟨36363717652358967474728549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96969913739623913265942797 36363717652358967474728549)
            ·
              refine ⟨6818197059817306401511603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36363717652358967474728549 6818197059817306401511603)
              ·
                refine ⟨10227295589725959602267405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6818197059817306401511603 10227295589725959602267405)
                ·
                  refine ⟨3835235846147234850850277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10227295589725959602267405 3835235846147234850850277)
                  ·
                    refine ⟨719106721152606534534427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3835235846147234850850277 719106721152606534534427)
                    ·
                      rfl

theorem cell22_2100683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 4].length) (baseStart_2100683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100683 prefixEnd_2100683 := by exact prefixLift 2100683
  have htrace : WordTrace (prefixWord ++ tailWord_2100683) baseStart_2100683 baseEnd_2100683 := by
    simpa [prefixWord, tailWord_2100683, baseEnd_2100683] using wordTrace_append hprefix tailTrace_2100683
  have hstable : (prefixWord ++ tailWord_2100683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100683).length < 2 ^ (prefixWord ++ tailWord_2100683).sum := by decide
  have hdescent : baseEnd_2100683 < baseStart_2100683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100728 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 1, 6]
def baseStart_2100728 : Nat := 118140960795 + 2100728 * 2 ^ 59
def prefixEnd_2100728 : Nat := 4983230072969 + 3 ^ 40 * 2100728 * 2
def baseEnd_2100728 : Nat := 719122125572241417159289

theorem tailTrace_2100728 : CollatzResearch.WordTrace tailWord_2100728 prefixEnd_2100728 719122125572241417159289 := by
  unfold tailWord_2100728
  simp only [CollatzResearch.WordTrace]
  refine ⟨38309922366714353311955419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51079896488952471082607225 38309922366714353311955419)
  ·
    refine ⟨57464883550071529967933129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38309922366714353311955419 57464883550071529967933129)
    ·
      refine ⟨43098662662553647475949847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57464883550071529967933129 43098662662553647475949847)
      ·
        refine ⟨64647993993830471213924771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43098662662553647475949847 64647993993830471213924771)
        ·
          refine ⟨96971990990745706820887157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64647993993830471213924771 96971990990745706820887157)
          ·
            refine ⟨9091124155382410014458171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96971990990745706820887157 9091124155382410014458171)
            ·
              refine ⟨13636686233073615021687257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9091124155382410014458171 13636686233073615021687257)
              ·
                refine ⟨10227514674805211266265443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13636686233073615021687257 10227514674805211266265443)
                ·
                  refine ⟨15341272012207816899398165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10227514674805211266265443 15341272012207816899398165)
                  ·
                    refine ⟨719122125572241417159289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15341272012207816899398165 719122125572241417159289)
                    ·
                      rfl

theorem cell22_2100728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_2100728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100728 prefixEnd_2100728 := by exact prefixLift 2100728
  have htrace : WordTrace (prefixWord ++ tailWord_2100728) baseStart_2100728 baseEnd_2100728 := by
    simpa [prefixWord, tailWord_2100728, baseEnd_2100728] using wordTrace_append hprefix tailTrace_2100728
  have hstable : (prefixWord ++ tailWord_2100728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100728).length < 2 ^ (prefixWord ++ tailWord_2100728).sum := by decide
  have hdescent : baseEnd_2100728 < baseStart_2100728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100742 : List Nat := [6, 2, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2100742 : Nat := 118140960795 + 2100742 * 2 ^ 59
def prefixEnd_2100742 : Nat := 4983230072969 + 3 ^ 40 * 2100742 * 2
def baseEnd_2100742 : Nat := 719126918058350047309247

theorem tailTrace_2100742 : CollatzResearch.WordTrace tailWord_2100742 prefixEnd_2100742 719126918058350047309247 := by
  unfold tailWord_2100742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2394386104855562094216265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51080236903585324676613653 2394386104855562094216265)
  ·
    refine ⟨1795789578641671570662199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2394386104855562094216265 1795789578641671570662199)
    ·
      refine ⟨2693684367962507355993299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1795789578641671570662199 2693684367962507355993299)
      ·
        refine ⟨4040526551943761033989949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2693684367962507355993299 4040526551943761033989949)
        ·
          refine ⟨1515197456978910387746231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4040526551943761033989949 1515197456978910387746231)
          ·
            refine ⟨2272796185468365581619347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515197456978910387746231 2272796185468365581619347)
            ·
              refine ⟨3409194278202548372429021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272796185468365581619347 3409194278202548372429021)
              ·
                refine ⟨1278447854325955639660883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3409194278202548372429021 1278447854325955639660883)
                ·
                  refine ⟨1917671781488933459491325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1278447854325955639660883 1917671781488933459491325)
                  ·
                    refine ⟨719126918058350047309247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917671781488933459491325 719126918058350047309247)
                    ·
                      rfl

theorem cell22_2100742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2100742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100742 prefixEnd_2100742 := by exact prefixLift 2100742
  have htrace : WordTrace (prefixWord ++ tailWord_2100742) baseStart_2100742 baseEnd_2100742 := by
    simpa [prefixWord, tailWord_2100742, baseEnd_2100742] using wordTrace_append hprefix tailTrace_2100742
  have hstable : (prefixWord ++ tailWord_2100742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100742).length < 2 ^ (prefixWord ++ tailWord_2100742).sum := by decide
  have hdescent : baseEnd_2100742 < baseStart_2100742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100760 : List Nat := [2, 1, 2, 3, 4, 2, 8]
def baseStart_2100760 : Nat := 118140960795 + 2100760 * 2 ^ 59
def prefixEnd_2100760 : Nat := 4983230072969 + 3 ^ 40 * 2100760 * 2
def baseEnd_2100760 : Nat := 26634558512081629642933

theorem tailTrace_2100760 : CollatzResearch.WordTrace tailWord_2100760 prefixEnd_2100760 26634558512081629642933 := by
  unfold tailWord_2100760
  simp only [CollatzResearch.WordTrace]
  refine ⟨38310505934656388044537867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51080674579541850726050489 38310505934656388044537867)
  ·
    refine ⟨57465758901984582066806801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38310505934656388044537867 57465758901984582066806801)
    ·
      refine ⟨43099319176488436550105101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57465758901984582066806801 43099319176488436550105101)
      ·
        refine ⟨16162244691183163706289413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43099319176488436550105101 16162244691183163706289413)
        ·
          refine ⟨3030420879596843194929265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16162244691183163706289413 3030420879596843194929265)
          ·
            refine ⟨2272815659697632396196949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3030420879596843194929265 2272815659697632396196949)
            ·
              refine ⟨26634558512081629642933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2272815659697632396196949 26634558512081629642933)
              ·
                rfl

theorem cell22_2100760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 8].length) (baseStart_2100760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100760 prefixEnd_2100760 := by exact prefixLift 2100760
  have htrace : WordTrace (prefixWord ++ tailWord_2100760) baseStart_2100760 baseEnd_2100760 := by
    simpa [prefixWord, tailWord_2100760, baseEnd_2100760] using wordTrace_append hprefix tailTrace_2100760
  have hstable : (prefixWord ++ tailWord_2100760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100760).length < 2 ^ (prefixWord ++ tailWord_2100760).sum := by decide
  have hdescent : baseEnd_2100760 < baseStart_2100760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100773 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_2100773 : Nat := 118140960795 + 2100773 * 2 ^ 59
def prefixEnd_2100773 : Nat := 4983230072969 + 3 ^ 40 * 2100773 * 2
def baseEnd_2100773 : Nat := 719137529991876299784151

theorem tailTrace_2100773 : CollatzResearch.WordTrace tailWord_2100773 prefixEnd_2100773 719137529991876299784151 := by
  unfold tailWord_2100773
  simp only [CollatzResearch.WordTrace]
  refine ⟨76621486018265679309298973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51080990678843786206199315 76621486018265679309298973)
  ·
    refine ⟨28733057256849629740987115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76621486018265679309298973 28733057256849629740987115)
    ·
      refine ⟨43099585885274444611480673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28733057256849629740987115 43099585885274444611480673)
      ·
        refine ⟨32324689413955833458610505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43099585885274444611480673 32324689413955833458610505)
        ·
          refine ⟨24243517060466875093957879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32324689413955833458610505 24243517060466875093957879)
          ·
            refine ⟨36365275590700312640936819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24243517060466875093957879 36365275590700312640936819)
            ·
              refine ⟨54547913386050468961405229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36365275590700312640936819 54547913386050468961405229)
              ·
                refine ⟨20455467519768925860526961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54547913386050468961405229 20455467519768925860526961)
                ·
                  refine ⟨15341600639826694395395221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20455467519768925860526961 15341600639826694395395221)
                  ·
                    refine ⟨719137529991876299784151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15341600639826694395395221 719137529991876299784151)
                    ·
                      rfl

theorem cell22_2100773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_2100773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100773 prefixEnd_2100773 := by exact prefixLift 2100773
  have htrace : WordTrace (prefixWord ++ tailWord_2100773) baseStart_2100773 baseEnd_2100773 := by
    simpa [prefixWord, tailWord_2100773, baseEnd_2100773] using wordTrace_append hprefix tailTrace_2100773
  have hstable : (prefixWord ++ tailWord_2100773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100773).length < 2 ^ (prefixWord ++ tailWord_2100773).sum := by decide
  have hdescent : baseEnd_2100773 < baseStart_2100773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100803 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 6, 5]
def baseStart_2100803 : Nat := 118140960795 + 2100803 * 2 ^ 59
def prefixEnd_2100803 : Nat := 4983230072969 + 3 ^ 40 * 2100803 * 2
def baseEnd_2100803 : Nat := 719147799604966221534059

theorem tailTrace_2100803 : CollatzResearch.WordTrace tailWord_2100803 prefixEnd_2100803 719147799604966221534059 := by
  unfold tailWord_2100803
  simp only [CollatzResearch.WordTrace]
  refine ⟨76622580208156994432891063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51081720138771329621927375 76622580208156994432891063)
  ·
    refine ⟨114933870312235491649336595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76622580208156994432891063 114933870312235491649336595)
    ·
      refine ⟨172400805468353237474004893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114933870312235491649336595 172400805468353237474004893)
      ·
        refine ⟨64650302050632464052751835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172400805468353237474004893 64650302050632464052751835)
        ·
          refine ⟨96975453075948696079127753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64650302050632464052751835 96975453075948696079127753)
          ·
            refine ⟨72731589806961522059345815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96975453075948696079127753 72731589806961522059345815)
            ·
              refine ⟨109097384710442283089018723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72731589806961522059345815 109097384710442283089018723)
              ·
                refine ⟨163646077065663424633528085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109097384710442283089018723 163646077065663424633528085)
                ·
                  refine ⟨7670909862452973029696629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163646077065663424633528085 7670909862452973029696629)
                  ·
                    refine ⟨719147799604966221534059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7670909862452973029696629 719147799604966221534059)
                    ·
                      rfl

theorem cell22_2100803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_2100803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100803 prefixEnd_2100803 := by exact prefixLift 2100803
  have htrace : WordTrace (prefixWord ++ tailWord_2100803) baseStart_2100803 baseEnd_2100803 := by
    simpa [prefixWord, tailWord_2100803, baseEnd_2100803] using wordTrace_append hprefix tailTrace_2100803
  have hstable : (prefixWord ++ tailWord_2100803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100803).length < 2 ^ (prefixWord ++ tailWord_2100803).sum := by decide
  have hdescent : baseEnd_2100803 < baseStart_2100803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100820 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2100820 : Nat := 118140960795 + 2100820 * 2 ^ 59
def prefixEnd_2100820 : Nat := 4983230072969 + 3 ^ 40 * 2100820 * 2
def baseEnd_2100820 : Nat := 719153619052383843859007

theorem tailTrace_2100820 : CollatzResearch.WordTrace tailWord_2100820 prefixEnd_2100820 719153619052383843859007 := by
  unfold tailWord_2100820
  simp only [CollatzResearch.WordTrace]
  refine ⟨38311600124547703168129957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51082133499396937557506609 38311600124547703168129957)
  ·
    refine ⟨7183425023352694344024367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38311600124547703168129957 7183425023352694344024367)
    ·
      refine ⟨10775137535029041516036551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7183425023352694344024367 10775137535029041516036551)
      ·
        refine ⟨16162706302543562274054827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10775137535029041516036551 16162706302543562274054827)
        ·
          refine ⟨24244059453815343411082241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16162706302543562274054827 24244059453815343411082241)
          ·
            refine ⟨18183044590361507558311681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24244059453815343411082241 18183044590361507558311681)
            ·
              refine ⟨13637283442771130668733761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18183044590361507558311681 13637283442771130668733761)
              ·
                refine ⟨10227962582078348001550321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13637283442771130668733761 10227962582078348001550321)
                ·
                  refine ⟨7670971936558761001162741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10227962582078348001550321 7670971936558761001162741)
                  ·
                    refine ⟨719153619052383843859007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7670971936558761001162741 719153619052383843859007)
                    ·
                      rfl

theorem cell22_2100820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2100820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100820 prefixEnd_2100820 := by exact prefixLift 2100820
  have htrace : WordTrace (prefixWord ++ tailWord_2100820) baseStart_2100820 baseEnd_2100820 := by
    simpa [prefixWord, tailWord_2100820, baseEnd_2100820] using wordTrace_append hprefix tailTrace_2100820
  have hstable : (prefixWord ++ tailWord_2100820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100820).length < 2 ^ (prefixWord ++ tailWord_2100820).sum := by decide
  have hdescent : baseEnd_2100820 < baseStart_2100820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100835 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 3, 4]
def baseStart_2100835 : Nat := 118140960795 + 2100835 * 2 ^ 59
def prefixEnd_2100835 : Nat := 4983230072969 + 3 ^ 40 * 2100835 * 2
def baseEnd_2100835 : Nat := 719158753858928804733961

theorem tailTrace_2100835 : CollatzResearch.WordTrace tailWord_2100835 prefixEnd_2100835 719158753858928804733961 := by
  unfold tailWord_2100835
  simp only [CollatzResearch.WordTrace]
  refine ⟨76623747344041063898055959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51082498229360709265370639 76623747344041063898055959)
  ·
    refine ⟨114935621016061595847083939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76623747344041063898055959 114935621016061595847083939)
    ·
      refine ⟨172403431524092393770625909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114935621016061595847083939 172403431524092393770625909)
      ·
        refine ⟨16162821705383661915996179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172403431524092393770625909 16162821705383661915996179)
        ·
          refine ⟨24244232558075492873994269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16162821705383661915996179 24244232558075492873994269)
          ·
            refine ⟨9091587209278309827747851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24244232558075492873994269 9091587209278309827747851)
            ·
              refine ⟨13637380813917464741621777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9091587209278309827747851 13637380813917464741621777)
              ·
                refine ⟨10228035610438098556216333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13637380813917464741621777 10228035610438098556216333)
                ·
                  refine ⟨3835513353914286958581125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10228035610438098556216333 3835513353914286958581125)
                  ·
                    refine ⟨719158753858928804733961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3835513353914286958581125 719158753858928804733961)
                    ·
                      rfl

theorem cell22_2100835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 4].length) (baseStart_2100835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100835 prefixEnd_2100835 := by exact prefixLift 2100835
  have htrace : WordTrace (prefixWord ++ tailWord_2100835) baseStart_2100835 baseEnd_2100835 := by
    simpa [prefixWord, tailWord_2100835, baseEnd_2100835] using wordTrace_append hprefix tailTrace_2100835
  have hstable : (prefixWord ++ tailWord_2100835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100835).length < 2 ^ (prefixWord ++ tailWord_2100835).sum := by decide
  have hdescent : baseEnd_2100835 < baseStart_2100835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100850 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 8]
def baseStart_2100850 : Nat := 118140960795 + 2100850 * 2 ^ 59
def prefixEnd_2100850 : Nat := 4983230072969 + 3 ^ 40 * 2100850 * 2
def baseEnd_2100850 : Nat := 239721296221824588536305

theorem tailTrace_2100850 : CollatzResearch.WordTrace tailWord_2100850 prefixEnd_2100850 239721296221824588536305 := by
  unfold tailWord_2100850
  simp only [CollatzResearch.WordTrace]
  refine ⟨19156073609746680364963001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51082862959324480973234669 19156073609746680364963001)
  ·
    refine ⟨14367055207310010273722251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19156073609746680364963001 14367055207310010273722251)
    ·
      refine ⟨21550582810965015410583377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14367055207310010273722251 21550582810965015410583377)
      ·
        refine ⟨16162937108223761557937533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21550582810965015410583377 16162937108223761557937533)
        ·
          refine ⟨6061101415583910584226575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16162937108223761557937533 6061101415583910584226575)
          ·
            refine ⟨9091652123375865876339863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6061101415583910584226575 9091652123375865876339863)
            ·
              refine ⟨13637478185063798814509795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9091652123375865876339863 13637478185063798814509795)
              ·
                refine ⟨20456217277595698221764693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13637478185063798814509795 20456217277595698221764693)
                ·
                  refine ⟨239721296221824588536305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20456217277595698221764693 239721296221824588536305)
                  ·
                    rfl

theorem cell22_2100850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_2100850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100850 prefixEnd_2100850 := by exact prefixLift 2100850
  have htrace : WordTrace (prefixWord ++ tailWord_2100850) baseStart_2100850 baseEnd_2100850 := by
    simpa [prefixWord, tailWord_2100850, baseEnd_2100850] using wordTrace_append hprefix tailTrace_2100850
  have hstable : (prefixWord ++ tailWord_2100850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100850).length < 2 ^ (prefixWord ++ tailWord_2100850).sum := by decide
  have hdescent : baseEnd_2100850 < baseStart_2100850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100880 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 2, 4]
def baseStart_2100880 : Nat := 118140960795 + 2100880 * 2 ^ 59
def prefixEnd_2100880 : Nat := 4983230072969 + 3 ^ 40 * 2100880 * 2
def baseEnd_2100880 : Nat := 719174158278563687358823

theorem tailTrace_2100880 : CollatzResearch.WordTrace tailWord_2100880 prefixEnd_2100880 719174158278563687358823 := by
  unfold tailWord_2100880
  simp only [CollatzResearch.WordTrace]
  refine ⟨38312694314439018291722047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51083592419252024388962729 38312694314439018291722047)
  ·
    refine ⟨57469041471658527437583071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38312694314439018291722047 57469041471658527437583071)
    ·
      refine ⟨86203562207487791156374607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57469041471658527437583071 86203562207487791156374607)
      ·
        refine ⟨129305343311231686734561911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86203562207487791156374607 129305343311231686734561911)
        ·
          refine ⟨193958014966847530101842867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129305343311231686734561911 193958014966847530101842867)
          ·
            refine ⟨290937022450271295152764301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193958014966847530101842867 290937022450271295152764301)
            ·
              refine ⟨109101383418851735682286613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290937022450271295152764301 109101383418851735682286613)
              ·
                refine ⟨5114127347758675110107185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109101383418851735682286613 5114127347758675110107185)
                ·
                  refine ⟨3835595510819006332580389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5114127347758675110107185 3835595510819006332580389)
                  ·
                    refine ⟨719174158278563687358823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3835595510819006332580389 719174158278563687358823)
                    ·
                      rfl

theorem cell22_2100880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_2100880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100880 prefixEnd_2100880 := by exact prefixLift 2100880
  have htrace : WordTrace (prefixWord ++ tailWord_2100880) baseStart_2100880 baseEnd_2100880 := by
    simpa [prefixWord, tailWord_2100880, baseEnd_2100880] using wordTrace_append hprefix tailTrace_2100880
  have hstable : (prefixWord ++ tailWord_2100880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100880).length < 2 ^ (prefixWord ++ tailWord_2100880).sum := by decide
  have hdescent : baseEnd_2100880 < baseStart_2100880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100884 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 6]
def baseStart_2100884 : Nat := 118140960795 + 2100884 * 2 ^ 59
def prefixEnd_2100884 : Nat := 4983230072969 + 3 ^ 40 * 2100884 * 2
def baseEnd_2100884 : Nat := 239725175853436336752937

theorem tailTrace_2100884 : CollatzResearch.WordTrace tailWord_2100884 prefixEnd_2100884 239725175853436336752937 := by
  unfold tailWord_2100884
  simp only [CollatzResearch.WordTrace]
  refine ⟨38312767260431772633294853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51083689680575696844393137 38312767260431772633294853)
  ·
    refine ⟨7183643861330957368742785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38312767260431772633294853 7183643861330957368742785)
    ·
      refine ⟨5387732895998218026557089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7183643861330957368742785 5387732895998218026557089)
      ·
        refine ⟨4040799671998663519917817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5387732895998218026557089 4040799671998663519917817)
        ·
          refine ⟨3030599753998997639938363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4040799671998663519917817 3030599753998997639938363)
          ·
            refine ⟨4545899630998496459907545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030599753998997639938363 4545899630998496459907545)
            ·
              refine ⟨3409424723248872344930659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4545899630998496459907545 3409424723248872344930659)
              ·
                refine ⟨5114137084873308517395989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3409424723248872344930659 5114137084873308517395989)
                ·
                  refine ⟨239725175853436336752937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5114137084873308517395989 239725175853436336752937)
                  ·
                    rfl

theorem cell22_2100884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_2100884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100884 prefixEnd_2100884 := by exact prefixLift 2100884
  have htrace : WordTrace (prefixWord ++ tailWord_2100884) baseStart_2100884 baseEnd_2100884 := by
    simpa [prefixWord, tailWord_2100884, baseEnd_2100884] using wordTrace_append hprefix tailTrace_2100884
  have hstable : (prefixWord ++ tailWord_2100884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100884).length < 2 ^ (prefixWord ++ tailWord_2100884).sum := by decide
  have hdescent : baseEnd_2100884 < baseStart_2100884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100899 : List Nat := [1, 1, 1, 4, 1, 1, 7, 1, 2, 3]
def baseStart_2100899 : Nat := 118140960795 + 2100899 * 2 ^ 59
def prefixEnd_2100899 : Nat := 4983230072969 + 3 ^ 40 * 2100899 * 2
def baseEnd_2100899 : Nat := 719180662366853971133765

theorem tailTrace_2100899 : CollatzResearch.WordTrace tailWord_2100899 prefixEnd_2100899 719180662366853971133765 := by
  unfold tailWord_2100899
  simp only [CollatzResearch.WordTrace]
  refine ⟨76626081615809202828385751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51084054410539468552257167 76626081615809202828385751)
  ·
    refine ⟨114939122423713804242578627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76626081615809202828385751 114939122423713804242578627)
    ·
      refine ⟨172408683635570706363867941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114939122423713804242578627 172408683635570706363867941)
      ·
        refine ⟨32326628181669507443225239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172408683635570706363867941 32326628181669507443225239)
        ·
          refine ⟨48489942272504261164837859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32326628181669507443225239 48489942272504261164837859)
          ·
            refine ⟨72734913408756391747256789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48489942272504261164837859 72734913408756391747256789)
            ·
              refine ⟨1704724533017727931576331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 72734913408756391747256789 1704724533017727931576331)
              ·
                refine ⟨2557086799526591897364497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704724533017727931576331 2557086799526591897364497)
                ·
                  refine ⟨1917815099644943923023373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2557086799526591897364497 1917815099644943923023373)
                  ·
                    refine ⟨719180662366853971133765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917815099644943923023373 719180662366853971133765)
                    ·
                      rfl

theorem cell22_2100899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 2, 3].length) (baseStart_2100899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100899 prefixEnd_2100899 := by exact prefixLift 2100899
  have htrace : WordTrace (prefixWord ++ tailWord_2100899) baseStart_2100899 baseEnd_2100899 := by
    simpa [prefixWord, tailWord_2100899, baseEnd_2100899] using wordTrace_append hprefix tailTrace_2100899
  have hstable : (prefixWord ++ tailWord_2100899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100899).length < 2 ^ (prefixWord ++ tailWord_2100899).sum := by decide
  have hdescent : baseEnd_2100899 < baseStart_2100899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2100918 : List Nat := [5, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_2100918 : Nat := 118140960795 + 2100918 * 2 ^ 59
def prefixEnd_2100918 : Nat := 4983230072969 + 3 ^ 40 * 2100918 * 2
def baseEnd_2100918 : Nat := 239729055485048084969569

theorem tailTrace_2100918 : CollatzResearch.WordTrace tailWord_2100918 prefixEnd_2100918 239729055485048084969569 := by
  unfold tailWord_2100918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4789173412671273067082963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51084516401826912715551605 4789173412671273067082963)
  ·
    refine ⟨7183760119006909600624445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4789173412671273067082963 7183760119006909600624445)
    ·
      refine ⟨2693910044627591100234167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7183760119006909600624445 2693910044627591100234167)
      ·
        refine ⟨4040865066941386650351251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2693910044627591100234167 4040865066941386650351251)
        ·
          refine ⟨6061297600412079975526877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4040865066941386650351251 6061297600412079975526877)
          ·
            refine ⟨2272986600154529990822579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6061297600412079975526877 2272986600154529990822579)
            ·
              refine ⟨3409479900231794986233869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272986600154529990822579 3409479900231794986233869)
              ·
                refine ⟨1278554962586923119837701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3409479900231794986233869 1278554962586923119837701)
                ·
                  refine ⟨239729055485048084969569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278554962586923119837701 239729055485048084969569)
                  ·
                    rfl

theorem cell22_2100918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_2100918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2100918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2100918 prefixEnd_2100918 := by exact prefixLift 2100918
  have htrace : WordTrace (prefixWord ++ tailWord_2100918) baseStart_2100918 baseEnd_2100918 := by
    simpa [prefixWord, tailWord_2100918, baseEnd_2100918] using wordTrace_append hprefix tailTrace_2100918
  have hstable : (prefixWord ++ tailWord_2100918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2100918).length < 2 ^ (prefixWord ++ tailWord_2100918).sum := by decide
  have hdescent : baseEnd_2100918 < baseStart_2100918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2100918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101068 : List Nat := [2, 2, 1, 3, 4, 1, 3, 1, 2, 3]
def baseStart_2101068 : Nat := 118140960795 + 2101068 * 2 ^ 59
def prefixEnd_2101068 : Nat := 4983230072969 + 3 ^ 40 * 2101068 * 2
def baseEnd_2101068 : Nat := 719238514520593863658247

theorem tailTrace_2101068 : CollatzResearch.WordTrace tailWord_2101068 prefixEnd_2101068 719238514520593863658247 := by
  unfold tailWord_2101068
  simp only [CollatzResearch.WordTrace]
  refine ⟨38316122776098472345643929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51088163701464629794191905 38316122776098472345643929)
  ·
    refine ⟨28737092082073854259232947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38316122776098472345643929 28737092082073854259232947)
    ·
      refine ⟨43105638123110781388849421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28737092082073854259232947 43105638123110781388849421)
      ·
        refine ⟨16164614296166543020818533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43105638123110781388849421 16164614296166543020818533)
        ·
          refine ⟨3030865180531226816403475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16164614296166543020818533 3030865180531226816403475)
          ·
            refine ⟨4546297770796840224605213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030865180531226816403475 4546297770796840224605213)
            ·
              refine ⟨1704861664048815084226955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4546297770796840224605213 1704861664048815084226955)
              ·
                refine ⟨2557292496073222626340433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704861664048815084226955 2557292496073222626340433)
                ·
                  refine ⟨1917969372054916969755325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2557292496073222626340433 1917969372054916969755325)
                  ·
                    refine ⟨719238514520593863658247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917969372054916969755325 719238514520593863658247)
                    ·
                      rfl

theorem cell22_2101068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_2101068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101068 prefixEnd_2101068 := by exact prefixLift 2101068
  have htrace : WordTrace (prefixWord ++ tailWord_2101068) baseStart_2101068 baseEnd_2101068 := by
    simpa [prefixWord, tailWord_2101068, baseEnd_2101068] using wordTrace_append hprefix tailTrace_2101068
  have hstable : (prefixWord ++ tailWord_2101068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101068).length < 2 ^ (prefixWord ++ tailWord_2101068).sum := by decide
  have hdescent : baseEnd_2101068 < baseStart_2101068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101109 : List Nat := [1, 3, 4, 1, 1, 1, 2, 4, 5]
def baseStart_2101109 : Nat := 118140960795 + 2101109 * 2 ^ 59
def prefixEnd_2101109 : Nat := 4983230072969 + 3 ^ 40 * 2101109 * 2
def baseEnd_2101109 : Nat := 239750849886161141127707

theorem tailTrace_2101109 : CollatzResearch.WordTrace tailWord_2101109 prefixEnd_2101109 239750849886161141127707 := by
  unfold tailWord_2101109
  simp only [CollatzResearch.WordTrace]
  refine ⟨76633740945048408693530381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51089160630032272462353587 76633740945048408693530381)
  ·
    refine ⟨28737652854393153260073893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76633740945048408693530381 28737652854393153260073893)
    ·
      refine ⟨5388309910198716236263855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28737652854393153260073893 5388309910198716236263855)
      ·
        refine ⟨8082464865298074354395783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5388309910198716236263855 8082464865298074354395783)
        ·
          refine ⟨12123697297947111531593675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8082464865298074354395783 12123697297947111531593675)
          ·
            refine ⟨18185545946920667297390513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12123697297947111531593675 18185545946920667297390513)
            ·
              refine ⟨13639159460190500473042885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18185545946920667297390513 13639159460190500473042885)
              ·
                refine ⟨2557342398785718838695541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13639159460190500473042885 2557342398785718838695541)
                ·
                  refine ⟨239750849886161141127707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2557342398785718838695541 239750849886161141127707)
                  ·
                    rfl

theorem cell22_2101109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_2101109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101109 prefixEnd_2101109 := by exact prefixLift 2101109
  have htrace : WordTrace (prefixWord ++ tailWord_2101109) baseStart_2101109 baseEnd_2101109 := by
    simpa [prefixWord, tailWord_2101109, baseEnd_2101109] using wordTrace_append hprefix tailTrace_2101109
  have hstable : (prefixWord ++ tailWord_2101109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101109).length < 2 ^ (prefixWord ++ tailWord_2101109).sum := by decide
  have hdescent : baseEnd_2101109 < baseStart_2101109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101113 : List Nat := [1, 2, 1, 3, 2, 2, 5, 2, 1, 3]
def baseStart_2101113 : Nat := 118140960795 + 2101113 * 2 ^ 59
def prefixEnd_2101113 : Nat := 4983230072969 + 3 ^ 40 * 2101113 * 2
def baseEnd_2101113 : Nat := 719253918940228746283109

theorem tailTrace_2101113 : CollatzResearch.WordTrace tailWord_2101113 prefixEnd_2101113 719253918940228746283109 := by
  unfold tailWord_2101113
  simp only [CollatzResearch.WordTrace]
  refine ⟨76633886837033917376675993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51089257891355944917783995 76633886837033917376675993)
  ·
    refine ⟨57475415127775438032506995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76633886837033917376675993 57475415127775438032506995)
    ·
      refine ⟨86213122691663157048760493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57475415127775438032506995 86213122691663157048760493)
      ·
        refine ⟨32329921009373683893285185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86213122691663157048760493 32329921009373683893285185)
        ·
          refine ⟨24247440757030262919963889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32329921009373683893285185 24247440757030262919963889)
          ·
            refine ⟨18185580567772697189972917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24247440757030262919963889 18185580567772697189972917)
            ·
              refine ⟨1704898178228690361559961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18185580567772697189972917 1704898178228690361559961)
              ·
                refine ⟨1278673633671517771169971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1704898178228690361559961 1278673633671517771169971)
                ·
                  refine ⟨1918010450507276656754957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1278673633671517771169971 1918010450507276656754957)
                  ·
                    refine ⟨719253918940228746283109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1918010450507276656754957 719253918940228746283109)
                    ·
                      rfl

theorem cell22_2101113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 1, 3].length) (baseStart_2101113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101113 prefixEnd_2101113 := by exact prefixLift 2101113
  have htrace : WordTrace (prefixWord ++ tailWord_2101113) baseStart_2101113 baseEnd_2101113 := by
    simpa [prefixWord, tailWord_2101113, baseEnd_2101113] using wordTrace_append hprefix tailTrace_2101113
  have hstable : (prefixWord ++ tailWord_2101113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101113).length < 2 ^ (prefixWord ++ tailWord_2101113).sum := by decide
  have hdescent : baseEnd_2101113 < baseStart_2101113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101137 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 6]
def baseStart_2101137 : Nat := 118140960795 + 2101137 * 2 ^ 59
def prefixEnd_2101137 : Nat := 4983230072969 + 3 ^ 40 * 2101137 * 2
def baseEnd_2101137 : Nat := 239754044876900227894345

theorem tailTrace_2101137 : CollatzResearch.WordTrace tailWord_2101137 prefixEnd_2101137 239754044876900227894345 := by
  unfold tailWord_2101137
  simp only [CollatzResearch.WordTrace]
  refine ⟨76634762188946969475549665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51089841459297979650366443 76634762188946969475549665)
  ·
    refine ⟨57476071641710227106662249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76634762188946969475549665 57476071641710227106662249)
    ·
      refine ⟨43107053731282670329996687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57476071641710227106662249 43107053731282670329996687)
      ·
        refine ⟨64660580596924005494995031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43107053731282670329996687 64660580596924005494995031)
        ·
          refine ⟨96990870895386008242492547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64660580596924005494995031 96990870895386008242492547)
          ·
            refine ⟨145486306343079012363738821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96990870895386008242492547 145486306343079012363738821)
            ·
              refine ⟨27278682439327314818201029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145486306343079012363738821 27278682439327314818201029)
              ·
                refine ⟨5114752957373871528412693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27278682439327314818201029 5114752957373871528412693)
                ·
                  refine ⟨239754044876900227894345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5114752957373871528412693 239754044876900227894345)
                  ·
                    rfl

theorem cell22_2101137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_2101137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101137 prefixEnd_2101137 := by exact prefixLift 2101137
  have htrace : WordTrace (prefixWord ++ tailWord_2101137) baseStart_2101137 baseEnd_2101137 := by
    simpa [prefixWord, tailWord_2101137, baseEnd_2101137] using wordTrace_append hprefix tailTrace_2101137
  have hstable : (prefixWord ++ tailWord_2101137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101137).length < 2 ^ (prefixWord ++ tailWord_2101137).sum := by decide
  have hdescent : baseEnd_2101137 < baseStart_2101137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101199 : List Nat := [1, 1, 2, 1, 1, 5, 5, 6]
def baseStart_2101199 : Nat := 118140960795 + 2101199 * 2 ^ 59
def prefixEnd_2101199 : Nat := 4983230072969 + 3 ^ 40 * 2101199 * 2
def baseEnd_2101199 : Nat := 79920373166417020959205

theorem tailTrace_2101199 : CollatzResearch.WordTrace tailWord_2101199 prefixEnd_2101199 79920373166417020959205 := by
  unfold tailWord_2101199
  simp only [CollatzResearch.WordTrace]
  refine ⟨76637023514722354064306651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51091349009814902709537767 76637023514722354064306651)
  ·
    refine ⟨114955535272083531096459977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76637023514722354064306651 114955535272083531096459977)
    ·
      refine ⟨86216651454062648322344983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114955535272083531096459977 86216651454062648322344983)
      ·
        refine ⟨129324977181093972483517475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86216651454062648322344983 129324977181093972483517475)
        ·
          refine ⟨193987465771640958725276213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129324977181093972483517475 193987465771640958725276213)
          ·
            refine ⟨18186324916091339880494645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193987465771640958725276213 18186324916091339880494645)
            ·
              refine ⟨1704967960883563113796373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18186324916091339880494645 1704967960883563113796373)
              ·
                refine ⟨79920373166417020959205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1704967960883563113796373 79920373166417020959205)
                ·
                  rfl

theorem cell22_2101199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 6].length) (baseStart_2101199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101199 prefixEnd_2101199 := by exact prefixLift 2101199
  have htrace : WordTrace (prefixWord ++ tailWord_2101199) baseStart_2101199 baseEnd_2101199 := by
    simpa [prefixWord, tailWord_2101199, baseEnd_2101199] using wordTrace_append hprefix tailTrace_2101199
  have hstable : (prefixWord ++ tailWord_2101199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101199).length < 2 ^ (prefixWord ++ tailWord_2101199).sum := by decide
  have hdescent : baseEnd_2101199 < baseStart_2101199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101231 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 3, 3]
def baseStart_2101231 : Nat := 118140960795 + 2101231 * 2 ^ 59
def prefixEnd_2101231 : Nat := 4983230072969 + 3 ^ 40 * 2101231 * 2
def baseEnd_2101231 : Nat := 719294312751715771832747

theorem tailTrace_2101231 : CollatzResearch.WordTrace tailWord_2101231 prefixEnd_2101231 719294312751715771832747 := by
  unfold tailWord_2101231
  simp only [CollatzResearch.WordTrace]
  refine ⟨76638190650606423529471547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51092127100404282352981031 76638190650606423529471547)
  ·
    refine ⟨114957285975909635294207321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76638190650606423529471547 114957285975909635294207321)
    ·
      refine ⟨86217964481932226470655491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114957285975909635294207321 86217964481932226470655491)
      ·
        refine ⟨129326946722898339705983237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86217964481932226470655491 129326946722898339705983237)
        ·
          refine ⟨24248802510543438694871857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129326946722898339705983237 24248802510543438694871857)
          ·
            refine ⟨18186601882907579021153893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24248802510543438694871857 18186601882907579021153893)
            ·
              refine ⟨3409987853045171066466355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18186601882907579021153893 3409987853045171066466355)
              ·
                refine ⟨5114981779567756599699533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3409987853045171066466355 5114981779567756599699533)
                ·
                  refine ⟨1918118167337908724887325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5114981779567756599699533 1918118167337908724887325)
                  ·
                    refine ⟨719294312751715771832747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1918118167337908724887325 719294312751715771832747)
                    ·
                      rfl

theorem cell22_2101231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 3].length) (baseStart_2101231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101231 prefixEnd_2101231 := by exact prefixLift 2101231
  have htrace : WordTrace (prefixWord ++ tailWord_2101231) baseStart_2101231 baseEnd_2101231 := by
    simpa [prefixWord, tailWord_2101231, baseEnd_2101231] using wordTrace_append hprefix tailTrace_2101231
  have hstable : (prefixWord ++ tailWord_2101231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101231).length < 2 ^ (prefixWord ++ tailWord_2101231).sum := by decide
  have hdescent : baseEnd_2101231 < baseStart_2101231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101325 : List Nat := [1, 6, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_2101325 : Nat := 118140960795 + 2101325 * 2 ^ 59
def prefixEnd_2101325 : Nat := 4983230072969 + 3 ^ 40 * 2101325 * 2
def baseEnd_2101325 : Nat := 719326490872730859982459

theorem tailTrace_2101325 : CollatzResearch.WordTrace tailWord_2101325 prefixEnd_2101325 719326490872730859982459 := by
  unfold tailWord_2101325
  simp only [CollatzResearch.WordTrace]
  refine ⟨76641619112265877583393429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51094412741510585055595619 76641619112265877583393429)
  ·
    refine ⟨3592575895887463011721567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76641619112265877583393429 3592575895887463011721567)
    ·
      refine ⟨5388863843831194517582351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3592575895887463011721567 5388863843831194517582351)
      ·
        refine ⟨8083295765746791776373527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5388863843831194517582351 8083295765746791776373527)
        ·
          refine ⟨12124943648620187664560291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8083295765746791776373527 12124943648620187664560291)
          ·
            refine ⟨18187415472930281496840437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12124943648620187664560291 18187415472930281496840437)
            ·
              refine ⟨1705070200587213890328791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18187415472930281496840437 1705070200587213890328791)
              ·
                refine ⟨2557605300880820835493187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705070200587213890328791 2557605300880820835493187)
                ·
                  refine ⟨3836407951321231253239781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557605300880820835493187 3836407951321231253239781)
                  ·
                    refine ⟨719326490872730859982459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3836407951321231253239781 719326490872730859982459)
                    ·
                      rfl

theorem cell22_2101325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_2101325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101325 prefixEnd_2101325 := by exact prefixLift 2101325
  have htrace : WordTrace (prefixWord ++ tailWord_2101325) baseStart_2101325 baseEnd_2101325 := by
    simpa [prefixWord, tailWord_2101325, baseEnd_2101325] using wordTrace_append hprefix tailTrace_2101325
  have hstable : (prefixWord ++ tailWord_2101325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101325).length < 2 ^ (prefixWord ++ tailWord_2101325).sum := by decide
  have hdescent : baseEnd_2101325 < baseStart_2101325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101336 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 2, 4]
def baseStart_2101336 : Nat := 118140960795 + 2101336 * 2 ^ 59
def prefixEnd_2101336 : Nat := 4983230072969 + 3 ^ 40 * 2101336 * 2
def baseEnd_2101336 : Nat := 719330256397530497957425

theorem tailTrace_2101336 : CollatzResearch.WordTrace tailWord_2101336 prefixEnd_2101336 719330256397530497957425 := by
  unfold tailWord_2101336
  simp only [CollatzResearch.WordTrace]
  refine ⟨38321010157613013231021931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51094680210150684308029241 38321010157613013231021931)
  ·
    refine ⟨57481515236419519846532897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38321010157613013231021931 57481515236419519846532897)
    ·
      refine ⟨43111136427314639884899673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57481515236419519846532897 43111136427314639884899673)
      ·
        refine ⟨32333352320485979913674755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43111136427314639884899673 32333352320485979913674755)
        ·
          refine ⟨48500028480728969870512133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32333352320485979913674755 48500028480728969870512133)
          ·
            refine ⟨9093755340136681850721025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48500028480728969870512133 9093755340136681850721025)
            ·
              refine ⟨6820316505102511388040769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9093755340136681850721025 6820316505102511388040769)
              ·
                refine ⟨5115237378826883541030577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6820316505102511388040769 5115237378826883541030577)
                ·
                  refine ⟨3836428034120162655772933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5115237378826883541030577 3836428034120162655772933)
                  ·
                    refine ⟨719330256397530497957425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3836428034120162655772933 719330256397530497957425)
                    ·
                      rfl

theorem cell22_2101336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_2101336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101336 prefixEnd_2101336 := by exact prefixLift 2101336
  have htrace : WordTrace (prefixWord ++ tailWord_2101336) baseStart_2101336 baseEnd_2101336 := by
    simpa [prefixWord, tailWord_2101336, baseEnd_2101336] using wordTrace_append hprefix tailTrace_2101336
  have hstable : (prefixWord ++ tailWord_2101336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101336).length < 2 ^ (prefixWord ++ tailWord_2101336).sum := by decide
  have hdescent : baseEnd_2101336 < baseStart_2101336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101338 : List Nat := [3, 1, 1, 2, 1, 1, 6, 2, 2, 3]
def baseStart_2101338 : Nat := 118140960795 + 2101338 * 2 ^ 59
def prefixEnd_2101338 : Nat := 4983230072969 + 3 ^ 40 * 2101338 * 2
def baseEnd_2101338 : Nat := 719330941038403159407419

theorem tailTrace_2101338 : CollatzResearch.WordTrace tailWord_2101338 prefixEnd_2101338 719330941038403159407419 := by
  unfold tailWord_2101338
  simp only [CollatzResearch.WordTrace]
  refine ⟨19160523315304695200904167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51094728840812520535744445 19160523315304695200904167)
  ·
    refine ⟨28740784972957042801356251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19160523315304695200904167 28740784972957042801356251)
    ·
      refine ⟨43111177459435564202034377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28740784972957042801356251 43111177459435564202034377)
      ·
        refine ⟨32333383094576673151525783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43111177459435564202034377 32333383094576673151525783)
        ·
          refine ⟨48500074641865009727288675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32333383094576673151525783 48500074641865009727288675)
          ·
            refine ⟨72750111962797514590933013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48500074641865009727288675 72750111962797514590933013)
            ·
              refine ⟨3410161498256133496449985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72750111962797514590933013 3410161498256133496449985)
              ·
                refine ⟨2557621123692100122337489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3410161498256133496449985 2557621123692100122337489)
                ·
                  refine ⟨1918215842769075091753117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2557621123692100122337489 1918215842769075091753117)
                  ·
                    refine ⟨719330941038403159407419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1918215842769075091753117 719330941038403159407419)
                    ·
                      rfl

theorem cell22_2101338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_2101338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101338 prefixEnd_2101338 := by exact prefixLift 2101338
  have htrace : WordTrace (prefixWord ++ tailWord_2101338) baseStart_2101338 baseEnd_2101338 := by
    simpa [prefixWord, tailWord_2101338, baseEnd_2101338] using wordTrace_append hprefix tailTrace_2101338
  have hstable : (prefixWord ++ tailWord_2101338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101338).length < 2 ^ (prefixWord ++ tailWord_2101338).sum := by decide
  have hdescent : baseEnd_2101338 < baseStart_2101338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101340 : List Nat := [2, 2, 4, 1, 1, 2, 4, 2, 4]
def baseStart_2101340 : Nat := 118140960795 + 2101340 * 2 ^ 59
def prefixEnd_2101340 : Nat := 4983230072969 + 3 ^ 40 * 2101340 * 2
def baseEnd_2101340 : Nat := 239777208559758606952471

theorem tailTrace_2101340 : CollatzResearch.WordTrace tailWord_2101340 prefixEnd_2101340 239777208559758606952471 := by
  unfold tailWord_2101340
  simp only [CollatzResearch.WordTrace]
  refine ⟨38321083103605767572594737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51094777471474356763459649 38321083103605767572594737)
  ·
    refine ⟨28740812327704325679446053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38321083103605767572594737 28740812327704325679446053)
    ·
      refine ⟨5388902311444561064896135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28740812327704325679446053 5388902311444561064896135)
      ·
        refine ⟨8083353467166841597344203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5388902311444561064896135 8083353467166841597344203)
        ·
          refine ⟨12125030200750262396016305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8083353467166841597344203 12125030200750262396016305)
          ·
            refine ⟨9093772650562696797012229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12125030200750262396016305 9093772650562696797012229)
            ·
              refine ⟨1705082371980505649439793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9093772650562696797012229 1705082371980505649439793)
              ·
                refine ⟨1278811778985379237079845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705082371980505649439793 1278811778985379237079845)
                ·
                  refine ⟨239777208559758606952471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278811778985379237079845 239777208559758606952471)
                  ·
                    rfl

theorem cell22_2101340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_2101340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101340 prefixEnd_2101340 := by exact prefixLift 2101340
  have htrace : WordTrace (prefixWord ++ tailWord_2101340) baseStart_2101340 baseEnd_2101340 := by
    simpa [prefixWord, tailWord_2101340, baseEnd_2101340] using wordTrace_append hprefix tailTrace_2101340
  have hstable : (prefixWord ++ tailWord_2101340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101340).length < 2 ^ (prefixWord ++ tailWord_2101340).sum := by decide
  have hdescent : baseEnd_2101340 < baseStart_2101340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101400 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 3, 3]
def baseStart_2101400 : Nat := 118140960795 + 2101400 * 2 ^ 59
def prefixEnd_2101400 : Nat := 4983230072969 + 3 ^ 40 * 2101400 * 2
def baseEnd_2101400 : Nat := 719352164905455664357229

theorem tailTrace_2101400 : CollatzResearch.WordTrace tailWord_2101400 prefixEnd_2101400 719352164905455664357229 := by
  unfold tailWord_2101400
  simp only [CollatzResearch.WordTrace]
  refine ⟨38322177293497082696186827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51096236391329443594915769 38322177293497082696186827)
  ·
    refine ⟨57483265940245624044280241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38322177293497082696186827 57483265940245624044280241)
    ·
      refine ⟨43112449455184218033210181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57483265940245624044280241 43112449455184218033210181)
      ·
        refine ⟨8083584272847040881226909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43112449455184218033210181 8083584272847040881226909)
        ·
          refine ⟨3031344102317640330460091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8083584272847040881226909 3031344102317640330460091)
          ·
            refine ⟨4547016153476460495690137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3031344102317640330460091 4547016153476460495690137)
            ·
              refine ⟨3410262115107345371767603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4547016153476460495690137 3410262115107345371767603)
              ·
                refine ⟨5115393172661018057651405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3410262115107345371767603 5115393172661018057651405)
                ·
                  refine ⟨1918272439747881771619277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5115393172661018057651405 1918272439747881771619277)
                  ·
                    refine ⟨719352164905455664357229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1918272439747881771619277 719352164905455664357229)
                    ·
                      rfl

theorem cell22_2101400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_2101400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101400 prefixEnd_2101400 := by exact prefixLift 2101400
  have htrace : WordTrace (prefixWord ++ tailWord_2101400) baseStart_2101400 baseEnd_2101400 := by
    simpa [prefixWord, tailWord_2101400, baseEnd_2101400] using wordTrace_append hprefix tailTrace_2101400
  have hstable : (prefixWord ++ tailWord_2101400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101400).length < 2 ^ (prefixWord ++ tailWord_2101400).sum := by decide
  have hdescent : baseEnd_2101400 < baseStart_2101400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101413 : List Nat := [1, 3, 1, 2, 1, 3, 5, 1, 5]
def baseStart_2101413 : Nat := 118140960795 + 2101413 * 2 ^ 59
def prefixEnd_2101413 : Nat := 4983230072969 + 3 ^ 40 * 2101413 * 2
def baseEnd_2101413 : Nat := 239785538357042654594063

theorem tailTrace_2101413 : CollatzResearch.WordTrace tailWord_2101413 prefixEnd_2101413 239785538357042654594063 := by
  unfold tailWord_2101413
  simp only [CollatzResearch.WordTrace]
  refine ⟨76644828735947068612596893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51096552490631379075064595 76644828735947068612596893)
  ·
    refine ⟨28741810775980150729723835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76644828735947068612596893 28741810775980150729723835)
    ·
      refine ⟨43112716163970226094585753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28741810775980150729723835 43112716163970226094585753)
      ·
        refine ⟨32334537122977669570939315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43112716163970226094585753 32334537122977669570939315)
        ·
          refine ⟨48501805684466504356408973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32334537122977669570939315 48501805684466504356408973)
          ·
            refine ⟨18188177131674939133653365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48501805684466504356408973 18188177131674939133653365)
            ·
              refine ⟨1705141606094525543780003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18188177131674939133653365 1705141606094525543780003)
              ·
                refine ⟨2557712409141788315670005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705141606094525543780003 2557712409141788315670005)
                ·
                  refine ⟨239785538357042654594063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2557712409141788315670005 239785538357042654594063)
                  ·
                    rfl

theorem cell22_2101413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_2101413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101413 prefixEnd_2101413 := by exact prefixLift 2101413
  have htrace : WordTrace (prefixWord ++ tailWord_2101413) baseStart_2101413 baseEnd_2101413 := by
    simpa [prefixWord, tailWord_2101413, baseEnd_2101413] using wordTrace_append hprefix tailTrace_2101413
  have hstable : (prefixWord ++ tailWord_2101413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101413).length < 2 ^ (prefixWord ++ tailWord_2101413).sum := by decide
  have hdescent : baseEnd_2101413 < baseStart_2101413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101458 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 6]
def baseStart_2101458 : Nat := 118140960795 + 2101458 * 2 ^ 59
def prefixEnd_2101458 : Nat := 4983230072969 + 3 ^ 40 * 2101458 * 2
def baseEnd_2101458 : Nat := 239790673163587615469017

theorem tailTrace_2101458 : CollatzResearch.WordTrace tailWord_2101458 prefixEnd_2101458 239790673163587615469017 := by
  unfold tailWord_2101458
  simp only [CollatzResearch.WordTrace]
  refine ⟨19161617505196010324496257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51097646680522694198656685 19161617505196010324496257)
  ·
    refine ⟨14371213128897007743372193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19161617505196010324496257 14371213128897007743372193)
    ·
      refine ⟨10778409846672755807529145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14371213128897007743372193 10778409846672755807529145)
      ·
        refine ⟨8083807385004566855646859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10778409846672755807529145 8083807385004566855646859)
        ·
          refine ⟨12125711077506850283470289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8083807385004566855646859 12125711077506850283470289)
          ·
            refine ⟨9094283308130137712602717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12125711077506850283470289 9094283308130137712602717)
            ·
              refine ⟨3410356240548801642226019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9094283308130137712602717 3410356240548801642226019)
              ·
                refine ⟨5115534360823202463339029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3410356240548801642226019 5115534360823202463339029)
                ·
                  refine ⟨239790673163587615469017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5115534360823202463339029 239790673163587615469017)
                  ·
                    rfl

theorem cell22_2101458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_2101458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101458 prefixEnd_2101458 := by exact prefixLift 2101458
  have htrace : WordTrace (prefixWord ++ tailWord_2101458) baseStart_2101458 baseEnd_2101458 := by
    simpa [prefixWord, tailWord_2101458, baseEnd_2101458] using wordTrace_append hprefix tailTrace_2101458
  have hstable : (prefixWord ++ tailWord_2101458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101458).length < 2 ^ (prefixWord ++ tailWord_2101458).sum := by decide
  have hdescent : baseEnd_2101458 < baseStart_2101458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101471 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 6, 4]
def baseStart_2101471 : Nat := 118140960795 + 2101471 * 2 ^ 59
def prefixEnd_2101471 : Nat := 4983230072969 + 3 ^ 40 * 2101471 * 2
def baseEnd_2101471 : Nat := 719376469656435145832011

theorem tailTrace_2101471 : CollatzResearch.WordTrace tailWord_2101471 prefixEnd_2101471 719376469656435145832011 := by
  unfold tailWord_2101471
  simp only [CollatzResearch.WordTrace]
  refine ⟨76646944169736944518208267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51097962779824629678805511 76646944169736944518208267)
  ·
    refine ⟨114970416254605416777312401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76646944169736944518208267 114970416254605416777312401)
    ·
      refine ⟨86227812190954062582984301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114970416254605416777312401 86227812190954062582984301)
      ·
        refine ⟨32335429571607773468619113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86227812190954062582984301 32335429571607773468619113)
        ·
          refine ⟨24251572178705830101464335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32335429571607773468619113 24251572178705830101464335)
          ·
            refine ⟨36377358268058745152196503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24251572178705830101464335 36377358268058745152196503)
            ·
              refine ⟨54566037402088117728294755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36377358268058745152196503 54566037402088117728294755)
              ·
                refine ⟨81849056103132176592442133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54566037402088117728294755 81849056103132176592442133)
                ·
                  refine ⟨3836674504834320777770725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81849056103132176592442133 3836674504834320777770725)
                  ·
                    refine ⟨719376469656435145832011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3836674504834320777770725 719376469656435145832011)
                    ·
                      rfl

theorem cell22_2101471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_2101471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101471 prefixEnd_2101471 := by exact prefixLift 2101471
  have htrace : WordTrace (prefixWord ++ tailWord_2101471) baseStart_2101471 baseEnd_2101471 := by
    simpa [prefixWord, tailWord_2101471, baseEnd_2101471] using wordTrace_append hprefix tailTrace_2101471
  have hstable : (prefixWord ++ tailWord_2101471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101471).length < 2 ^ (prefixWord ++ tailWord_2101471).sum := by decide
  have hdescent : baseEnd_2101471 < baseStart_2101471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101516 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_2101516 : Nat := 118140960795 + 2101516 * 2 ^ 59
def prefixEnd_2101516 : Nat := 4983230072969 + 3 ^ 40 * 2101516 * 2
def baseEnd_2101516 : Nat := 719391874076070028456873

theorem tailTrace_2101516 : CollatzResearch.WordTrace tailWord_2101516 prefixEnd_2101516 719391874076070028456873 := by
  unfold tailWord_2101516
  simp only [CollatzResearch.WordTrace]
  refine ⟨38324292727286958601798201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51099056969715944802397601 38324292727286958601798201)
  ·
    refine ⟨28743219545465218951348651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38324292727286958601798201 28743219545465218951348651)
    ·
      refine ⟨43114829318197828427022977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28743219545465218951348651 43114829318197828427022977)
      ·
        refine ⟨32336121988648371320267233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43114829318197828427022977 32336121988648371320267233)
        ·
          refine ⟨24252091491486278490200425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32336121988648371320267233 24252091491486278490200425)
          ·
            refine ⟨18189068618614708867650319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24252091491486278490200425 18189068618614708867650319)
            ·
              refine ⟨27283602927922063301475479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18189068618614708867650319 27283602927922063301475479)
              ·
                refine ⟨40925404391883094952213219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27283602927922063301475479 40925404391883094952213219)
                ·
                  refine ⟨61388106587824642428319829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40925404391883094952213219 61388106587824642428319829)
                  ·
                    refine ⟨719391874076070028456873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61388106587824642428319829 719391874076070028456873)
                    ·
                      rfl

theorem cell22_2101516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_2101516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101516 prefixEnd_2101516 := by exact prefixLift 2101516
  have htrace : WordTrace (prefixWord ++ tailWord_2101516) baseStart_2101516 baseEnd_2101516 := by
    simpa [prefixWord, tailWord_2101516, baseEnd_2101516] using wordTrace_append hprefix tailTrace_2101516
  have hstable : (prefixWord ++ tailWord_2101516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101516).length < 2 ^ (prefixWord ++ tailWord_2101516).sum := by decide
  have hdescent : baseEnd_2101516 < baseStart_2101516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101535 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 3, 3]
def baseStart_2101535 : Nat := 118140960795 + 2101535 * 2 ^ 59
def prefixEnd_2101535 : Nat := 4983230072969 + 3 ^ 40 * 2101535 * 2
def baseEnd_2101535 : Nat := 719398378164360312231815

theorem tailTrace_2101535 : CollatzResearch.WordTrace tailWord_2101535 prefixEnd_2101535 719398378164360312231815 := by
  unfold tailWord_2101535
  simp only [CollatzResearch.WordTrace]
  refine ⟨76649278441505083448538059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51099518961003388965692039 76649278441505083448538059)
  ·
    refine ⟨114973917662257625172807089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76649278441505083448538059 114973917662257625172807089)
    ·
      refine ⟨86230438246693218879605317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114973917662257625172807089 86230438246693218879605317)
      ·
        refine ⟨16168207171254978539925997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86230438246693218879605317 16168207171254978539925997)
        ·
          refine ⟨6063077689220616952472249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16168207171254978539925997 6063077689220616952472249)
          ·
            refine ⟨4547308266915462714354187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6063077689220616952472249 4547308266915462714354187)
            ·
              refine ⟨6820962400373194071531281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4547308266915462714354187 6820962400373194071531281)
              ·
                refine ⟨5115721800279895553648461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6820962400373194071531281 5115721800279895553648461)
                ·
                  refine ⟨1918395675104960832618173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5115721800279895553648461 1918395675104960832618173)
                  ·
                    refine ⟨719398378164360312231815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1918395675104960832618173 719398378164360312231815)
                    ·
                      rfl

theorem cell22_2101535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 3].length) (baseStart_2101535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101535 prefixEnd_2101535 := by exact prefixLift 2101535
  have htrace : WordTrace (prefixWord ++ tailWord_2101535) baseStart_2101535 baseEnd_2101535 := by
    simpa [prefixWord, tailWord_2101535, baseEnd_2101535] using wordTrace_append hprefix tailTrace_2101535
  have hstable : (prefixWord ++ tailWord_2101535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101535).length < 2 ^ (prefixWord ++ tailWord_2101535).sum := by decide
  have hdescent : baseEnd_2101535 < baseStart_2101535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101625 : List Nat := [1, 2, 1, 3, 2, 1, 1, 6, 2, 3]
def baseStart_2101625 : Nat := 118140960795 + 2101625 * 2 ^ 59
def prefixEnd_2101625 : Nat := 4983230072969 + 3 ^ 40 * 2101625 * 2
def baseEnd_2101625 : Nat := 719429187003630077481539

theorem tailTrace_2101625 : CollatzResearch.WordTrace tailWord_2101625 prefixEnd_2101625 719429187003630077481539 := by
  unfold tailWord_2101625
  simp only [CollatzResearch.WordTrace]
  refine ⟨76652561011179028819314329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51101707340786019212876219 76652561011179028819314329)
  ·
    refine ⟨57489420758384271614485747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76652561011179028819314329 57489420758384271614485747)
    ·
      refine ⟨86234131137576407421728621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57489420758384271614485747 86234131137576407421728621)
      ·
        refine ⟨32337799176591152783148233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86234131137576407421728621 32337799176591152783148233)
        ·
          refine ⟨24253349382443364587361175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32337799176591152783148233 24253349382443364587361175)
          ·
            refine ⟨36380024073665046881041763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24253349382443364587361175 36380024073665046881041763)
            ·
              refine ⟨54570036110497570321562645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36380024073665046881041763 54570036110497570321562645)
              ·
                refine ⟨2557970442679573608823249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54570036110497570321562645 2557970442679573608823249)
                ·
                  refine ⟨1918477832009680206617437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2557970442679573608823249 1918477832009680206617437)
                  ·
                    refine ⟨719429187003630077481539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1918477832009680206617437 719429187003630077481539)
                    ·
                      rfl

theorem cell22_2101625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 3].length) (baseStart_2101625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101625 prefixEnd_2101625 := by exact prefixLift 2101625
  have htrace : WordTrace (prefixWord ++ tailWord_2101625) baseStart_2101625 baseEnd_2101625 := by
    simpa [prefixWord, tailWord_2101625, baseEnd_2101625] using wordTrace_append hprefix tailTrace_2101625
  have hstable : (prefixWord ++ tailWord_2101625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101625).length < 2 ^ (prefixWord ++ tailWord_2101625).sum := by decide
  have hdescent : baseEnd_2101625 < baseStart_2101625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101627 : List Nat := [1, 1, 1, 1, 1, 8, 3, 2, 4]
def baseStart_2101627 : Nat := 118140960795 + 2101627 * 2 ^ 59
def prefixEnd_2101627 : Nat := 4983230072969 + 3 ^ 40 * 2101627 * 2
def baseEnd_2101627 : Nat := 239809957214834246310511

theorem tailTrace_2101627 : CollatzResearch.WordTrace tailWord_2101627 prefixEnd_2101627 239809957214834246310511 := by
  unfold tailWord_2101627
  simp only [CollatzResearch.WordTrace]
  refine ⟨76652633957171783160887135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51101755971447855440591423 76652633957171783160887135)
  ·
    refine ⟨114978950935757674741330703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76652633957171783160887135 114978950935757674741330703)
    ·
      refine ⟨172468426403636512111996055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114978950935757674741330703 172468426403636512111996055)
      ·
        refine ⟨258702639605454768167994083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172468426403636512111996055 258702639605454768167994083)
        ·
          refine ⟨388053959408182152251991125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258702639605454768167994083 388053959408182152251991125)
          ·
            refine ⟨4547507336814634596703021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 388053959408182152251991125 4547507336814634596703021)
            ·
              refine ⟨1705315251305487973763633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4547507336814634596703021 1705315251305487973763633)
              ·
                refine ⟨1278986438479115980322725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705315251305487973763633 1278986438479115980322725)
                ·
                  refine ⟨239809957214834246310511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278986438479115980322725 239809957214834246310511)
                  ·
                    rfl

theorem cell22_2101627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 4].length) (baseStart_2101627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101627 prefixEnd_2101627 := by exact prefixLift 2101627
  have htrace : WordTrace (prefixWord ++ tailWord_2101627) baseStart_2101627 baseEnd_2101627 := by
    simpa [prefixWord, tailWord_2101627, baseEnd_2101627] using wordTrace_append hprefix tailTrace_2101627
  have hstable : (prefixWord ++ tailWord_2101627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101627).length < 2 ^ (prefixWord ++ tailWord_2101627).sum := by decide
  have hdescent : baseEnd_2101627 < baseStart_2101627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101728 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 8]
def baseStart_2101728 : Nat := 118140960795 + 2101728 * 2 ^ 59
def prefixEnd_2101728 : Nat := 4983230072969 + 3 ^ 40 * 2101728 * 2
def baseEnd_2101728 : Nat := 239821482002857380718741

theorem tailTrace_2101728 : CollatzResearch.WordTrace tailWord_2101728 prefixEnd_2101728 239821482002857380718741 := by
  unfold tailWord_2101728
  simp only [CollatzResearch.WordTrace]
  refine ⟨38328158864902938705156919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51104211819870584940209225 38328158864902938705156919)
  ·
    refine ⟨57492238297354408057735379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38328158864902938705156919 57492238297354408057735379)
    ·
      refine ⟨86238357446031612086603069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57492238297354408057735379 86238357446031612086603069)
      ·
        refine ⟨32339384042261854532476151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86238357446031612086603069 32339384042261854532476151)
        ·
          refine ⟨48509076063392781798714227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32339384042261854532476151 48509076063392781798714227)
          ·
            refine ⟨72763614095089172698071341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48509076063392781798714227 72763614095089172698071341)
            ·
              refine ⟨27286355285658439761776753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72763614095089172698071341 27286355285658439761776753)
              ·
                refine ⟨20464766464243829821332565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27286355285658439761776753 20464766464243829821332565)
                ·
                  refine ⟨239821482002857380718741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20464766464243829821332565 239821482002857380718741)
                  ·
                    rfl

theorem cell22_2101728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_2101728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101728 prefixEnd_2101728 := by exact prefixLift 2101728
  have htrace : WordTrace (prefixWord ++ tailWord_2101728) baseStart_2101728 baseEnd_2101728 := by
    simpa [prefixWord, tailWord_2101728, baseEnd_2101728] using wordTrace_append hprefix tailTrace_2101728
  have hstable : (prefixWord ++ tailWord_2101728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101728).length < 2 ^ (prefixWord ++ tailWord_2101728).sum := by decide
  have hdescent : baseEnd_2101728 < baseStart_2101728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101745 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 6]
def baseStart_2101745 : Nat := 118140960795 + 2101745 * 2 ^ 59
def prefixEnd_2101745 : Nat := 4983230072969 + 3 ^ 40 * 2101745 * 2
def baseEnd_2101745 : Nat := 239823421818663254827057

theorem tailTrace_2101745 : CollatzResearch.WordTrace tailWord_2101745 prefixEnd_2101745 239823421818663254827057 := by
  unfold tailWord_2101745
  simp only [CollatzResearch.WordTrace]
  refine ⟨76656937770744289313682689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51104625180496192875788459 76656937770744289313682689)
  ·
    refine ⟨57492703328058216985262017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76656937770744289313682689 57492703328058216985262017)
    ·
      refine ⟨43119527496043662738946513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57492703328058216985262017 43119527496043662738946513)
      ·
        refine ⟨32339645622032747054209885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43119527496043662738946513 32339645622032747054209885)
        ·
          refine ⟨12127367108262280145328707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32339645622032747054209885 12127367108262280145328707)
          ·
            refine ⟨18191050662393420217993061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12127367108262280145328707 18191050662393420217993061)
            ·
              refine ⟨3410821999198766290873699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18191050662393420217993061 3410821999198766290873699)
              ·
                refine ⟨5116232998798149436310549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3410821999198766290873699 5116232998798149436310549)
                ·
                  refine ⟨239823421818663254827057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5116232998798149436310549 239823421818663254827057)
                  ·
                    rfl

theorem cell22_2101745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_2101745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101745 prefixEnd_2101745 := by exact prefixLift 2101745
  have htrace : WordTrace (prefixWord ++ tailWord_2101745) baseStart_2101745 baseEnd_2101745 := by
    simpa [prefixWord, tailWord_2101745, baseEnd_2101745] using wordTrace_append hprefix tailTrace_2101745
  have hstable : (prefixWord ++ tailWord_2101745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101745).length < 2 ^ (prefixWord ++ tailWord_2101745).sum := by decide
  have hdescent : baseEnd_2101745 < baseStart_2101745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101764 : List Nat := [2, 3, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_2101764 : Nat := 118140960795 + 2101764 * 2 ^ 59
def prefixEnd_2101764 : Nat := 4983230072969 + 3 ^ 40 * 2101764 * 2
def baseEnd_2101764 : Nat := 719476769544280048256113

theorem tailTrace_2101764 : CollatzResearch.WordTrace tailWord_2101764 prefixEnd_2101764 719476769544280048256113 := by
  unfold tailWord_2101764
  simp only [CollatzResearch.WordTrace]
  refine ⟨38328815378837727779312173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51105087171783637039082897 38328815378837727779312173)
  ·
    refine ⟨14373305767064147917242065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38328815378837727779312173 14373305767064147917242065)
    ·
      refine ⟨10779979325298110937931549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14373305767064147917242065 10779979325298110937931549)
      ·
        refine ⟨4042492246986791601724331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10779979325298110937931549 4042492246986791601724331)
        ·
          refine ⟨6063738370480187402586497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4042492246986791601724331 6063738370480187402586497)
          ·
            refine ⟨4547803777860140551939873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6063738370480187402586497 4547803777860140551939873)
            ·
              refine ⟨3410852833395105413954905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4547803777860140551939873 3410852833395105413954905)
              ·
                refine ⟨2558139625046329060466179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3410852833395105413954905 2558139625046329060466179)
                ·
                  refine ⟨3837209437569493590699269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558139625046329060466179 3837209437569493590699269)
                  ·
                    refine ⟨719476769544280048256113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3837209437569493590699269 719476769544280048256113)
                    ·
                      rfl

theorem cell22_2101764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_2101764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101764 prefixEnd_2101764 := by exact prefixLift 2101764
  have htrace : WordTrace (prefixWord ++ tailWord_2101764) baseStart_2101764 baseEnd_2101764 := by
    simpa [prefixWord, tailWord_2101764, baseEnd_2101764] using wordTrace_append hprefix tailTrace_2101764
  have hstable : (prefixWord ++ tailWord_2101764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101764).length < 2 ^ (prefixWord ++ tailWord_2101764).sum := by decide
  have hdescent : baseEnd_2101764 < baseStart_2101764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101796 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 6]
def baseStart_2101796 : Nat := 118140960795 + 2101796 * 2 ^ 59
def prefixEnd_2101796 : Nat := 4983230072969 + 3 ^ 40 * 2101796 * 2
def baseEnd_2101796 : Nat := 239829241266080877152005

theorem tailTrace_2101796 : CollatzResearch.WordTrace tailWord_2101796 prefixEnd_2101796 239829241266080877152005 := by
  unfold tailWord_2101796
  simp only [CollatzResearch.WordTrace]
  refine ⟨38329398946779762511894621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51105865262373016682526161 38329398946779762511894621)
  ·
    refine ⟨14373524605042410941960483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38329398946779762511894621 14373524605042410941960483)
    ·
      refine ⟨21560286907563616412940725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14373524605042410941960483 21560286907563616412940725)
      ·
        refine ⟨2021276897584089038713193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21560286907563616412940725 2021276897584089038713193)
        ·
          refine ⟨1515957673188066779034895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2021276897584089038713193 1515957673188066779034895)
          ·
            refine ⟨2273936509782100168552343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515957673188066779034895 2273936509782100168552343)
            ·
              refine ⟨3410904764673150252828515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273936509782100168552343 3410904764673150252828515)
              ·
                refine ⟨5116357147009725379242773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3410904764673150252828515 5116357147009725379242773)
                ·
                  refine ⟨239829241266080877152005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5116357147009725379242773 239829241266080877152005)
                  ·
                    rfl

theorem cell22_2101796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_2101796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101796 prefixEnd_2101796 := by exact prefixLift 2101796
  have htrace : WordTrace (prefixWord ++ tailWord_2101796) baseStart_2101796 baseEnd_2101796 := by
    simpa [prefixWord, tailWord_2101796, baseEnd_2101796] using wordTrace_append hprefix tailTrace_2101796
  have hstable : (prefixWord ++ tailWord_2101796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101796).length < 2 ^ (prefixWord ++ tailWord_2101796).sum := by decide
  have hdescent : baseEnd_2101796 < baseStart_2101796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101856 : List Nat := [2, 1, 1, 3, 2, 1, 6, 2, 1, 3]
def baseStart_2101856 : Nat := 118140960795 + 2101856 * 2 ^ 59
def prefixEnd_2101856 : Nat := 4983230072969 + 3 ^ 40 * 2101856 * 2
def baseEnd_2101856 : Nat := 719508263024422474955831

theorem tailTrace_2101856 : CollatzResearch.WordTrace tailWord_2101856 prefixEnd_2101856 719508263024422474955831 := by
  unfold tailWord_2101856
  simp only [CollatzResearch.WordTrace]
  refine ⟨38330493136671077635486711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51107324182228103513982281 38330493136671077635486711)
  ·
    refine ⟨57495739705006616453230067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38330493136671077635486711 57495739705006616453230067)
    ·
      refine ⟨86243609557509924679845101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57495739705006616453230067 86243609557509924679845101)
      ·
        refine ⟨32341353584066221754941913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86243609557509924679845101 32341353584066221754941913)
        ·
          refine ⟨24256015188049666316206435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32341353584066221754941913 24256015188049666316206435)
          ·
            refine ⟨36384022782074499474309653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24256015188049666316206435 36384022782074499474309653)
            ·
              refine ⟨1705501067909742162858265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36384022782074499474309653 1705501067909742162858265)
              ·
                refine ⟨1279125800932306622143699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705501067909742162858265 1279125800932306622143699)
                ·
                  refine ⟨1918688701398459933215549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279125800932306622143699 1918688701398459933215549)
                  ·
                    refine ⟨719508263024422474955831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1918688701398459933215549 719508263024422474955831)
                    ·
                      rfl

theorem cell22_2101856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 1, 3].length) (baseStart_2101856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101856 prefixEnd_2101856 := by exact prefixLift 2101856
  have htrace : WordTrace (prefixWord ++ tailWord_2101856) baseStart_2101856 baseEnd_2101856 := by
    simpa [prefixWord, tailWord_2101856, baseEnd_2101856] using wordTrace_append hprefix tailTrace_2101856
  have hstable : (prefixWord ++ tailWord_2101856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101856).length < 2 ^ (prefixWord ++ tailWord_2101856).sum := by decide
  have hdescent : baseEnd_2101856 < baseStart_2101856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101880 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 6]
def baseStart_2101880 : Nat := 118140960795 + 2101880 * 2 ^ 59
def prefixEnd_2101880 : Nat := 4983230072969 + 3 ^ 40 * 2101880 * 2
def baseEnd_2101880 : Nat := 239838826238298137451919

theorem tailTrace_2101880 : CollatzResearch.WordTrace tailWord_2101880 prefixEnd_2101880 239838826238298137451919 := by
  unfold tailWord_2101880
  simp only [CollatzResearch.WordTrace]
  refine ⟨38330930812627603684923547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51107907750170138246564729 38330930812627603684923547)
  ·
    refine ⟨57496396218941405527385321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38330930812627603684923547 57496396218941405527385321)
    ·
      refine ⟨43122297164206054145538991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57496396218941405527385321 43122297164206054145538991)
      ·
        refine ⟨64683445746309081218308487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43122297164206054145538991 64683445746309081218308487)
        ·
          refine ⟨97025168619463621827462731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64683445746309081218308487 97025168619463621827462731)
          ·
            refine ⟨145537752929195432741194097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97025168619463621827462731 145537752929195432741194097)
            ·
              refine ⟨109153314696896574555895573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145537752929195432741194097 109153314696896574555895573)
              ·
                refine ⟨5116561626417026932307605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109153314696896574555895573 5116561626417026932307605)
                ·
                  refine ⟨239838826238298137451919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5116561626417026932307605 239838826238298137451919)
                  ·
                    rfl

theorem cell22_2101880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_2101880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101880 prefixEnd_2101880 := by exact prefixLift 2101880
  have htrace : WordTrace (prefixWord ++ tailWord_2101880) baseStart_2101880 baseEnd_2101880 := by
    simpa [prefixWord, tailWord_2101880, baseEnd_2101880] using wordTrace_append hprefix tailTrace_2101880
  have hstable : (prefixWord ++ tailWord_2101880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101880).length < 2 ^ (prefixWord ++ tailWord_2101880).sum := by decide
  have hdescent : baseEnd_2101880 < baseStart_2101880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101925 : List Nat := [1, 3, 1, 2, 1, 2, 1, 11]
def baseStart_2101925 : Nat := 118140960795 + 2101925 * 2 ^ 59
def prefixEnd_2101925 : Nat := 4983230072969 + 3 ^ 40 * 2101925 * 2
def baseEnd_2101925 : Nat := 79947987014947699442291

theorem tailTrace_2101925 : CollatzResearch.WordTrace tailWord_2101925 prefixEnd_2101925 79947987014947699442291 := by
  unfold tailWord_2101925
  simp only [CollatzResearch.WordTrace]
  refine ⟨76663502910092180055235229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51109001940061453370156819 76663502910092180055235229)
  ·
    refine ⟨28748813591284567520713211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76663502910092180055235229 28748813591284567520713211)
    ·
      refine ⟨43123220386926851281069817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28748813591284567520713211 43123220386926851281069817)
      ·
        refine ⟨32342415290195138460802363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43123220386926851281069817 32342415290195138460802363)
        ·
          refine ⟨48513622935292707691203545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32342415290195138460802363 48513622935292707691203545)
          ·
            refine ⟨36385217201469530768402659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48513622935292707691203545 36385217201469530768402659)
            ·
              refine ⟨54577825802204296152603989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36385217201469530768402659 54577825802204296152603989)
              ·
                refine ⟨79947987014947699442291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 54577825802204296152603989 79947987014947699442291)
                ·
                  rfl

theorem cell22_2101925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 11].length) (baseStart_2101925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101925 prefixEnd_2101925 := by exact prefixLift 2101925
  have htrace : WordTrace (prefixWord ++ tailWord_2101925) baseStart_2101925 baseEnd_2101925 := by
    simpa [prefixWord, tailWord_2101925, baseEnd_2101925] using wordTrace_append hprefix tailTrace_2101925
  have hstable : (prefixWord ++ tailWord_2101925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101925).length < 2 ^ (prefixWord ++ tailWord_2101925).sum := by decide
  have hdescent : baseEnd_2101925 < baseStart_2101925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101965 : List Nat := [1, 6, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2101965 : Nat := 118140960795 + 2101965 * 2 ^ 59
def prefixEnd_2101965 : Nat := 4983230072969 + 3 ^ 40 * 2101965 * 2
def baseEnd_2101965 : Nat := 239848525317327507993499

theorem tailTrace_2101965 : CollatzResearch.WordTrace tailWord_2101965 prefixEnd_2101965 239848525317327507993499 := by
  unfold tailWord_2101965
  simp only [CollatzResearch.WordTrace]
  refine ⟨76664961829947266886691349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51109974553298177924460899 76664961829947266886691349)
  ·
    refine ⟨3593670085778778135313657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76664961829947266886691349 3593670085778778135313657)
    ·
      refine ⟨2695252564334083601485243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3593670085778778135313657 2695252564334083601485243)
      ·
        refine ⟨4042878846501125402227865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2695252564334083601485243 4042878846501125402227865)
        ·
          refine ⟨3032159134875844051670899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4042878846501125402227865 3032159134875844051670899)
          ·
            refine ⟨4548238702313766077506349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3032159134875844051670899 4548238702313766077506349)
            ·
              refine ⟨1705589513367662279064881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4548238702313766077506349 1705589513367662279064881)
              ·
                refine ⟨1279192135025746709298661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705589513367662279064881 1279192135025746709298661)
                ·
                  refine ⟨239848525317327507993499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1279192135025746709298661 239848525317327507993499)
                  ·
                    rfl

theorem cell22_2101965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2101965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101965 prefixEnd_2101965 := by exact prefixLift 2101965
  have htrace : WordTrace (prefixWord ++ tailWord_2101965) baseStart_2101965 baseEnd_2101965 := by
    simpa [prefixWord, tailWord_2101965, baseEnd_2101965] using wordTrace_append hprefix tailTrace_2101965
  have hstable : (prefixWord ++ tailWord_2101965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101965).length < 2 ^ (prefixWord ++ tailWord_2101965).sum := by decide
  have hdescent : baseEnd_2101965 < baseStart_2101965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2101980 : List Nat := [2, 2, 5, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2101980 : Nat := 118140960795 + 2101980 * 2 ^ 59
def prefixEnd_2101980 : Nat := 4983230072969 + 3 ^ 40 * 2101980 * 2
def baseEnd_2101980 : Nat := 719550710758527484855451

theorem tailTrace_2101980 : CollatzResearch.WordTrace tailWord_2101980 prefixEnd_2101980 719550710758527484855451 := by
  unfold tailWord_2101980
  simp only [CollatzResearch.WordTrace]
  refine ⟨38332754462446462224243697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51110339283261949632324929 38332754462446462224243697)
  ·
    refine ⟨28749565846834846668182773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38332754462446462224243697 28749565846834846668182773)
    ·
      refine ⟨2695271798140766875142135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28749565846834846668182773 2695271798140766875142135)
      ·
        refine ⟨4042907697211150312713203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2695271798140766875142135 4042907697211150312713203)
        ·
          refine ⟨6064361545816725469069805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4042907697211150312713203 6064361545816725469069805)
          ·
            refine ⟨2274135579681272050901177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6064361545816725469069805 2274135579681272050901177)
            ·
              refine ⟨1705601684760954038175883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2274135579681272050901177 1705601684760954038175883)
              ·
                refine ⟨2558402527141431057263825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705601684760954038175883 2558402527141431057263825)
                ·
                  refine ⟨1918801895356073292947869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2558402527141431057263825 1918801895356073292947869)
                  ·
                    refine ⟨719550710758527484855451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1918801895356073292947869 719550710758527484855451)
                    ·
                      rfl

theorem cell22_2101980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2101980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2101980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2101980 prefixEnd_2101980 := by exact prefixLift 2101980
  have htrace : WordTrace (prefixWord ++ tailWord_2101980) baseStart_2101980 baseEnd_2101980 := by
    simpa [prefixWord, tailWord_2101980, baseEnd_2101980] using wordTrace_append hprefix tailTrace_2101980
  have hstable : (prefixWord ++ tailWord_2101980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2101980).length < 2 ^ (prefixWord ++ tailWord_2101980).sum := by decide
  have hdescent : baseEnd_2101980 < baseStart_2101980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2101980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102066 : List Nat := [3, 2, 1, 1, 3, 1, 4, 3, 4]
def baseStart_2102066 : Nat := 118140960795 + 2102066 * 2 ^ 59
def prefixEnd_2102066 : Nat := 4983230072969 + 3 ^ 40 * 2102066 * 2
def baseEnd_2102066 : Nat := 239860050105350642401729

theorem tailTrace_2102066 : CollatzResearch.WordTrace tailWord_2102066 prefixEnd_2102066 239860050105350642401729 := by
  unfold tailWord_2102066
  simp only [CollatzResearch.WordTrace]
  refine ⟨19167161400645340284029513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51112430401720907424078701 19167161400645340284029513)
  ·
    refine ⟨14375371050484005213022135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19167161400645340284029513 14375371050484005213022135)
    ·
      refine ⟨21563056575726007819533203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14375371050484005213022135 21563056575726007819533203)
      ·
        refine ⟨32344584863589011729299805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21563056575726007819533203 32344584863589011729299805)
        ·
          refine ⟨12129219323845879398487427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32344584863589011729299805 12129219323845879398487427)
          ·
            refine ⟨18193828985768819097731141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12129219323845879398487427 18193828985768819097731141)
            ·
              refine ⟨3411342934831653580824589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18193828985768819097731141 3411342934831653580824589)
              ·
                refine ⟨1279253600561870092809221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3411342934831653580824589 1279253600561870092809221)
                ·
                  refine ⟨239860050105350642401729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1279253600561870092809221 239860050105350642401729)
                  ·
                    rfl

theorem cell22_2102066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_2102066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102066 prefixEnd_2102066 := by exact prefixLift 2102066
  have htrace : WordTrace (prefixWord ++ tailWord_2102066) baseStart_2102066 baseEnd_2102066 := by
    simpa [prefixWord, tailWord_2102066, baseEnd_2102066] using wordTrace_append hprefix tailTrace_2102066
  have hstable : (prefixWord ++ tailWord_2102066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102066).length < 2 ^ (prefixWord ++ tailWord_2102066).sum := by decide
  have hdescent : baseEnd_2102066 < baseStart_2102066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102068 : List Nat := [2, 5, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2102068 : Nat := 118140960795 + 2102068 * 2 ^ 59
def prefixEnd_2102068 : Nat := 4983230072969 + 3 ^ 40 * 2102068 * 2
def baseEnd_2102068 : Nat := 719580834956924588655181

theorem tailTrace_2102068 : CollatzResearch.WordTrace tailWord_2102068 prefixEnd_2102068 719580834956924588655181 := by
  unfold tailWord_2102068
  simp only [CollatzResearch.WordTrace]
  refine ⟨38334359274287057738845429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51112479032382743651793905 38334359274287057738845429)
  ·
    refine ⟨3593846181964411663016759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38334359274287057738845429 3593846181964411663016759)
    ·
      refine ⟨5390769272946617494525139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3593846181964411663016759 5390769272946617494525139)
      ·
        refine ⟨8086153909419926241787709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5390769272946617494525139 8086153909419926241787709)
        ·
          refine ⟨3032307716032472340670391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8086153909419926241787709 3032307716032472340670391)
          ·
            refine ⟨4548461574048708511005587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3032307716032472340670391 4548461574048708511005587)
            ·
              refine ⟨6822692361073062766508381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4548461574048708511005587 6822692361073062766508381)
              ·
                refine ⟨2558509635402398537440643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6822692361073062766508381 2558509635402398537440643)
                ·
                  refine ⟨3837764453103597806160965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558509635402398537440643 3837764453103597806160965)
                  ·
                    refine ⟨719580834956924588655181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3837764453103597806160965 719580834956924588655181)
                    ·
                      rfl

theorem cell22_2102068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2102068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102068 prefixEnd_2102068 := by exact prefixLift 2102068
  have htrace : WordTrace (prefixWord ++ tailWord_2102068) baseStart_2102068 baseEnd_2102068 := by
    simpa [prefixWord, tailWord_2102068, baseEnd_2102068] using wordTrace_append hprefix tailTrace_2102068
  have hstable : (prefixWord ++ tailWord_2102068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102068).length < 2 ^ (prefixWord ++ tailWord_2102068).sum := by decide
  have hdescent : baseEnd_2102068 < baseStart_2102068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102098 : List Nat := [3, 2, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_2102098 : Nat := 118140960795 + 2102098 * 2 ^ 59
def prefixEnd_2102098 : Nat := 4983230072969 + 3 ^ 40 * 2102098 * 2
def baseEnd_2102098 : Nat := 719591104570014510405089

theorem tailTrace_2102098 : CollatzResearch.WordTrace tailWord_2102098 prefixEnd_2102098 719591104570014510405089 := by
  unfold tailWord_2102098
  simp only [CollatzResearch.WordTrace]
  refine ⟨19167453184616357650320737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51113208492310287067521965 19167453184616357650320737)
  ·
    refine ⟨14375589888462268237740553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19167453184616357650320737 14375589888462268237740553)
    ·
      refine ⟨10781692416346701178305415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14375589888462268237740553 10781692416346701178305415)
      ·
        refine ⟨16172538624520051767458123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10781692416346701178305415 16172538624520051767458123)
        ·
          refine ⟨24258807936780077651187185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16172538624520051767458123 24258807936780077651187185)
          ·
            refine ⟨18194105952585058238390389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24258807936780077651187185 18194105952585058238390389)
            ·
              refine ⟨1705697433054849209849099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18194105952585058238390389 1705697433054849209849099)
              ·
                refine ⟨2558546149582273814773649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705697433054849209849099 2558546149582273814773649)
                ·
                  refine ⟨1918909612186705361080237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2558546149582273814773649 1918909612186705361080237)
                  ·
                    refine ⟨719591104570014510405089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1918909612186705361080237 719591104570014510405089)
                    ·
                      rfl

theorem cell22_2102098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_2102098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102098 prefixEnd_2102098 := by exact prefixLift 2102098
  have htrace : WordTrace (prefixWord ++ tailWord_2102098) baseStart_2102098 baseEnd_2102098 := by
    simpa [prefixWord, tailWord_2102098, baseEnd_2102098] using wordTrace_append hprefix tailTrace_2102098
  have hstable : (prefixWord ++ tailWord_2102098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102098).length < 2 ^ (prefixWord ++ tailWord_2102098).sum := by decide
  have hdescent : baseEnd_2102098 < baseStart_2102098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102156 : List Nat := [2, 2, 1, 2, 1, 2, 6, 1, 5]
def baseStart_2102156 : Nat := 118140960795 + 2102156 * 2 ^ 59
def prefixEnd_2102156 : Nat := 4983230072969 + 3 ^ 40 * 2102156 * 2
def baseEnd_2102156 : Nat := 239870319718440564151637

theorem tailTrace_2102156 : CollatzResearch.WordTrace tailWord_2102156 prefixEnd_2102156 239870319718440564151637 := by
  unfold tailWord_2102156
  simp only [CollatzResearch.WordTrace]
  refine ⟨38335964086127653253447161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51114618781503537671262881 38335964086127653253447161)
  ·
    refine ⟨28751973064595739940085371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38335964086127653253447161 28751973064595739940085371)
    ·
      refine ⟨43127959596893609910128057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28751973064595739940085371 43127959596893609910128057)
      ·
        refine ⟨32345969697670207432596043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43127959596893609910128057 32345969697670207432596043)
        ·
          refine ⟨48518954546505311148894065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32345969697670207432596043 48518954546505311148894065)
          ·
            refine ⟨36389215909878983361670549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48518954546505311148894065 36389215909878983361670549)
            ·
              refine ⟨1705744495775577345078307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36389215909878983361670549 1705744495775577345078307)
              ·
                refine ⟨2558616743663366017617461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705744495775577345078307 2558616743663366017617461)
                ·
                  refine ⟨239870319718440564151637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2558616743663366017617461 239870319718440564151637)
                  ·
                    rfl

theorem cell22_2102156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_2102156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102156 prefixEnd_2102156 := by exact prefixLift 2102156
  have htrace : WordTrace (prefixWord ++ tailWord_2102156) baseStart_2102156 baseEnd_2102156 := by
    simpa [prefixWord, tailWord_2102156, baseEnd_2102156] using wordTrace_append hprefix tailTrace_2102156
  have hstable : (prefixWord ++ tailWord_2102156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102156).length < 2 ^ (prefixWord ++ tailWord_2102156).sum := by decide
  have hdescent : baseEnd_2102156 < baseStart_2102156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102250 : List Nat := [3, 1, 3, 1, 2, 4, 1, 2, 2, 3]
def baseStart_2102250 : Nat := 118140960795 + 2102250 * 2 ^ 59
def prefixEnd_2102250 : Nat := 4983230072969 + 3 ^ 40 * 2102250 * 2
def baseEnd_2102250 : Nat := 719643137276336780604623

theorem tailTrace_2102250 : CollatzResearch.WordTrace tailWord_2102250 prefixEnd_2102250 719643137276336780604623 := by
  unfold tailWord_2102250
  simp only [CollatzResearch.WordTrace]
  refine ⟨19168839158478690140204051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51116904422609840373877469 19168839158478690140204051)
  ·
    refine ⟨28753258737718035210306077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19168839158478690140204051 28753258737718035210306077)
    ·
      refine ⟨10782472026644263203864779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28753258737718035210306077 10782472026644263203864779)
      ·
        refine ⟨16173708039966394805797169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10782472026644263203864779 16173708039966394805797169)
        ·
          refine ⟨12130281029974796104347877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16173708039966394805797169 12130281029974796104347877)
          ·
            refine ⟨2274427693120274269565227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12130281029974796104347877 2274427693120274269565227)
            ·
              refine ⟨3411641539680411404347841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2274427693120274269565227 3411641539680411404347841)
              ·
                refine ⟨2558731154760308553260881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3411641539680411404347841 2558731154760308553260881)
                ·
                  refine ⟨1919048366070231414945661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2558731154760308553260881 1919048366070231414945661)
                  ·
                    refine ⟨719643137276336780604623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1919048366070231414945661 719643137276336780604623)
                    ·
                      rfl

theorem cell22_2102250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_2102250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102250 prefixEnd_2102250 := by exact prefixLift 2102250
  have htrace : WordTrace (prefixWord ++ tailWord_2102250) baseStart_2102250 baseEnd_2102250 := by
    simpa [prefixWord, tailWord_2102250, baseEnd_2102250] using wordTrace_append hprefix tailTrace_2102250
  have hstable : (prefixWord ++ tailWord_2102250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102250).length < 2 ^ (prefixWord ++ tailWord_2102250).sum := by decide
  have hdescent : baseEnd_2102250 < baseStart_2102250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102289 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 1, 7]
def baseStart_2102289 : Nat := 118140960795 + 2102289 * 2 ^ 59
def prefixEnd_2102289 : Nat := 4983230072969 + 3 ^ 40 * 2102289 * 2
def baseEnd_2102289 : Nat := 719656487773353678879503

theorem tailTrace_2102289 : CollatzResearch.WordTrace tailWord_2102289 prefixEnd_2102289 719656487773353678879503 := by
  unfold tailWord_2102289
  simp only [CollatzResearch.WordTrace]
  refine ⟨76676779080773470221485921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51117852720515646814323947 76676779080773470221485921)
  ·
    refine ⟨57507584310580102666114441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76676779080773470221485921 57507584310580102666114441)
    ·
      refine ⟨43130688232935076999585831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57507584310580102666114441 43130688232935076999585831)
      ·
        refine ⟨64696032349402615499378747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43130688232935076999585831 64696032349402615499378747)
        ·
          refine ⟨97044048524103923249068121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64696032349402615499378747 97044048524103923249068121)
          ·
            refine ⟨72783036393077942436801091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97044048524103923249068121 72783036393077942436801091)
            ·
              refine ⟨109174554589616913655201637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72783036393077942436801091 109174554589616913655201637)
              ·
                refine ⟨20470228985553171310350307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109174554589616913655201637 20470228985553171310350307)
                ·
                  refine ⟨30705343478329756965525461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20470228985553171310350307 30705343478329756965525461)
                  ·
                    refine ⟨719656487773353678879503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30705343478329756965525461 719656487773353678879503)
                    ·
                      rfl

theorem cell22_2102289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_2102289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102289 prefixEnd_2102289 := by exact prefixLift 2102289
  have htrace : WordTrace (prefixWord ++ tailWord_2102289) baseStart_2102289 baseEnd_2102289 := by
    simpa [prefixWord, tailWord_2102289, baseEnd_2102289] using wordTrace_append hprefix tailTrace_2102289
  have hstable : (prefixWord ++ tailWord_2102289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102289).length < 2 ^ (prefixWord ++ tailWord_2102289).sum := by decide
  have hdescent : baseEnd_2102289 < baseStart_2102289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102321 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 3, 4]
def baseStart_2102321 : Nat := 118140960795 + 2102321 * 2 ^ 59
def prefixEnd_2102321 : Nat := 4983230072969 + 3 ^ 40 * 2102321 * 2
def baseEnd_2102321 : Nat := 719667442027316262079405

theorem tailTrace_2102321 : CollatzResearch.WordTrace tailWord_2102321 prefixEnd_2102321 719667442027316262079405 := by
  unfold tailWord_2102321
  simp only [CollatzResearch.WordTrace]
  refine ⟨76677946216657539686650817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51118630811105026457767211 76677946216657539686650817)
  ·
    refine ⟨57508459662493154764988113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76677946216657539686650817 57508459662493154764988113)
    ·
      refine ⟨43131344746869866073741085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57508459662493154764988113 43131344746869866073741085)
      ·
        refine ⟨16174254280076199777652907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43131344746869866073741085 16174254280076199777652907)
        ·
          refine ⟨24261381420114299666479361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16174254280076199777652907 24261381420114299666479361)
          ·
            refine ⟨18196036065085724749859521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24261381420114299666479361 18196036065085724749859521)
            ·
              refine ⟨13647027048814293562394641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18196036065085724749859521 13647027048814293562394641)
              ·
                refine ⟨10235270286610720171795981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13647027048814293562394641 10235270286610720171795981)
                ·
                  refine ⟨3838226357479020064423493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10235270286610720171795981 3838226357479020064423493)
                  ·
                    refine ⟨719667442027316262079405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3838226357479020064423493 719667442027316262079405)
                    ·
                      rfl

theorem cell22_2102321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_2102321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102321 prefixEnd_2102321 := by exact prefixLift 2102321
  have htrace : WordTrace (prefixWord ++ tailWord_2102321) baseStart_2102321 baseEnd_2102321 := by
    simpa [prefixWord, tailWord_2102321, baseEnd_2102321] using wordTrace_append hprefix tailTrace_2102321
  have hstable : (prefixWord ++ tailWord_2102321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102321).length < 2 ^ (prefixWord ++ tailWord_2102321).sum := by decide
  have hdescent : baseEnd_2102321 < baseStart_2102321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102464 : List Nat := [2, 1, 1, 2, 6, 2, 1, 3, 1, 3]
def baseStart_2102464 : Nat := 118140960795 + 2102464 * 2 ^ 59
def prefixEnd_2102464 : Nat := 4983230072969 + 3 ^ 40 * 2102464 * 2
def baseEnd_2102464 : Nat := 719716393849711555753967

theorem tailTrace_2102464 : CollatzResearch.WordTrace tailWord_2102464 prefixEnd_2102464 719716393849711555753967 := by
  unfold tailWord_2102464
  simp only [CollatzResearch.WordTrace]
  refine ⟨38341580927569737554553223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51122107903426316739404297 38341580927569737554553223)
  ·
    refine ⟨57512371391354606331829835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38341580927569737554553223 57512371391354606331829835)
    ·
      refine ⟨86268557087031909497744753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57512371391354606331829835 86268557087031909497744753)
      ·
        refine ⟨64701417815273932123308565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86268557087031909497744753 64701417815273932123308565)
        ·
          refine ⟨3032878960090965568280089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64701417815273932123308565 3032878960090965568280089)
          ·
            refine ⟨2274659220068224176210067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3032878960090965568280089 2274659220068224176210067)
            ·
              refine ⟨3411988830102336264315101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2274659220068224176210067 3411988830102336264315101)
              ·
                refine ⟨1279495811288376099118163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3411988830102336264315101 1279495811288376099118163)
                ·
                  refine ⟨1919243716932564148677245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279495811288376099118163 1919243716932564148677245)
                  ·
                    refine ⟨719716393849711555753967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1919243716932564148677245 719716393849711555753967)
                    ·
                      rfl

theorem cell22_2102464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 1, 3].length) (baseStart_2102464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102464 prefixEnd_2102464 := by exact prefixLift 2102464
  have htrace : WordTrace (prefixWord ++ tailWord_2102464) baseStart_2102464 baseEnd_2102464 := by
    simpa [prefixWord, tailWord_2102464, baseEnd_2102464] using wordTrace_append hprefix tailTrace_2102464
  have hstable : (prefixWord ++ tailWord_2102464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102464).length < 2 ^ (prefixWord ++ tailWord_2102464).sum := by decide
  have hdescent : baseEnd_2102464 < baseStart_2102464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102471 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 8]
def baseStart_2102471 : Nat := 118140960795 + 2102471 * 2 ^ 59
def prefixEnd_2102471 : Nat := 4983230072969 + 3 ^ 40 * 2102471 * 2
def baseEnd_2102471 : Nat := 239906263364255290276315

theorem tailTrace_2102471 : CollatzResearch.WordTrace tailWord_2102471 prefixEnd_2102471 239906263364255290276315 := by
  unfold tailWord_2102471
  simp only [CollatzResearch.WordTrace]
  refine ⟨76683417166114115304611267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51122278110742743536407511 76683417166114115304611267)
  ·
    refine ⟨115025125749171172956916901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76683417166114115304611267 115025125749171172956916901)
    ·
      refine ⟨21567211077969594929421919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115025125749171172956916901 21567211077969594929421919)
      ·
        refine ⟨32350816616954392394132879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21567211077969594929421919 32350816616954392394132879)
        ·
          refine ⟨48526224925431588591199319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32350816616954392394132879 48526224925431588591199319)
          ·
            refine ⟨72789337388147382886798979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48526224925431588591199319 72789337388147382886798979)
            ·
              refine ⟨109184006082221074330198469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72789337388147382886798979 109184006082221074330198469)
              ·
                refine ⟨20472001140416451436912213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109184006082221074330198469 20472001140416451436912213)
                ·
                  refine ⟨239906263364255290276315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20472001140416451436912213 239906263364255290276315)
                  ·
                    rfl

theorem cell22_2102471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 8].length) (baseStart_2102471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102471 prefixEnd_2102471 := by exact prefixLift 2102471
  have htrace : WordTrace (prefixWord ++ tailWord_2102471) baseStart_2102471 baseEnd_2102471 := by
    simpa [prefixWord, tailWord_2102471, baseEnd_2102471] using wordTrace_append hprefix tailTrace_2102471
  have hstable : (prefixWord ++ tailWord_2102471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102471).length < 2 ^ (prefixWord ++ tailWord_2102471).sum := by decide
  have hdescent : baseEnd_2102471 < baseStart_2102471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102565 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 5, 3]
def baseStart_2102565 : Nat := 118140960795 + 2102565 * 2 ^ 59
def prefixEnd_2102565 : Nat := 4983230072969 + 3 ^ 40 * 2102565 * 2
def baseEnd_2102565 : Nat := 719750968213780958978657

theorem tailTrace_2102565 : CollatzResearch.WordTrace tailWord_2102565 prefixEnd_2102565 719750968213780958978657 := by
  unfold tailWord_2102565
  simp only [CollatzResearch.WordTrace]
  refine ⟨76686845627773569358533149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51124563751849046239022099 76686845627773569358533149)
  ·
    refine ⟨28757567110415088509449931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76686845627773569358533149 28757567110415088509449931)
    ·
      refine ⟨43136350665622632764174897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28757567110415088509449931 43136350665622632764174897)
      ·
        refine ⟨32352262999216974573131173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43136350665622632764174897 32352262999216974573131173)
        ·
          refine ⟨6066049312353182732462095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32352262999216974573131173 6066049312353182732462095)
          ·
            refine ⟨9099073968529774098693143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6066049312353182732462095 9099073968529774098693143)
            ·
              refine ⟨13648610952794661148039715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9099073968529774098693143 13648610952794661148039715)
              ·
                refine ⟨20472916429191991722059573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13648610952794661148039715 20472916429191991722059573)
                ·
                  refine ⟨1919335915236749223943085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20472916429191991722059573 1919335915236749223943085)
                  ·
                    refine ⟨719750968213780958978657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1919335915236749223943085 719750968213780958978657)
                    ·
                      rfl

theorem cell22_2102565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_2102565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102565 prefixEnd_2102565 := by exact prefixLift 2102565
  have htrace : WordTrace (prefixWord ++ tailWord_2102565) baseStart_2102565 baseEnd_2102565 := by
    simpa [prefixWord, tailWord_2102565, baseEnd_2102565] using wordTrace_append hprefix tailTrace_2102565
  have hstable : (prefixWord ++ tailWord_2102565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102565).length < 2 ^ (prefixWord ++ tailWord_2102565).sum := by decide
  have hdescent : baseEnd_2102565 < baseStart_2102565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102612 : List Nat := [2, 4, 1, 1, 2, 1, 5, 1, 5]
def baseStart_2102612 : Nat := 118140960795 + 2102612 * 2 ^ 59
def prefixEnd_2102612 : Nat := 4983230072969 + 3 ^ 40 * 2102612 * 2
def baseEnd_2102612 : Nat := 239922352424762834351171

theorem tailTrace_2102612 : CollatzResearch.WordTrace tailWord_2102612 prefixEnd_2102612 239922352424762834351171 := by
  unfold tailWord_2102612
  simp only [CollatzResearch.WordTrace]
  refine ⟨38344279929301648192747045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51125706572402197590329393 38344279929301648192747045)
  ·
    refine ⟨7189552486744059036140071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38344279929301648192747045 7189552486744059036140071)
    ·
      refine ⟨10784328730116088554210107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7189552486744059036140071 10784328730116088554210107)
      ·
        refine ⟨16176493095174132831315161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10784328730116088554210107 16176493095174132831315161)
        ·
          refine ⟨12132369821380599623486371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16176493095174132831315161 12132369821380599623486371)
          ·
            refine ⟨18198554732070899435229557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12132369821380599623486371 18198554732070899435229557)
            ·
              refine ⟨1706114506131646822052771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18198554732070899435229557 1706114506131646822052771)
              ·
                refine ⟨2559171759197470233079157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706114506131646822052771 2559171759197470233079157)
                ·
                  refine ⟨239922352424762834351171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2559171759197470233079157 239922352424762834351171)
                  ·
                    rfl

theorem cell22_2102612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_2102612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102612 prefixEnd_2102612 := by exact prefixLift 2102612
  have htrace : WordTrace (prefixWord ++ tailWord_2102612) baseStart_2102612 baseEnd_2102612 := by
    simpa [prefixWord, tailWord_2102612, baseEnd_2102612] using wordTrace_append hprefix tailTrace_2102612
  have hstable : (prefixWord ++ tailWord_2102612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102612).length < 2 ^ (prefixWord ++ tailWord_2102612).sum := by decide
  have hdescent : baseEnd_2102612 < baseStart_2102612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102685 : List Nat := [1, 4, 2, 1, 3, 1, 2, 8]
def baseStart_2102685 : Nat := 118140960795 + 2102685 * 2 ^ 59
def prefixEnd_2102685 : Nat := 4983230072969 + 3 ^ 40 * 2102685 * 2
def baseEnd_2102685 : Nat := 79976894074015627330921

theorem tailTrace_2102685 : CollatzResearch.WordTrace tailWord_2102685 prefixEnd_2102685 79976894074015627330921 := by
  unfold tailWord_2102685
  simp only [CollatzResearch.WordTrace]
  refine ⟨76691222387338829852901509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51127481591559219901934339 76691222387338829852901509)
  ·
    refine ⟨14379604197626030597419033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76691222387338829852901509 14379604197626030597419033)
    ·
      refine ⟨10784703148219522948064275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14379604197626030597419033 10784703148219522948064275)
      ·
        refine ⟨16177054722329284422096413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10784703148219522948064275 16177054722329284422096413)
        ·
          refine ⟨6066395520873481658286155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16177054722329284422096413 6066395520873481658286155)
          ·
            refine ⟨9099593281310222487429233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6066395520873481658286155 9099593281310222487429233)
            ·
              refine ⟨6824694960982666865571925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9099593281310222487429233 6824694960982666865571925)
              ·
                refine ⟨79976894074015627330921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6824694960982666865571925 79976894074015627330921)
                ·
                  rfl

theorem cell22_2102685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 8].length) (baseStart_2102685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102685 prefixEnd_2102685 := by exact prefixLift 2102685
  have htrace : WordTrace (prefixWord ++ tailWord_2102685) baseStart_2102685 baseEnd_2102685 := by
    simpa [prefixWord, tailWord_2102685, baseEnd_2102685] using wordTrace_append hprefix tailTrace_2102685
  have hstable : (prefixWord ++ tailWord_2102685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102685).length < 2 ^ (prefixWord ++ tailWord_2102685).sum := by decide
  have hdescent : baseEnd_2102685 < baseStart_2102685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102687 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 2, 4]
def baseStart_2102687 : Nat := 118140960795 + 2102687 * 2 ^ 59
def prefixEnd_2102687 : Nat := 4983230072969 + 3 ^ 40 * 2102687 * 2
def baseEnd_2102687 : Nat := 719792731307013307428283

theorem tailTrace_2102687 : CollatzResearch.WordTrace tailWord_2102687 prefixEnd_2102687 719792731307013307428283 := by
  unfold tailWord_2102687
  simp only [CollatzResearch.WordTrace]
  refine ⟨76691295333331584194474315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51127530222221056129649543 76691295333331584194474315)
  ·
    refine ⟨115036942999997376291711473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76691295333331584194474315 115036942999997376291711473)
    ·
      refine ⟨86277707249998032218783605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115036942999997376291711473 86277707249998032218783605)
      ·
        refine ⟨8088535054687315520510963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86277707249998032218783605 8088535054687315520510963)
        ·
          refine ⟨12132802582030973280766445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8088535054687315520510963 12132802582030973280766445)
          ·
            refine ⟨4549800968261614980287417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12132802582030973280766445 4549800968261614980287417)
            ·
              refine ⟨3412350726196211235215563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4549800968261614980287417 3412350726196211235215563)
              ·
                refine ⟨5118526089294316852823345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3412350726196211235215563 5118526089294316852823345)
                ·
                  refine ⟨3838894566970737639617509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5118526089294316852823345 3838894566970737639617509)
                  ·
                    refine ⟨719792731307013307428283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3838894566970737639617509 719792731307013307428283)
                    ·
                      rfl

theorem cell22_2102687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_2102687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102687 prefixEnd_2102687 := by exact prefixLift 2102687
  have htrace : WordTrace (prefixWord ++ tailWord_2102687) baseStart_2102687 baseEnd_2102687 := by
    simpa [prefixWord, tailWord_2102687, baseEnd_2102687] using wordTrace_append hprefix tailTrace_2102687
  have hstable : (prefixWord ++ tailWord_2102687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102687).length < 2 ^ (prefixWord ++ tailWord_2102687).sum := by decide
  have hdescent : baseEnd_2102687 < baseStart_2102687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102717 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_2102717 : Nat := 118140960795 + 2102717 * 2 ^ 59
def prefixEnd_2102717 : Nat := 4983230072969 + 3 ^ 40 * 2102717 * 2
def baseEnd_2102717 : Nat := 719803000920103229178191

theorem tailTrace_2102717 : CollatzResearch.WordTrace tailWord_2102717 prefixEnd_2102717 719803000920103229178191 := by
  unfold tailWord_2102717
  simp only [CollatzResearch.WordTrace]
  refine ⟨76692389523222899318066405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51128259682148599545377603 76692389523222899318066405)
  ·
    refine ⟨14379823035604293622137451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76692389523222899318066405 14379823035604293622137451)
    ·
      refine ⟨21569734553406440433206177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14379823035604293622137451 21569734553406440433206177)
      ·
        refine ⟨16177300915054830324904633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21569734553406440433206177 16177300915054830324904633)
        ·
          refine ⟨12132975686291122743678475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16177300915054830324904633 12132975686291122743678475)
          ·
            refine ⟨18199463529436684115517713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12132975686291122743678475 18199463529436684115517713)
            ·
              refine ⟨13649597647077513086638285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18199463529436684115517713 13649597647077513086638285)
              ·
                refine ⟨5118599117654067407489357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13649597647077513086638285 5118599117654067407489357)
                ·
                  refine ⟨1919474669120275277808509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5118599117654067407489357 1919474669120275277808509)
                  ·
                    refine ⟨719803000920103229178191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1919474669120275277808509 719803000920103229178191)
                    ·
                      rfl

theorem cell22_2102717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_2102717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102717 prefixEnd_2102717 := by exact prefixLift 2102717
  have htrace : WordTrace (prefixWord ++ tailWord_2102717) baseStart_2102717 baseEnd_2102717 := by
    simpa [prefixWord, tailWord_2102717, baseEnd_2102717] using wordTrace_append hprefix tailTrace_2102717
  have hstable : (prefixWord ++ tailWord_2102717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102717).length < 2 ^ (prefixWord ++ tailWord_2102717).sum := by decide
  have hdescent : baseEnd_2102717 < baseStart_2102717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102794 : List Nat := [3, 1, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_2102794 : Nat := 118140960795 + 2102794 * 2 ^ 59
def prefixEnd_2102794 : Nat := 4983230072969 + 3 ^ 40 * 2102794 * 2
def baseEnd_2102794 : Nat := 719829359593700695002955

theorem tailTrace_2102794 : CollatzResearch.WordTrace tailWord_2102794 prefixEnd_2102794 719829359593700695002955 := by
  unfold tailWord_2102794
  simp only [CollatzResearch.WordTrace]
  refine ⟨19173799485985985367154859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51130131962629294312412957 19173799485985985367154859)
  ·
    refine ⟨28760699228978978050732289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19173799485985985367154859 28760699228978978050732289)
    ·
      refine ⟨21570524421734233538049217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28760699228978978050732289 21570524421734233538049217)
      ·
        refine ⟨16177893316300675153536913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21570524421734233538049217 16177893316300675153536913)
        ·
          refine ⟨12133419987225506365152685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16177893316300675153536913 12133419987225506365152685)
          ·
            refine ⟨4550032495209564886932257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12133419987225506365152685 4550032495209564886932257)
            ·
              refine ⟨3412524371407173665199193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4550032495209564886932257 3412524371407173665199193)
              ·
                refine ⟨2559393278555380248899395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3412524371407173665199193 2559393278555380248899395)
                ·
                  refine ⟨3839089917833070373349093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559393278555380248899395 3839089917833070373349093)
                  ·
                    refine ⟨719829359593700695002955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3839089917833070373349093 719829359593700695002955)
                    ·
                      rfl

theorem cell22_2102794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_2102794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102794 prefixEnd_2102794 := by exact prefixLift 2102794
  have htrace : WordTrace (prefixWord ++ tailWord_2102794) baseStart_2102794 baseEnd_2102794 := by
    simpa [prefixWord, tailWord_2102794, baseEnd_2102794] using wordTrace_append hprefix tailTrace_2102794
  have hstable : (prefixWord ++ tailWord_2102794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102794).length < 2 ^ (prefixWord ++ tailWord_2102794).sum := by decide
  have hdescent : baseEnd_2102794 < baseStart_2102794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102826 : List Nat := [3, 1, 4, 1, 1, 1, 5, 2, 4]
def baseStart_2102826 : Nat := 118140960795 + 2102826 * 2 ^ 59
def prefixEnd_2102826 : Nat := 4983230072969 + 3 ^ 40 * 2102826 * 2
def baseEnd_2102826 : Nat := 239946771282554426067619

theorem tailTrace_2102826 : CollatzResearch.WordTrace tailWord_2102826 prefixEnd_2102826 239946771282554426067619 := by
  unfold tailWord_2102826
  simp only [CollatzResearch.WordTrace]
  refine ⟨19174091269957002733446083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51130910053218673955856221 19174091269957002733446083)
  ·
    refine ⟨28761136904935504100169125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19174091269957002733446083 28761136904935504100169125)
    ·
      refine ⟨5392713169675407018781711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28761136904935504100169125 5392713169675407018781711)
      ·
        refine ⟨8089069754513110528172567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5392713169675407018781711 8089069754513110528172567)
        ·
          refine ⟨12133604631769665792258851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8089069754513110528172567 12133604631769665792258851)
          ·
            refine ⟨18200406947654498688388277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12133604631769665792258851 18200406947654498688388277)
            ·
              refine ⟨1706288151342609252036401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18200406947654498688388277 1706288151342609252036401)
              ·
                refine ⟨1279716113506956939027301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1706288151342609252036401 1279716113506956939027301)
                ·
                  refine ⟨239946771282554426067619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1279716113506956939027301 239946771282554426067619)
                  ·
                    rfl

theorem cell22_2102826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_2102826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102826 prefixEnd_2102826 := by exact prefixLift 2102826
  have htrace : WordTrace (prefixWord ++ tailWord_2102826) baseStart_2102826 baseEnd_2102826 := by
    simpa [prefixWord, tailWord_2102826, baseEnd_2102826] using wordTrace_append hprefix tailTrace_2102826
  have hstable : (prefixWord ++ tailWord_2102826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102826).length < 2 ^ (prefixWord ++ tailWord_2102826).sum := by decide
  have hdescent : baseEnd_2102826 < baseStart_2102826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102837 : List Nat := [1, 3, 3, 1, 1, 4, 2, 7]
def baseStart_2102837 : Nat := 118140960795 + 2102837 * 2 ^ 59
def prefixEnd_2102837 : Nat := 4983230072969 + 3 ^ 40 * 2102837 * 2
def baseEnd_2102837 : Nat := 79982675485829212908647

theorem tailTrace_2102837 : CollatzResearch.WordTrace tailWord_2102837 prefixEnd_2102837 79982675485829212908647 := by
  unfold tailWord_2102837
  simp only [CollatzResearch.WordTrace]
  refine ⟨76696766282788159812434765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51131177521858773208289843 76696766282788159812434765)
  ·
    refine ⟨28761287356045559929663037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76696766282788159812434765 28761287356045559929663037)
    ·
      refine ⟨10785482758517084973623639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28761287356045559929663037 10785482758517084973623639)
      ·
        refine ⟨16178224137775627460435459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10785482758517084973623639 16178224137775627460435459)
        ·
          refine ⟨24267336206663441190653189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16178224137775627460435459 24267336206663441190653189)
          ·
            refine ⟨4550125538749395223247473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24267336206663441190653189 4550125538749395223247473)
            ·
              refine ⟨3412594154062046417435605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4550125538749395223247473 3412594154062046417435605)
              ·
                refine ⟨79982675485829212908647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3412594154062046417435605 79982675485829212908647)
                ·
                  rfl

theorem cell22_2102837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 7].length) (baseStart_2102837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102837 prefixEnd_2102837 := by exact prefixLift 2102837
  have htrace : WordTrace (prefixWord ++ tailWord_2102837) baseStart_2102837 baseEnd_2102837 := by
    simpa [prefixWord, tailWord_2102837, baseEnd_2102837] using wordTrace_append hprefix tailTrace_2102837
  have hstable : (prefixWord ++ tailWord_2102837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102837).length < 2 ^ (prefixWord ++ tailWord_2102837).sum := by decide
  have hdescent : baseEnd_2102837 < baseStart_2102837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102841 : List Nat := [1, 2, 1, 5, 1, 2, 4, 1, 2, 3]
def baseStart_2102841 : Nat := 118140960795 + 2102841 * 2 ^ 59
def prefixEnd_2102841 : Nat := 4983230072969 + 3 ^ 40 * 2102841 * 2
def baseEnd_2102841 : Nat := 719845448654208239077811

theorem tailTrace_2102841 : CollatzResearch.WordTrace tailWord_2102841 prefixEnd_2102841 719845448654208239077811 := by
  unfold tailWord_2102841
  simp only [CollatzResearch.WordTrace]
  refine ⟨76696912174773668495580377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51131274783182445663720251 76696912174773668495580377)
  ·
    refine ⟨57522684131080251371685283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76696912174773668495580377 57522684131080251371685283)
    ·
      refine ⟨86284026196620377057527925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57522684131080251371685283 86284026196620377057527925)
      ·
        refine ⟨8089127455933160349143243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86284026196620377057527925 8089127455933160349143243)
        ·
          refine ⟨12133691183899740523714865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8089127455933160349143243 12133691183899740523714865)
          ·
            refine ⟨9100268387924805392786149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12133691183899740523714865 9100268387924805392786149)
            ·
              refine ⟨1706300322735901011147403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9100268387924805392786149 1706300322735901011147403)
              ·
                refine ⟨2559450484103851516721105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706300322735901011147403 2559450484103851516721105)
                ·
                  refine ⟨1919587863077888637540829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2559450484103851516721105 1919587863077888637540829)
                  ·
                    refine ⟨719845448654208239077811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1919587863077888637540829 719845448654208239077811)
                    ·
                      rfl

theorem cell22_2102841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 2, 3].length) (baseStart_2102841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102841 prefixEnd_2102841 := by exact prefixLift 2102841
  have htrace : WordTrace (prefixWord ++ tailWord_2102841) baseStart_2102841 baseEnd_2102841 := by
    simpa [prefixWord, tailWord_2102841, baseEnd_2102841] using wordTrace_append hprefix tailTrace_2102841
  have hstable : (prefixWord ++ tailWord_2102841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102841).length < 2 ^ (prefixWord ++ tailWord_2102841).sum := by decide
  have hdescent : baseEnd_2102841 < baseStart_2102841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102877 : List Nat := [1, 4, 4, 2, 2, 1, 2, 2, 4]
def baseStart_2102877 : Nat := 118140960795 + 2102877 * 2 ^ 59
def prefixEnd_2102877 : Nat := 4983230072969 + 3 ^ 40 * 2102877 * 2
def baseEnd_2102877 : Nat := 239952590729972048392567

theorem tailTrace_2102877 : CollatzResearch.WordTrace tailWord_2102877 prefixEnd_2102877 239952590729972048392567 := by
  unfold tailWord_2102877
  simp only [CollatzResearch.WordTrace]
  refine ⟨76698225202643246643890885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51132150135095497762593923 76698225202643246643890885)
  ·
    refine ⟨14380917225495608745729541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76698225202643246643890885 14380917225495608745729541)
    ·
      refine ⟨2696421979780426639824289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14380917225495608745729541 2696421979780426639824289)
      ·
        refine ⟨2022316484835319979868217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2696421979780426639824289 2022316484835319979868217)
        ·
          refine ⟨1516737363626489984901163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022316484835319979868217 1516737363626489984901163)
          ·
            refine ⟨2275106045439734977351745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516737363626489984901163 2275106045439734977351745)
            ·
              refine ⟨1706329534079801233013809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2275106045439734977351745 1706329534079801233013809)
              ·
                refine ⟨1279747150559850924760357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1706329534079801233013809 1279747150559850924760357)
                ·
                  refine ⟨239952590729972048392567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1279747150559850924760357 239952590729972048392567)
                  ·
                    rfl

theorem cell22_2102877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_2102877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102877 prefixEnd_2102877 := by exact prefixLift 2102877
  have htrace : WordTrace (prefixWord ++ tailWord_2102877) baseStart_2102877 baseEnd_2102877 := by
    simpa [prefixWord, tailWord_2102877, baseEnd_2102877] using wordTrace_append hprefix tailTrace_2102877
  have hstable : (prefixWord ++ tailWord_2102877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102877).length < 2 ^ (prefixWord ++ tailWord_2102877).sum := by decide
  have hdescent : baseEnd_2102877 < baseStart_2102877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102912 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 3, 4]
def baseStart_2102912 : Nat := 118140960795 + 2102912 * 2 ^ 59
def prefixEnd_2102912 : Nat := 4983230072969 + 3 ^ 40 * 2102912 * 2
def baseEnd_2102912 : Nat := 719869753405187720552593

theorem tailTrace_2102912 : CollatzResearch.WordTrace tailWord_2102912 prefixEnd_2102912 719869753405187720552593 := by
  unfold tailWord_2102912
  simp only [CollatzResearch.WordTrace]
  refine ⟨38349750878758223810707495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51133001171677631747609993 38349750878758223810707495)
  ·
    refine ⟨57524626318137335716061243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38349750878758223810707495 57524626318137335716061243)
    ·
      refine ⟨86286939477206003574091865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57524626318137335716061243 86286939477206003574091865)
      ·
        refine ⟨64715204607904502680568899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86286939477206003574091865 64715204607904502680568899)
        ·
          refine ⟨97072806911856754020853349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64715204607904502680568899 97072806911856754020853349)
          ·
            refine ⟨18201151295973141378910003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97072806911856754020853349 18201151295973141378910003)
            ·
              refine ⟨27301726943959712068365005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18201151295973141378910003 27301726943959712068365005)
              ·
                refine ⟨10238147603984892025636877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27301726943959712068365005 10238147603984892025636877)
                ·
                  refine ⟨3839305351494334509613829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10238147603984892025636877 3839305351494334509613829)
                  ·
                    refine ⟨719869753405187720552593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3839305351494334509613829 719869753405187720552593)
                    ·
                      rfl

theorem cell22_2102912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_2102912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102912 prefixEnd_2102912 := by exact prefixLift 2102912
  have htrace : WordTrace (prefixWord ++ tailWord_2102912) baseStart_2102912 baseEnd_2102912 := by
    simpa [prefixWord, tailWord_2102912, baseEnd_2102912] using wordTrace_append hprefix tailTrace_2102912
  have hstable : (prefixWord ++ tailWord_2102912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102912).length < 2 ^ (prefixWord ++ tailWord_2102912).sum := by decide
  have hdescent : baseEnd_2102912 < baseStart_2102912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102920 : List Nat := [2, 1, 3, 5, 1, 1, 2, 3, 1, 3]
def baseStart_2102920 : Nat := 118140960795 + 2102920 * 2 ^ 59
def prefixEnd_2102920 : Nat := 4983230072969 + 3 ^ 40 * 2102920 * 2
def baseEnd_2102920 : Nat := 719872491968678366352569

theorem tailTrace_2102920 : CollatzResearch.WordTrace tailWord_2102920 prefixEnd_2102920 719872491968678366352569 := by
  unfold tailWord_2102920
  simp only [CollatzResearch.WordTrace]
  refine ⟨38349896770743732493853107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51133195694324976658470809 38349896770743732493853107)
  ·
    refine ⟨57524845156115598740779661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38349896770743732493853107 57524845156115598740779661)
    ·
      refine ⟨21571816933543349527792373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57524845156115598740779661 21571816933543349527792373)
      ·
        refine ⟨2022357837519689018230535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21571816933543349527792373 2022357837519689018230535)
        ·
          refine ⟨3033536756279533527345803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2022357837519689018230535 3033536756279533527345803)
          ·
            refine ⟨4550305134419300291018705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3033536756279533527345803 4550305134419300291018705)
            ·
              refine ⟨3412728850814475218264029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4550305134419300291018705 3412728850814475218264029)
              ·
                refine ⟨1279773319055428206849011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3412728850814475218264029 1279773319055428206849011)
                ·
                  refine ⟨1919659978583142310273517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279773319055428206849011 1919659978583142310273517)
                  ·
                    refine ⟨719872491968678366352569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1919659978583142310273517 719872491968678366352569)
                    ·
                      rfl

theorem cell22_2102920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_2102920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102920 prefixEnd_2102920 := by exact prefixLift 2102920
  have htrace : WordTrace (prefixWord ++ tailWord_2102920) baseStart_2102920 baseEnd_2102920 := by
    simpa [prefixWord, tailWord_2102920, baseEnd_2102920] using wordTrace_append hprefix tailTrace_2102920
  have hstable : (prefixWord ++ tailWord_2102920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102920).length < 2 ^ (prefixWord ++ tailWord_2102920).sum := by decide
  have hdescent : baseEnd_2102920 < baseStart_2102920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102944 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 6]
def baseStart_2102944 : Nat := 118140960795 + 2102944 * 2 ^ 59
def prefixEnd_2102944 : Nat := 4983230072969 + 3 ^ 40 * 2102944 * 2
def baseEnd_2102944 : Nat := 239960235886383434584165

theorem tailTrace_2102944 : CollatzResearch.WordTrace tailWord_2102944 prefixEnd_2102944 239960235886383434584165 := by
  unfold tailWord_2102944
  simp only [CollatzResearch.WordTrace]
  refine ⟨38350334446700258543289943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51133779262267011391053257 38350334446700258543289943)
  ·
    refine ⟨57525501670050387814934915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38350334446700258543289943 57525501670050387814934915)
    ·
      refine ⟨86288252505075581722402373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57525501670050387814934915 86288252505075581722402373)
      ·
        refine ⟨16179047344701671572950445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86288252505075581722402373 16179047344701671572950445)
        ·
          refine ⟨6067142754263126839856417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16179047344701671572950445 6067142754263126839856417)
          ·
            refine ⟨4550357065697345129892313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6067142754263126839856417 4550357065697345129892313)
            ·
              refine ⟨3412767799273008847419235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4550357065697345129892313 3412767799273008847419235)
              ·
                refine ⟨5119151698909513271128853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3412767799273008847419235 5119151698909513271128853)
                ·
                  refine ⟨239960235886383434584165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5119151698909513271128853 239960235886383434584165)
                  ·
                    rfl

theorem cell22_2102944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_2102944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102944 prefixEnd_2102944 := by exact prefixLift 2102944
  have htrace : WordTrace (prefixWord ++ tailWord_2102944) baseStart_2102944 baseEnd_2102944 := by
    simpa [prefixWord, tailWord_2102944, baseEnd_2102944] using wordTrace_append hprefix tailTrace_2102944
  have hstable : (prefixWord ++ tailWord_2102944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102944).length < 2 ^ (prefixWord ++ tailWord_2102944).sum := by decide
  have hdescent : baseEnd_2102944 < baseStart_2102944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2102974 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_2102974 : Nat := 118140960795 + 2102974 * 2 ^ 59
def prefixEnd_2102974 : Nat := 4983230072969 + 3 ^ 40 * 2102974 * 2
def baseEnd_2102974 : Nat := 719890977272240225502403

theorem tailTrace_2102974 : CollatzResearch.WordTrace tailWord_2102974 prefixEnd_2102974 719890977272240225502403 := by
  unfold tailWord_2102974
  simp only [CollatzResearch.WordTrace]
  refine ⟨9587720385411479026271497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51134508722194554806781317 9587720385411479026271497)
  ·
    refine ⟨7190790289058609269703623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9587720385411479026271497 7190790289058609269703623)
    ·
      refine ⟨10786185433587913904555435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7190790289058609269703623 10786185433587913904555435)
      ·
        refine ⟨16179278150381870856833153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10786185433587913904555435 16179278150381870856833153)
        ·
          refine ⟨12134458612786403142624865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16179278150381870856833153 12134458612786403142624865)
          ·
            refine ⟨9100843959589802356968649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12134458612786403142624865 9100843959589802356968649)
            ·
              refine ⟨6825632969692351767726487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9100843959589802356968649 6825632969692351767726487)
              ·
                refine ⟨10238449454538527651589731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6825632969692351767726487 10238449454538527651589731)
                ·
                  refine ⟨15357674181807791477384597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10238449454538527651589731 15357674181807791477384597)
                  ·
                    refine ⟨719890977272240225502403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15357674181807791477384597 719890977272240225502403)
                    ·
                      rfl

theorem cell22_2102974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_2102974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2102974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2102974 prefixEnd_2102974 := by exact prefixLift 2102974
  have htrace : WordTrace (prefixWord ++ tailWord_2102974) baseStart_2102974 baseEnd_2102974 := by
    simpa [prefixWord, tailWord_2102974, baseEnd_2102974] using wordTrace_append hprefix tailTrace_2102974
  have hstable : (prefixWord ++ tailWord_2102974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2102974).length < 2 ^ (prefixWord ++ tailWord_2102974).sum := by decide
  have hdescent : baseEnd_2102974 < baseStart_2102974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2102974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103032 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 3, 7]
def baseStart_2103032 : Nat := 118140960795 + 2103032 * 2 ^ 59
def prefixEnd_2103032 : Nat := 4983230072969 + 3 ^ 40 * 2103032 * 2
def baseEnd_2103032 : Nat := 719910831857547407552225

theorem tailTrace_2103032 : CollatzResearch.WordTrace tailWord_2103032 prefixEnd_2103032 719910831857547407552225 := by
  unfold tailWord_2103032
  simp only [CollatzResearch.WordTrace]
  refine ⟨38351939258540854057891675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51135919011387805410522233 38351939258540854057891675)
  ·
    refine ⟨57527908887811281086837513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38351939258540854057891675 57527908887811281086837513)
    ·
      refine ⟨43145931665858460815128135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57527908887811281086837513 43145931665858460815128135)
      ·
        refine ⟨64718897498787691222692203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43145931665858460815128135 64718897498787691222692203)
        ·
          refine ⟨97078346248181536834038305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64718897498787691222692203 97078346248181536834038305)
          ·
            refine ⟨72808759686136152625528729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97078346248181536834038305 72808759686136152625528729)
            ·
              refine ⟨54606569764602114469146547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72808759686136152625528729 54606569764602114469146547)
              ·
                refine ⟨81909854646903171703719821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54606569764602114469146547 81909854646903171703719821)
                ·
                  refine ⟨30716195492588689388894933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81909854646903171703719821 30716195492588689388894933)
                  ·
                    refine ⟨719910831857547407552225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30716195492588689388894933 719910831857547407552225)
                    ·
                      rfl

theorem cell22_2103032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_2103032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103032 prefixEnd_2103032 := by exact prefixLift 2103032
  have htrace : WordTrace (prefixWord ++ tailWord_2103032) baseStart_2103032 baseEnd_2103032 := by
    simpa [prefixWord, tailWord_2103032, baseEnd_2103032] using wordTrace_append hprefix tailTrace_2103032
  have hstable : (prefixWord ++ tailWord_2103032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103032).length < 2 ^ (prefixWord ++ tailWord_2103032).sum := by decide
  have hdescent : baseEnd_2103032 < baseStart_2103032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103064 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 3, 4]
def baseStart_2103064 : Nat := 118140960795 + 2103064 * 2 ^ 59
def prefixEnd_2103064 : Nat := 4983230072969 + 3 ^ 40 * 2103064 * 2
def baseEnd_2103064 : Nat := 719921786111509990752127

theorem tailTrace_2103064 : CollatzResearch.WordTrace tailWord_2103064 prefixEnd_2103064 719921786111509990752127 := by
  unfold tailWord_2103064
  simp only [CollatzResearch.WordTrace]
  refine ⟨38352522826482888790474123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51136697101977185053965497 38352522826482888790474123)
  ·
    refine ⟨57528784239724333185711185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38352522826482888790474123 57528784239724333185711185)
    ·
      refine ⟨43146588179793249889283389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57528784239724333185711185 43146588179793249889283389)
      ·
        refine ⟨16179970567422468708481271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43146588179793249889283389 16179970567422468708481271)
        ·
          refine ⟨24269955851133703062721907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16179970567422468708481271 24269955851133703062721907)
          ·
            refine ⟨36404933776700554594082861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24269955851133703062721907 36404933776700554594082861)
            ·
              refine ⟨13651850166262707972781073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36404933776700554594082861 13651850166262707972781073)
              ·
                refine ⟨10238887624697030979585805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13651850166262707972781073 10238887624697030979585805)
                ·
                  refine ⟨3839582859261386617344677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10238887624697030979585805 3839582859261386617344677)
                  ·
                    refine ⟨719921786111509990752127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3839582859261386617344677 719921786111509990752127)
                    ·
                      rfl

theorem cell22_2103064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_2103064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103064 prefixEnd_2103064 := by exact prefixLift 2103064
  have htrace : WordTrace (prefixWord ++ tailWord_2103064) baseStart_2103064 baseEnd_2103064 := by
    simpa [prefixWord, tailWord_2103064, baseEnd_2103064] using wordTrace_append hprefix tailTrace_2103064
  have hstable : (prefixWord ++ tailWord_2103064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103064).length < 2 ^ (prefixWord ++ tailWord_2103064).sum := by decide
  have hdescent : baseEnd_2103064 < baseStart_2103064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103096 : List Nat := [2, 1, 2, 1, 3, 3, 1, 5, 4]
def baseStart_2103096 : Nat := 118140960795 + 2103096 * 2 ^ 59
def prefixEnd_2103096 : Nat := 4983230072969 + 3 ^ 40 * 2103096 * 2
def baseEnd_2103096 : Nat := 239977580121824191317343

theorem tailTrace_2103096 : CollatzResearch.WordTrace tailWord_2103096 prefixEnd_2103096 239977580121824191317343 := by
  unfold tailWord_2103096
  simp only [CollatzResearch.WordTrace]
  refine ⟨38353106394424923523056571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51137475192566564697408761 38353106394424923523056571)
  ·
    refine ⟨57529659591637385284584857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38353106394424923523056571 57529659591637385284584857)
    ·
      refine ⟨43147244693728038963438643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57529659591637385284584857 43147244693728038963438643)
      ·
        refine ⟨64720867040592058445157965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43147244693728038963438643 64720867040592058445157965)
        ·
          refine ⟨24270325140222021916934237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64720867040592058445157965 24270325140222021916934237)
          ·
            refine ⟨9101371927583258218850339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24270325140222021916934237 9101371927583258218850339)
            ·
              refine ⟨13652057891374887328275509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9101371927583258218850339 13652057891374887328275509)
              ·
                refine ⟨1279880427316395687025829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13652057891374887328275509 1279880427316395687025829)
                ·
                  refine ⟨239977580121824191317343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1279880427316395687025829 239977580121824191317343)
                  ·
                    rfl

theorem cell22_2103096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 4].length) (baseStart_2103096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103096 prefixEnd_2103096 := by exact prefixLift 2103096
  have htrace : WordTrace (prefixWord ++ tailWord_2103096) baseStart_2103096 baseEnd_2103096 := by
    simpa [prefixWord, tailWord_2103096, baseEnd_2103096] using wordTrace_append hprefix tailTrace_2103096
  have hstable : (prefixWord ++ tailWord_2103096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103096).length < 2 ^ (prefixWord ++ tailWord_2103096).sum := by decide
  have hdescent : baseEnd_2103096 < baseStart_2103096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103098 : List Nat := [3, 1, 1, 1, 5, 1, 4, 1, 1, 4]
def baseStart_2103098 : Nat := 118140960795 + 2103098 * 2 ^ 59
def prefixEnd_2103098 : Nat := 4983230072969 + 3 ^ 40 * 2103098 * 2
def baseEnd_2103098 : Nat := 719933425006345235402023

theorem tailTrace_2103098 : CollatzResearch.WordTrace tailWord_2103098 prefixEnd_2103098 719933425006345235402023 := by
  unfold tailWord_2103098
  simp only [CollatzResearch.WordTrace]
  refine ⟨19176571433710650346921487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51137523823228400925123965 19176571433710650346921487)
  ·
    refine ⟨28764857150565975520382231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19176571433710650346921487 28764857150565975520382231)
    ·
      refine ⟨43147285725848963280573347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28764857150565975520382231 43147285725848963280573347)
      ·
        refine ⟨64720928588773444920860021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43147285725848963280573347 64720928588773444920860021)
        ·
          refine ⟨6067587055197510461330627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64720928588773444920860021 6067587055197510461330627)
          ·
            refine ⟨9101380582796265691995941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6067587055197510461330627 9101380582796265691995941)
            ·
              refine ⟨1706508859274299817249239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9101380582796265691995941 1706508859274299817249239)
              ·
                refine ⟨2559763288911449725873859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706508859274299817249239 2559763288911449725873859)
                ·
                  refine ⟨3839644933367174588810789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559763288911449725873859 3839644933367174588810789)
                  ·
                    refine ⟨719933425006345235402023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3839644933367174588810789 719933425006345235402023)
                    ·
                      rfl

theorem cell22_2103098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_2103098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103098 prefixEnd_2103098 := by exact prefixLift 2103098
  have htrace : WordTrace (prefixWord ++ tailWord_2103098) baseStart_2103098 baseEnd_2103098 := by
    simpa [prefixWord, tailWord_2103098, baseEnd_2103098] using wordTrace_append hprefix tailTrace_2103098
  have hstable : (prefixWord ++ tailWord_2103098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103098).length < 2 ^ (prefixWord ++ tailWord_2103098).sum := by decide
  have hdescent : baseEnd_2103098 < baseStart_2103098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103109 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_2103109 : Nat := 118140960795 + 2103109 * 2 ^ 59
def prefixEnd_2103109 : Nat := 4983230072969 + 3 ^ 40 * 2103109 * 2
def baseEnd_2103109 : Nat := 719937190531144873376989

theorem tailTrace_2103109 : CollatzResearch.WordTrace tailWord_2103109 prefixEnd_2103109 719937190531144873376989 := by
  unfold tailWord_2103109
  simp only [CollatzResearch.WordTrace]
  refine ⟨76706686937802750266336381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51137791291868500177557587 76706686937802750266336381)
  ·
    refine ⟨28765007601676031349876143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76706686937802750266336381 28765007601676031349876143)
    ·
      refine ⟨43147511402514047024814215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28765007601676031349876143 43147511402514047024814215)
      ·
        refine ⟨64721267103771070537221323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43147511402514047024814215 64721267103771070537221323)
        ·
          refine ⟨97081900655656605805831985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64721267103771070537221323 97081900655656605805831985)
          ·
            refine ⟨72811425491742454354373989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97081900655656605805831985 72811425491742454354373989)
            ·
              refine ⟨13652142279701710191445123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72811425491742454354373989 13652142279701710191445123)
              ·
                refine ⟨20478213419552565287167685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13652142279701710191445123 20478213419552565287167685)
                ·
                  refine ⟨3839665016166105991343941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20478213419552565287167685 3839665016166105991343941)
                  ·
                    refine ⟨719937190531144873376989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3839665016166105991343941 719937190531144873376989)
                    ·
                      rfl

theorem cell22_2103109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_2103109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103109 prefixEnd_2103109 := by exact prefixLift 2103109
  have htrace : WordTrace (prefixWord ++ tailWord_2103109) baseStart_2103109 baseEnd_2103109 := by
    simpa [prefixWord, tailWord_2103109, baseEnd_2103109] using wordTrace_append hprefix tailTrace_2103109
  have hstable : (prefixWord ++ tailWord_2103109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103109).length < 2 ^ (prefixWord ++ tailWord_2103109).sum := by decide
  have hdescent : baseEnd_2103109 < baseStart_2103109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103154 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_2103154 : Nat := 118140960795 + 2103154 * 2 ^ 59
def prefixEnd_2103154 : Nat := 4983230072969 + 3 ^ 40 * 2103154 * 2
def baseEnd_2103154 : Nat := 719952594950779756001851

theorem tailTrace_2103154 : CollatzResearch.WordTrace tailWord_2103154 prefixEnd_2103154 719952594950779756001851 := by
  unfold tailWord_2103154
  simp only [CollatzResearch.WordTrace]
  refine ⟨19177082055659930737931129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51138885481759815301149677 19177082055659930737931129)
  ·
    refine ⟨14382811541744948053448347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19177082055659930737931129 14382811541744948053448347)
    ·
      refine ⟨21574217312617422080172521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14382811541744948053448347 21574217312617422080172521)
      ·
        refine ⟨16180662984463066560129391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21574217312617422080172521 16180662984463066560129391)
        ·
          refine ⟨24270994476694599840194087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16180662984463066560129391 24270994476694599840194087)
          ·
            refine ⟨36406491715041899760291131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24270994476694599840194087 36406491715041899760291131)
            ·
              refine ⟨54609737572562849640436697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36406491715041899760291131 54609737572562849640436697)
              ·
                refine ⟨40957303179422137230327523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54609737572562849640436697 40957303179422137230327523)
                ·
                  refine ⟨61435954769133205845491285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40957303179422137230327523 61435954769133205845491285)
                  ·
                    refine ⟨719952594950779756001851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61435954769133205845491285 719952594950779756001851)
                    ·
                      rfl

theorem cell22_2103154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_2103154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103154 prefixEnd_2103154 := by exact prefixLift 2103154
  have htrace : WordTrace (prefixWord ++ tailWord_2103154) baseStart_2103154 baseEnd_2103154 := by
    simpa [prefixWord, tailWord_2103154, baseEnd_2103154] using wordTrace_append hprefix tailTrace_2103154
  have hstable : (prefixWord ++ tailWord_2103154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103154).length < 2 ^ (prefixWord ++ tailWord_2103154).sum := by decide
  have hdescent : baseEnd_2103154 < baseStart_2103154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103158 : List Nat := [5, 1, 1, 3, 2, 2, 8]
def baseStart_2103158 : Nat := 118140960795 + 2103158 * 2 ^ 59
def prefixEnd_2103158 : Nat := 4983230072969 + 3 ^ 40 * 2103158 * 2
def baseEnd_2103158 : Nat := 26664961638241669588957

theorem tailTrace_2103158 : CollatzResearch.WordTrace tailWord_2103158 prefixEnd_2103158 26664961638241669588957 := by
  unfold tailWord_2103158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4794279632164076977179383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51138982743083487756580085 4794279632164076977179383)
  ·
    refine ⟨7191419448246115465769075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4794279632164076977179383 7191419448246115465769075)
    ·
      refine ⟨10787129172369173198653613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7191419448246115465769075 10787129172369173198653613)
      ·
        refine ⟨4045173439638439949495105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10787129172369173198653613 4045173439638439949495105)
        ·
          refine ⟨3033880079728829962121329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4045173439638439949495105 3033880079728829962121329)
          ·
            refine ⟨2275410059796622471590997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3033880079728829962121329 2275410059796622471590997)
            ·
              refine ⟨26664961638241669588957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2275410059796622471590997 26664961638241669588957)
              ·
                rfl

theorem cell22_2103158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 8].length) (baseStart_2103158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103158 prefixEnd_2103158 := by exact prefixLift 2103158
  have htrace : WordTrace (prefixWord ++ tailWord_2103158) baseStart_2103158 baseEnd_2103158 := by
    simpa [prefixWord, tailWord_2103158, baseEnd_2103158] using wordTrace_append hprefix tailTrace_2103158
  have hstable : (prefixWord ++ tailWord_2103158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103158).length < 2 ^ (prefixWord ++ tailWord_2103158).sum := by decide
  have hdescent : baseEnd_2103158 < baseStart_2103158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103308 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 3, 3]
def baseStart_2103308 : Nat := 118140960795 + 2103308 * 2 ^ 59
def prefixEnd_2103308 : Nat := 4983230072969 + 3 ^ 40 * 2103308 * 2
def baseEnd_2103308 : Nat := 720005312297974687651379

theorem tailTrace_2103308 : CollatzResearch.WordTrace tailWord_2103308 prefixEnd_2103308 720005312297974687651379 := by
  unfold tailWord_2103308
  simp only [CollatzResearch.WordTrace]
  refine ⟨38356972532040903626415289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51142630042721204835220385 38356972532040903626415289)
  ·
    refine ⟨28767729399030677719811467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38356972532040903626415289 28767729399030677719811467)
    ·
      refine ⟨43151594098546016579717201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28767729399030677719811467 43151594098546016579717201)
      ·
        refine ⟨32363695573909512434787901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43151594098546016579717201 32363695573909512434787901)
        ·
          refine ⟨12136385840216067163045463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32363695573909512434787901 12136385840216067163045463)
          ·
            refine ⟨18204578760324100744568195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12136385840216067163045463 18204578760324100744568195)
            ·
              refine ⟨27306868140486151116852293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18204578760324100744568195 27306868140486151116852293)
              ·
                refine ⟨5120037776341153334409805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27306868140486151116852293 5120037776341153334409805)
                ·
                  refine ⟨1920014166127932500403677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5120037776341153334409805 1920014166127932500403677)
                  ·
                    refine ⟨720005312297974687651379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1920014166127932500403677 720005312297974687651379)
                    ·
                      rfl

theorem cell22_2103308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_2103308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103308 prefixEnd_2103308 := by exact prefixLift 2103308
  have htrace : WordTrace (prefixWord ++ tailWord_2103308) baseStart_2103308 baseEnd_2103308 := by
    simpa [prefixWord, tailWord_2103308, baseEnd_2103308] using wordTrace_append hprefix tailTrace_2103308
  have hstable : (prefixWord ++ tailWord_2103308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103308).length < 2 ^ (prefixWord ++ tailWord_2103308).sum := by decide
  have hdescent : baseEnd_2103308 < baseStart_2103308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103316 : List Nat := [2, 4, 3, 2, 2, 1, 1, 3, 4]
def baseStart_2103316 : Nat := 118140960795 + 2103316 * 2 ^ 59
def prefixEnd_2103316 : Nat := 4983230072969 + 3 ^ 40 * 2103316 * 2
def baseEnd_2103316 : Nat := 240002683620488444483785

theorem tailTrace_2103316 : CollatzResearch.WordTrace tailWord_2103316 prefixEnd_2103316 240002683620488444483785 := by
  unfold tailWord_2103316
  simp only [CollatzResearch.WordTrace]
  refine ⟨38357118424026412309560901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51142824565368549746081201 38357118424026412309560901)
  ·
    refine ⟨7191959704504952308042669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38357118424026412309560901 7191959704504952308042669)
    ·
      refine ⟨2696984889189357115516001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7191959704504952308042669 2696984889189357115516001)
      ·
        refine ⟨2022738666892017836637001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2696984889189357115516001 2022738666892017836637001)
        ·
          refine ⟨1517054000169013377477751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022738666892017836637001 1517054000169013377477751)
          ·
            refine ⟨2275581000253520066216627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517054000169013377477751 2275581000253520066216627)
            ·
              refine ⟨3413371500380280099324941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2275581000253520066216627 3413371500380280099324941)
              ·
                refine ⟨1280014312642605037246853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3413371500380280099324941 1280014312642605037246853)
                ·
                  refine ⟨240002683620488444483785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1280014312642605037246853 240002683620488444483785)
                  ·
                    rfl

theorem cell22_2103316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_2103316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103316 prefixEnd_2103316 := by exact prefixLift 2103316
  have htrace : WordTrace (prefixWord ++ tailWord_2103316) baseStart_2103316 baseEnd_2103316 := by
    simpa [prefixWord, tailWord_2103316, baseEnd_2103316] using wordTrace_append hprefix tailTrace_2103316
  have hstable : (prefixWord ++ tailWord_2103316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103316).length < 2 ^ (prefixWord ++ tailWord_2103316).sum := by decide
  have hdescent : baseEnd_2103316 < baseStart_2103316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103338 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 7]
def baseStart_2103338 : Nat := 118140960795 + 2103338 * 2 ^ 59
def prefixEnd_2103338 : Nat := 4983230072969 + 3 ^ 40 * 2103338 * 2
def baseEnd_2103338 : Nat := 240005193970354869800429

theorem tailTrace_2103338 : CollatzResearch.WordTrace tailWord_2103338 prefixEnd_2103338 240005193970354869800429 := by
  unfold tailWord_2103338
  simp only [CollatzResearch.WordTrace]
  refine ⟨19178759813493280594105667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51143359502648748250948445 19178759813493280594105667)
  ·
    refine ⟨28768139720239920891158501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19178759813493280594105667 28768139720239920891158501)
    ·
      refine ⟨5394026197544985167092219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28768139720239920891158501 5394026197544985167092219)
      ·
        refine ⟨8091039296317477750638329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5394026197544985167092219 8091039296317477750638329)
        ·
          refine ⟨6068279472238108312978747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8091039296317477750638329 6068279472238108312978747)
          ·
            refine ⟨9102419208357162469468121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6068279472238108312978747 9102419208357162469468121)
            ·
              refine ⟨6826814406267871852101091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9102419208357162469468121 6826814406267871852101091)
              ·
                refine ⟨10240221609401807778151637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6826814406267871852101091 10240221609401807778151637)
                ·
                  refine ⟨240005193970354869800429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10240221609401807778151637 240005193970354869800429)
                  ·
                    rfl

theorem cell22_2103338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_2103338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103338 prefixEnd_2103338 := by exact prefixLift 2103338
  have htrace : WordTrace (prefixWord ++ tailWord_2103338) baseStart_2103338 baseEnd_2103338 := by
    simpa [prefixWord, tailWord_2103338, baseEnd_2103338] using wordTrace_append hprefix tailTrace_2103338
  have hstable : (prefixWord ++ tailWord_2103338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103338).length < 2 ^ (prefixWord ++ tailWord_2103338).sum := by decide
  have hdescent : baseEnd_2103338 < baseStart_2103338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103342 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_2103342 : Nat := 118140960795 + 2103342 * 2 ^ 59
def prefixEnd_2103342 : Nat := 4983230072969 + 3 ^ 40 * 2103342 * 2
def baseEnd_2103342 : Nat := 720016951192809932301275

theorem tailTrace_2103342 : CollatzResearch.WordTrace tailWord_2103342 prefixEnd_2103342 720016951192809932301275 := by
  unfold tailWord_2103342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9589398143244828882446035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51143456763972420706378853 9589398143244828882446035)
  ·
    refine ⟨14384097214867243323669053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9589398143244828882446035 14384097214867243323669053)
    ·
      refine ⟨5394036455575216246375895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14384097214867243323669053 5394036455575216246375895)
      ·
        refine ⟨8091054683362824369563843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5394036455575216246375895 8091054683362824369563843)
        ·
          refine ⟨12136582025044236554345765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8091054683362824369563843 12136582025044236554345765)
          ·
            refine ⟨2275609129695794353939831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12136582025044236554345765 2275609129695794353939831)
            ·
              refine ⟨3413413694543691530909747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2275609129695794353939831 3413413694543691530909747)
              ·
                refine ⟨5120120541815537296364621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3413413694543691530909747 5120120541815537296364621)
                ·
                  refine ⟨1920045203180826486136733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5120120541815537296364621 1920045203180826486136733)
                  ·
                    refine ⟨720016951192809932301275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1920045203180826486136733 720016951192809932301275)
                    ·
                      rfl

theorem cell22_2103342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_2103342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103342 prefixEnd_2103342 := by exact prefixLift 2103342
  have htrace : WordTrace (prefixWord ++ tailWord_2103342) baseStart_2103342 baseEnd_2103342 := by
    simpa [prefixWord, tailWord_2103342, baseEnd_2103342] using wordTrace_append hprefix tailTrace_2103342
  have hstable : (prefixWord ++ tailWord_2103342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103342).length < 2 ^ (prefixWord ++ tailWord_2103342).sum := by decide
  have hdescent : baseEnd_2103342 < baseStart_2103342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103368 : List Nat := [2, 1, 3, 1, 1, 1, 2, 6, 1, 4]
def baseStart_2103368 : Nat := 118140960795 + 2103368 * 2 ^ 59
def prefixEnd_2103368 : Nat := 4983230072969 + 3 ^ 40 * 2103368 * 2
def baseEnd_2103368 : Nat := 720025851524154531151195

theorem tailTrace_2103368 : CollatzResearch.WordTrace tailWord_2103368 prefixEnd_2103368 720025851524154531151195 := by
  unfold tailWord_2103368
  simp only [CollatzResearch.WordTrace]
  refine ⟨38358066721932218750007379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51144088962576291666676505 38358066721932218750007379)
  ·
    refine ⟨57537100082898328125011069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38358066721932218750007379 57537100082898328125011069)
    ·
      refine ⟨21576412531086873046879151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57537100082898328125011069 21576412531086873046879151)
      ·
        refine ⟨32364618796630309570318727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21576412531086873046879151 32364618796630309570318727)
        ·
          refine ⟨48546928194945464355478091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32364618796630309570318727 48546928194945464355478091)
          ·
            refine ⟨72820392292418196533217137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48546928194945464355478091 72820392292418196533217137)
            ·
              refine ⟨54615294219313647399912853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72820392292418196533217137 54615294219313647399912853)
              ·
                refine ⟨2560091916530327221870915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54615294219313647399912853 2560091916530327221870915)
                ·
                  refine ⟨3840137874795490832806373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2560091916530327221870915 3840137874795490832806373)
                  ·
                    refine ⟨720025851524154531151195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3840137874795490832806373 720025851524154531151195)
                    ·
                      rfl

theorem cell22_2103368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_2103368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103368 prefixEnd_2103368 := by exact prefixLift 2103368
  have htrace : WordTrace (prefixWord ++ tailWord_2103368) baseStart_2103368 baseEnd_2103368 := by
    simpa [prefixWord, tailWord_2103368, baseEnd_2103368] using wordTrace_append hprefix tailTrace_2103368
  have hstable : (prefixWord ++ tailWord_2103368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103368).length < 2 ^ (prefixWord ++ tailWord_2103368).sum := by decide
  have hdescent : baseEnd_2103368 < baseStart_2103368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103385 : List Nat := [1, 2, 1, 2, 2, 1, 7, 1, 1, 4]
def baseStart_2103385 : Nat := 118140960795 + 2103385 * 2 ^ 59
def prefixEnd_2103385 : Nat := 4983230072969 + 3 ^ 40 * 2103385 * 2
def baseEnd_2103385 : Nat := 720031670971572153476143

theorem tailTrace_2103385 : CollatzResearch.WordTrace tailWord_2103385 prefixEnd_2103385 720031670971572153476143 := by
  unfold tailWord_2103385
  simp only [CollatzResearch.WordTrace]
  refine ⟨76716753484802849403383609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51144502323201899602255739 76716753484802849403383609)
  ·
    refine ⟨57537565113602137052537707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76716753484802849403383609 57537565113602137052537707)
    ·
      refine ⟨86306347670403205578806561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57537565113602137052537707 86306347670403205578806561)
      ·
        refine ⟨64729760752802404184104921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86306347670403205578806561 64729760752802404184104921)
        ·
          refine ⟨48547320564601803138078691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64729760752802404184104921 48547320564601803138078691)
          ·
            refine ⟨72820980846902704707118037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48547320564601803138078691 72820980846902704707118037)
            ·
              refine ⟨1706741738599282141573079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 72820980846902704707118037 1706741738599282141573079)
              ·
                refine ⟨2560112607898923212359619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706741738599282141573079 2560112607898923212359619)
                ·
                  refine ⟨3840168911848384818539429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2560112607898923212359619 3840168911848384818539429)
                  ·
                    refine ⟨720031670971572153476143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3840168911848384818539429 720031670971572153476143)
                    ·
                      rfl

theorem cell22_2103385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 1, 4].length) (baseStart_2103385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103385 prefixEnd_2103385 := by exact prefixLift 2103385
  have htrace : WordTrace (prefixWord ++ tailWord_2103385) baseStart_2103385 baseEnd_2103385 := by
    simpa [prefixWord, tailWord_2103385, baseEnd_2103385] using wordTrace_append hprefix tailTrace_2103385
  have hstable : (prefixWord ++ tailWord_2103385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103385).length < 2 ^ (prefixWord ++ tailWord_2103385).sum := by decide
  have hdescent : baseEnd_2103385 < baseStart_2103385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103415 : List Nat := [1, 1, 3, 1, 1, 5, 2, 3, 2, 3]
def baseStart_2103415 : Nat := 118140960795 + 2103415 * 2 ^ 59
def prefixEnd_2103415 : Nat := 4983230072969 + 3 ^ 40 * 2103415 * 2
def baseEnd_2103415 : Nat := 720041940584662075226051

theorem tailTrace_2103415 : CollatzResearch.WordTrace tailWord_2103415 prefixEnd_2103415 720041940584662075226051 := by
  unfold tailWord_2103415
  simp only [CollatzResearch.WordTrace]
  refine ⟨76717847674694164526975699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51145231783129443017983799 76717847674694164526975699)
  ·
    refine ⟨115076771512041246790463549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76717847674694164526975699 115076771512041246790463549)
    ·
      refine ⟨43153789317015467546423831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115076771512041246790463549 43153789317015467546423831)
      ·
        refine ⟨64730683975523201319635747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43153789317015467546423831 64730683975523201319635747)
        ·
          refine ⟨97096025963284801979453621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64730683975523201319635747 97096025963284801979453621)
          ·
            refine ⟨9102752434057950185573777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97096025963284801979453621 9102752434057950185573777)
            ·
              refine ⟨6827064325543462639180333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9102752434057950185573777 6827064325543462639180333)
              ·
                refine ⟨2560149122078798489692625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6827064325543462639180333 2560149122078798489692625)
                ·
                  refine ⟨1920111841559098867269469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2560149122078798489692625 1920111841559098867269469)
                  ·
                    refine ⟨720041940584662075226051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1920111841559098867269469 720041940584662075226051)
                    ·
                      rfl

theorem cell22_2103415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_2103415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103415 prefixEnd_2103415 := by exact prefixLift 2103415
  have htrace : WordTrace (prefixWord ++ tailWord_2103415) baseStart_2103415 baseEnd_2103415 := by
    simpa [prefixWord, tailWord_2103415, baseEnd_2103415] using wordTrace_append hprefix tailTrace_2103415
  have hstable : (prefixWord ++ tailWord_2103415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103415).length < 2 ^ (prefixWord ++ tailWord_2103415).sum := by decide
  have hdescent : baseEnd_2103415 < baseStart_2103415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103443 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 7, 3]
def baseStart_2103443 : Nat := 118140960795 + 2103443 * 2 ^ 59
def prefixEnd_2103443 : Nat := 4983230072969 + 3 ^ 40 * 2103443 * 2
def baseEnd_2103443 : Nat := 720051525556879335525965

theorem tailTrace_2103443 : CollatzResearch.WordTrace tailWord_2103443 prefixEnd_2103443 720051525556879335525965 := by
  unfold tailWord_2103443
  simp only [CollatzResearch.WordTrace]
  refine ⟨76718868918592725308994983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51145912612395150205996655 76718868918592725308994983)
  ·
    refine ⟨115078303377889087963492475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76718868918592725308994983 115078303377889087963492475)
    ·
      refine ⟨172617455066833631945238713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115078303377889087963492475 172617455066833631945238713)
      ·
        refine ⟨129463091300125223958929035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172617455066833631945238713 129463091300125223958929035)
        ·
          refine ⟨194194636950187835938393553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129463091300125223958929035 194194636950187835938393553)
          ·
            refine ⟨145645977712640876953795165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194194636950187835938393553 145645977712640876953795165)
            ·
              refine ⟨54617241642240328857673187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145645977712640876953795165 54617241642240328857673187)
              ·
                refine ⟨81925862463360493286509781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54617241642240328857673187 81925862463360493286509781)
                ·
                  refine ⟨1920137401485011561402573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 81925862463360493286509781 1920137401485011561402573)
                  ·
                    refine ⟨720051525556879335525965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1920137401485011561402573 720051525556879335525965)
                    ·
                      rfl

theorem cell22_2103443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 3].length) (baseStart_2103443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103443 prefixEnd_2103443 := by exact prefixLift 2103443
  have htrace : WordTrace (prefixWord ++ tailWord_2103443) baseStart_2103443 baseEnd_2103443 := by
    simpa [prefixWord, tailWord_2103443, baseEnd_2103443] using wordTrace_append hprefix tailTrace_2103443
  have hstable : (prefixWord ++ tailWord_2103443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103443).length < 2 ^ (prefixWord ++ tailWord_2103443).sum := by decide
  have hdescent : baseEnd_2103443 < baseStart_2103443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103466 : List Nat := [3, 1, 5, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2103466 : Nat := 118140960795 + 2103466 * 2 ^ 59
def prefixEnd_2103466 : Nat := 4983230072969 + 3 ^ 40 * 2103466 * 2
def baseEnd_2103466 : Nat := 720059398926914942200895

theorem tailTrace_2103466 : CollatzResearch.WordTrace tailWord_2103466 prefixEnd_2103466 720059398926914942200895 := by
  unfold tailWord_2103466
  simp only [CollatzResearch.WordTrace]
  refine ⟨19179926949377350059270563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51146471865006266824721501 19179926949377350059270563)
  ·
    refine ⟨28769890424066025088905845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19179926949377350059270563 28769890424066025088905845)
    ·
      refine ⟨2697177227256189852084923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28769890424066025088905845 2697177227256189852084923)
      ·
        refine ⟨4045765840884284778127385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697177227256189852084923 4045765840884284778127385)
        ·
          refine ⟨3034324380663213583595539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4045765840884284778127385 3034324380663213583595539)
          ·
            refine ⟨4551486570994820375393309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3034324380663213583595539 4551486570994820375393309)
            ·
              refine ⟨1706807464123057640772491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4551486570994820375393309 1706807464123057640772491)
              ·
                refine ⟨2560211196184586461158737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706807464123057640772491 2560211196184586461158737)
                ·
                  refine ⟨1920158397138439845869053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2560211196184586461158737 1920158397138439845869053)
                  ·
                    refine ⟨720059398926914942200895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1920158397138439845869053 720059398926914942200895)
                    ·
                      rfl

theorem cell22_2103466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2103466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103466 prefixEnd_2103466 := by exact prefixLift 2103466
  have htrace : WordTrace (prefixWord ++ tailWord_2103466) baseStart_2103466 baseEnd_2103466 := by
    simpa [prefixWord, tailWord_2103466, baseEnd_2103466] using wordTrace_append hprefix tailTrace_2103466
  have hstable : (prefixWord ++ tailWord_2103466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103466).length < 2 ^ (prefixWord ++ tailWord_2103466).sum := by decide
  have hdescent : baseEnd_2103466 < baseStart_2103466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103569 : List Nat := [1, 2, 2, 1, 1, 7, 2, 2, 4]
def baseStart_2103569 : Nat := 118140960795 + 2103569 * 2 ^ 59
def prefixEnd_2103569 : Nat := 4983230072969 + 3 ^ 40 * 2103569 * 2
def baseEnd_2103569 : Nat := 240031552643952335625193

theorem tailTrace_2103569 : CollatzResearch.WordTrace tailWord_2103569 prefixEnd_2103569 240031552643952335625193 := by
  unfold tailWord_2103569
  simp only [CollatzResearch.WordTrace]
  refine ⟨76723464516136248828081761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51148976344090832552054507 76723464516136248828081761)
  ·
    refine ⟨57542598387102186621061321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76723464516136248828081761 57542598387102186621061321)
    ·
      refine ⟨43156948790326639965795991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57542598387102186621061321 43156948790326639965795991)
      ·
        refine ⟨64735423185489959948693987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43156948790326639965795991 64735423185489959948693987)
        ·
          refine ⟨97103134778234939923040981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64735423185489959948693987 97103134778234939923040981)
          ·
            refine ⟨2275854721364881404446273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 97103134778234939923040981 2275854721364881404446273)
            ·
              refine ⟨1706891041023661053334705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2275854721364881404446273 1706891041023661053334705)
              ·
                refine ⟨1280168280767745790001029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1706891041023661053334705 1280168280767745790001029)
                ·
                  refine ⟨240031552643952335625193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1280168280767745790001029 240031552643952335625193)
                  ·
                    rfl

theorem cell22_2103569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 4].length) (baseStart_2103569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103569 prefixEnd_2103569 := by exact prefixLift 2103569
  have htrace : WordTrace (prefixWord ++ tailWord_2103569) baseStart_2103569 baseEnd_2103569 := by
    simpa [prefixWord, tailWord_2103569, baseEnd_2103569] using wordTrace_append hprefix tailTrace_2103569
  have hstable : (prefixWord ++ tailWord_2103569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103569).length < 2 ^ (prefixWord ++ tailWord_2103569).sum := by decide
  have hdescent : baseEnd_2103569 < baseStart_2103569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103715 : List Nat := [1, 1, 1, 4, 1, 4, 2, 8]
def baseStart_2103715 : Nat := 118140960795 + 2103715 * 2 ^ 59
def prefixEnd_2103715 : Nat := 4983230072969 + 3 ^ 40 * 2103715 * 2
def baseEnd_2103715 : Nat := 80016070746173476969459

theorem tailTrace_2103715 : CollatzResearch.WordTrace tailWord_2103715 prefixEnd_2103715 80016070746173476969459 := by
  unfold tailWord_2103715
  simp only [CollatzResearch.WordTrace]
  refine ⟨76728789573607315762896599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51152526382404877175264399 76728789573607315762896599)
  ·
    refine ⟨115093184360410973644344899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76728789573607315762896599 115093184360410973644344899)
    ·
      refine ⟨172639776540616460466517349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115093184360410973644344899 172639776540616460466517349)
      ·
        refine ⟨32369958101365586337472003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172639776540616460466517349 32369958101365586337472003)
        ·
          refine ⟨48554937152048379506208005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32369958101365586337472003 48554937152048379506208005)
          ·
            refine ⟨9104050716009071157414001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48554937152048379506208005 9104050716009071157414001)
            ·
              refine ⟨6828038037006803368060501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9104050716009071157414001 6828038037006803368060501)
              ·
                refine ⟨80016070746173476969459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6828038037006803368060501 80016070746173476969459)
                ·
                  rfl

theorem cell22_2103715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 8].length) (baseStart_2103715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103715 prefixEnd_2103715 := by exact prefixLift 2103715
  have htrace : WordTrace (prefixWord ++ tailWord_2103715) baseStart_2103715 baseEnd_2103715 := by
    simpa [prefixWord, tailWord_2103715, baseEnd_2103715] using wordTrace_append hprefix tailTrace_2103715
  have hstable : (prefixWord ++ tailWord_2103715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103715).length < 2 ^ (prefixWord ++ tailWord_2103715).sum := by decide
  have hdescent : baseEnd_2103715 < baseStart_2103715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103717 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_2103717 : Nat := 118140960795 + 2103717 * 2 ^ 59
def prefixEnd_2103717 : Nat := 4983230072969 + 3 ^ 40 * 2103717 * 2
def baseEnd_2103717 : Nat := 720145321356433954175125

theorem tailTrace_2103717 : CollatzResearch.WordTrace tailWord_2103717 prefixEnd_2103717 720145321356433954175125 := by
  unfold tailWord_2103717
  simp only [CollatzResearch.WordTrace]
  refine ⟨76728862519600070104469405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51152575013066713402979603 76728862519600070104469405)
  ·
    refine ⟨28773323444850026289176027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76728862519600070104469405 28773323444850026289176027)
    ·
      refine ⟨43159985167275039433764041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28773323444850026289176027 43159985167275039433764041)
      ·
        refine ⟨32369988875456279575323031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43159985167275039433764041 32369988875456279575323031)
        ·
          refine ⟨48554983313184419362984547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32369988875456279575323031 48554983313184419362984547)
          ·
            refine ⟨72832474969776629044476821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48554983313184419362984547 72832474969776629044476821)
            ·
              refine ⟨3414022264208279486459851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72832474969776629044476821 3414022264208279486459851)
              ·
                refine ⟨5121033396312419229689777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3414022264208279486459851 5121033396312419229689777)
                ·
                  refine ⟨3840775047234314422267333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5121033396312419229689777 3840775047234314422267333)
                  ·
                    refine ⟨720145321356433954175125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3840775047234314422267333 720145321356433954175125)
                    ·
                      rfl

theorem cell22_2103717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_2103717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103717 prefixEnd_2103717 := by exact prefixLift 2103717
  have htrace : WordTrace (prefixWord ++ tailWord_2103717) baseStart_2103717 baseEnd_2103717 := by
    simpa [prefixWord, tailWord_2103717, baseEnd_2103717] using wordTrace_append hprefix tailTrace_2103717
  have hstable : (prefixWord ++ tailWord_2103717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103717).length < 2 ^ (prefixWord ++ tailWord_2103717).sum := by decide
  have hdescent : baseEnd_2103717 < baseStart_2103717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103747 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 3, 3]
def baseStart_2103747 : Nat := 118140960795 + 2103747 * 2 ^ 59
def prefixEnd_2103747 : Nat := 4983230072969 + 3 ^ 40 * 2103747 * 2
def baseEnd_2103747 : Nat := 720155590969523875925033

theorem tailTrace_2103747 : CollatzResearch.WordTrace tailWord_2103747 prefixEnd_2103747 720155590969523875925033 := by
  unfold tailWord_2103747
  simp only [CollatzResearch.WordTrace]
  refine ⟨76729956709491385228061495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51153304472994256818707663 76729956709491385228061495)
  ·
    refine ⟨115094935064237077842092243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76729956709491385228061495 115094935064237077842092243)
    ·
      refine ⟨172642402596355616763138365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115094935064237077842092243 172642402596355616763138365)
      ·
        refine ⟨64740900973633356286176887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172642402596355616763138365 64740900973633356286176887)
        ·
          refine ⟨97111351460450034429265331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64740900973633356286176887 97111351460450034429265331)
          ·
            refine ⟨145667027190675051643897997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97111351460450034429265331 145667027190675051643897997)
            ·
              refine ⟨54625135196503144366461749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145667027190675051643897997 54625135196503144366461749)
              ·
                refine ⟨5121106424672169784355789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54625135196503144366461749 5121106424672169784355789)
                ·
                  refine ⟨1920414909252063669133421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5121106424672169784355789 1920414909252063669133421)
                  ·
                    refine ⟨720155590969523875925033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1920414909252063669133421 720155590969523875925033)
                    ·
                      rfl

theorem cell22_2103747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 3].length) (baseStart_2103747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103747 prefixEnd_2103747 := by exact prefixLift 2103747
  have htrace : WordTrace (prefixWord ++ tailWord_2103747) baseStart_2103747 baseEnd_2103747 := by
    simpa [prefixWord, tailWord_2103747, baseEnd_2103747] using wordTrace_append hprefix tailTrace_2103747
  have hstable : (prefixWord ++ tailWord_2103747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103747).length < 2 ^ (prefixWord ++ tailWord_2103747).sum := by decide
  have hdescent : baseEnd_2103747 < baseStart_2103747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103764 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_2103764 : Nat := 118140960795 + 2103764 * 2 ^ 59
def prefixEnd_2103764 : Nat := 4983230072969 + 3 ^ 40 * 2103764 * 2
def baseEnd_2103764 : Nat := 720161410416941498249981

theorem tailTrace_2103764 : CollatzResearch.WordTrace tailWord_2103764 prefixEnd_2103764 720161410416941498249981 := by
  unfold tailWord_2103764
  simp only [CollatzResearch.WordTrace]
  refine ⟨38365288375214898565715173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51153717833619864754286897 38365288375214898565715173)
  ·
    refine ⟨7193491570352793481071595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38365288375214898565715173 7193491570352793481071595)
    ·
      refine ⟨10790237355529190221607393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7193491570352793481071595 10790237355529190221607393)
      ·
        refine ⟨8092678016646892666205545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10790237355529190221607393 8092678016646892666205545)
        ·
          refine ⟨6069508512485169499654159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8092678016646892666205545 6069508512485169499654159)
          ·
            refine ⟨9104262768727754249481239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6069508512485169499654159 9104262768727754249481239)
            ·
              refine ⟨13656394153091631374221859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9104262768727754249481239 13656394153091631374221859)
              ·
                refine ⟨20484591229637447061332789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13656394153091631374221859 20484591229637447061332789)
                ·
                  refine ⟨1920430427778510661999949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20484591229637447061332789 1920430427778510661999949)
                  ·
                    refine ⟨720161410416941498249981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1920430427778510661999949 720161410416941498249981)
                    ·
                      rfl

theorem cell22_2103764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_2103764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103764 prefixEnd_2103764 := by exact prefixLift 2103764
  have htrace : WordTrace (prefixWord ++ tailWord_2103764) baseStart_2103764 baseEnd_2103764 := by
    simpa [prefixWord, tailWord_2103764, baseEnd_2103764] using wordTrace_append hprefix tailTrace_2103764
  have hstable : (prefixWord ++ tailWord_2103764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103764).length < 2 ^ (prefixWord ++ tailWord_2103764).sum := by decide
  have hdescent : baseEnd_2103764 < baseStart_2103764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103794 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 7]
def baseStart_2103794 : Nat := 118140960795 + 2103794 * 2 ^ 59
def prefixEnd_2103794 : Nat := 4983230072969 + 3 ^ 40 * 2103794 * 2
def baseEnd_2103794 : Nat := 240057226676677139999963

theorem tailTrace_2103794 : CollatzResearch.WordTrace tailWord_2103794 prefixEnd_2103794 240057226676677139999963 := by
  unfold tailWord_2103794
  simp only [CollatzResearch.WordTrace]
  refine ⟨19182917735080278063755609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51154447293547408170014957 19182917735080278063755609)
  ·
    refine ⟨14387188301310208547816707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19182917735080278063755609 14387188301310208547816707)
    ·
      refine ⟨21580782451965312821725061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14387188301310208547816707 21580782451965312821725061)
      ·
        refine ⟨4046396709743496154073449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21580782451965312821725061 4046396709743496154073449)
        ·
          refine ⟨3034797532307622115555087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4046396709743496154073449 3034797532307622115555087)
          ·
            refine ⟨4552196298461433173332631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3034797532307622115555087 4552196298461433173332631)
            ·
              refine ⟨6828294447692149759998947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4552196298461433173332631 6828294447692149759998947)
              ·
                refine ⟨10242441671538224639998421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6828294447692149759998947 10242441671538224639998421)
                ·
                  refine ⟨240057226676677139999963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10242441671538224639998421 240057226676677139999963)
                  ·
                    rfl

theorem cell22_2103794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_2103794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103794 prefixEnd_2103794 := by exact prefixLift 2103794
  have htrace : WordTrace (prefixWord ++ tailWord_2103794) baseStart_2103794 baseEnd_2103794 := by
    simpa [prefixWord, tailWord_2103794, baseEnd_2103794] using wordTrace_append hprefix tailTrace_2103794
  have hstable : (prefixWord ++ tailWord_2103794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103794).length < 2 ^ (prefixWord ++ tailWord_2103794).sum := by decide
  have hdescent : baseEnd_2103794 < baseStart_2103794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103927 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 1, 7]
def baseStart_2103927 : Nat := 118140960795 + 2103927 * 2 ^ 59
def prefixEnd_2103927 : Nat := 4983230072969 + 3 ^ 40 * 2103927 * 2
def baseEnd_2103927 : Nat := 720217208648063406424481

theorem tailTrace_2103927 : CollatzResearch.WordTrace tailWord_2103927 prefixEnd_2103927 720217208648063406424481 := by
  unfold tailWord_2103927
  simp only [CollatzResearch.WordTrace]
  refine ⟨76736521848839275969614035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51157681232559517313076023 76736521848839275969614035)
  ·
    refine ⟨115104782773258913954421053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76736521848839275969614035 115104782773258913954421053)
    ·
      refine ⟨43164293539972092732907895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115104782773258913954421053 43164293539972092732907895)
      ·
        refine ⟨64746440309958139099361843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43164293539972092732907895 64746440309958139099361843)
        ·
          refine ⟨97119660464937208649042765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64746440309958139099361843 97119660464937208649042765)
          ·
            refine ⟨36419872674351453243391037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97119660464937208649042765 36419872674351453243391037)
            ·
              refine ⟨13657452252881794966271639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36419872674351453243391037 13657452252881794966271639)
              ·
                refine ⟨20486178379322692449407459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13657452252881794966271639 20486178379322692449407459)
                ·
                  refine ⟨30729267568984038674111189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20486178379322692449407459 30729267568984038674111189)
                  ·
                    refine ⟨720217208648063406424481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30729267568984038674111189 720217208648063406424481)
                    ·
                      rfl

theorem cell22_2103927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_2103927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103927 prefixEnd_2103927 := by exact prefixLift 2103927
  have htrace : WordTrace (prefixWord ++ tailWord_2103927) baseStart_2103927 baseEnd_2103927 := by
    simpa [prefixWord, tailWord_2103927, baseEnd_2103927] using wordTrace_append hprefix tailTrace_2103927
  have hstable : (prefixWord ++ tailWord_2103927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103927).length < 2 ^ (prefixWord ++ tailWord_2103927).sum := by decide
  have hdescent : baseEnd_2103927 < baseStart_2103927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2103929 : List Nat := [1, 2, 1, 3, 3, 2, 2, 3, 5]
def baseStart_2103929 : Nat := 118140960795 + 2103929 * 2 ^ 59
def prefixEnd_2103929 : Nat := 4983230072969 + 3 ^ 40 * 2103929 * 2
def baseEnd_2103929 : Nat := 240072631096312022624825

theorem tailTrace_2103929 : CollatzResearch.WordTrace tailWord_2103929 prefixEnd_2103929 240072631096312022624825 := by
  unfold tailWord_2103929
  simp only [CollatzResearch.WordTrace]
  refine ⟨76736594794832030311186841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51157729863221353540791227 76736594794832030311186841)
  ·
    refine ⟨57552446096124022733390131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76736594794832030311186841 57552446096124022733390131)
    ·
      refine ⟨86328669144186034100085197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57552446096124022733390131 86328669144186034100085197)
      ·
        refine ⟨32373250929069762787531949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86328669144186034100085197 32373250929069762787531949)
        ·
          refine ⟨12139969098401161045324481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32373250929069762787531949 12139969098401161045324481)
          ·
            refine ⟨9104976823800870783993361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12139969098401161045324481 9104976823800870783993361)
            ·
              refine ⟨6828732617850653087995021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9104976823800870783993361 6828732617850653087995021)
              ·
                refine ⟨2560774731693994907998133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6828732617850653087995021 2560774731693994907998133)
                ·
                  refine ⟨240072631096312022624825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2560774731693994907998133 240072631096312022624825)
                  ·
                    rfl

theorem cell22_2103929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_2103929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2103929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2103929 prefixEnd_2103929 := by exact prefixLift 2103929
  have htrace : WordTrace (prefixWord ++ tailWord_2103929) baseStart_2103929 baseEnd_2103929 := by
    simpa [prefixWord, tailWord_2103929, baseEnd_2103929] using wordTrace_append hprefix tailTrace_2103929
  have hstable : (prefixWord ++ tailWord_2103929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2103929).length < 2 ^ (prefixWord ++ tailWord_2103929).sum := by decide
  have hdescent : baseEnd_2103929 < baseStart_2103929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2103929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104008 : List Nat := [2, 1, 3, 1, 2, 5, 1, 3, 4]
def baseStart_2104008 : Nat := 118140960795 + 2104008 * 2 ^ 59
def prefixEnd_2104008 : Nat := 4983230072969 + 3 ^ 40 * 2104008 * 2
def baseEnd_2104008 : Nat := 240081645534468731716411

theorem tailTrace_2104008 : CollatzResearch.WordTrace tailWord_2104008 prefixEnd_2104008 240081645534468731716411 := by
  unfold tailWord_2104008
  simp only [CollatzResearch.WordTrace]
  refine ⟨38369738080772913401656339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51159650774363884535541785 38369738080772913401656339)
  ·
    refine ⟨57554607121159370102484509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38369738080772913401656339 57554607121159370102484509)
    ·
      refine ⟨21582977670434763788431691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57554607121159370102484509 21582977670434763788431691)
      ·
        refine ⟨32374466505652145682647537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21582977670434763788431691 32374466505652145682647537)
        ·
          refine ⟨24280849879239109261985653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32374466505652145682647537 24280849879239109261985653)
          ·
            refine ⟨2276329676178666493311155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24280849879239109261985653 2276329676178666493311155)
            ·
              refine ⟨3414494514267999739966733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276329676178666493311155 3414494514267999739966733)
              ·
                refine ⟨1280435442850499902487525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3414494514267999739966733 1280435442850499902487525)
                ·
                  refine ⟨240081645534468731716411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1280435442850499902487525 240081645534468731716411)
                  ·
                    rfl

theorem cell22_2104008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 4].length) (baseStart_2104008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104008 prefixEnd_2104008 := by exact prefixLift 2104008
  have htrace : WordTrace (prefixWord ++ tailWord_2104008) baseStart_2104008 baseEnd_2104008 := by
    simpa [prefixWord, tailWord_2104008, baseEnd_2104008] using wordTrace_append hprefix tailTrace_2104008
  have hstable : (prefixWord ++ tailWord_2104008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104008).length < 2 ^ (prefixWord ++ tailWord_2104008).sum := by decide
  have hdescent : baseEnd_2104008 < baseStart_2104008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104079 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 2, 5]
def baseStart_2104079 : Nat := 118140960795 + 2104079 * 2 ^ 59
def prefixEnd_2104079 : Nat := 4983230072969 + 3 ^ 40 * 2104079 * 2
def baseEnd_2104079 : Nat := 720269241354385676624015

theorem tailTrace_2104079 : CollatzResearch.WordTrace tailWord_2104079 prefixEnd_2104079 720269241354385676624015 := by
  unfold tailWord_2104079
  simp only [CollatzResearch.WordTrace]
  refine ⟨76742065744288605929147291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51161377162859070619431527 76742065744288605929147291)
  ·
    refine ⟨115113098616432908893720937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76742065744288605929147291 115113098616432908893720937)
    ·
      refine ⟨86334823962324681670290703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115113098616432908893720937 86334823962324681670290703)
      ·
        refine ⟨129502235943487022505436055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86334823962324681670290703 129502235943487022505436055)
        ·
          refine ⟨194253353915230533758154083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129502235943487022505436055 194253353915230533758154083)
          ·
            refine ⟨291380030872845800637231125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194253353915230533758154083 291380030872845800637231125)
            ·
              refine ⟨13658438947164646904870209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 291380030872845800637231125 13658438947164646904870209)
              ·
                refine ⟨10243829210373485178652657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13658438947164646904870209 10243829210373485178652657)
                ·
                  refine ⟨7682871907780113883989493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10243829210373485178652657 7682871907780113883989493)
                  ·
                    refine ⟨720269241354385676624015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7682871907780113883989493 720269241354385676624015)
                    ·
                      rfl

theorem cell22_2104079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_2104079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104079 prefixEnd_2104079 := by exact prefixLift 2104079
  have htrace : WordTrace (prefixWord ++ tailWord_2104079) baseStart_2104079 baseEnd_2104079 := by
    simpa [prefixWord, tailWord_2104079, baseEnd_2104079] using wordTrace_append hprefix tailTrace_2104079
  have hstable : (prefixWord ++ tailWord_2104079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104079).length < 2 ^ (prefixWord ++ tailWord_2104079).sum := by decide
  have hdescent : baseEnd_2104079 < baseStart_2104079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104096 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 2, 5]
def baseStart_2104096 : Nat := 118140960795 + 2104096 * 2 ^ 59
def prefixEnd_2104096 : Nat := 4983230072969 + 3 ^ 40 * 2104096 * 2
def baseEnd_2104096 : Nat := 720275060801803298948963

theorem tailTrace_2104096 : CollatzResearch.WordTrace tailWord_2104096 prefixEnd_2104096 720275060801803298948963 := by
  unfold tailWord_2104096
  simp only [CollatzResearch.WordTrace]
  refine ⟨38371342892613508916258071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51161790523484678555010761 38371342892613508916258071)
  ·
    refine ⟨57557014338920263374387107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38371342892613508916258071 57557014338920263374387107)
    ·
      refine ⟨86335521508380395061580661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57557014338920263374387107 86335521508380395061580661)
      ·
        refine ⟨8093955141410662037023187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86335521508380395061580661 8093955141410662037023187)
        ·
          refine ⟨12140932712115993055534781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8093955141410662037023187 12140932712115993055534781)
          ·
            refine ⟨4552849767043497395825543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12140932712115993055534781 4552849767043497395825543)
            ·
              refine ⟨6829274650565246093738315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4552849767043497395825543 6829274650565246093738315)
              ·
                refine ⟨10243911975847869140607473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6829274650565246093738315 10243911975847869140607473)
                ·
                  refine ⟨7682933981885901855455605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10243911975847869140607473 7682933981885901855455605)
                  ·
                    refine ⟨720275060801803298948963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7682933981885901855455605 720275060801803298948963)
                    ·
                      rfl

theorem cell22_2104096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_2104096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104096 prefixEnd_2104096 := by exact prefixLift 2104096
  have htrace : WordTrace (prefixWord ++ tailWord_2104096) baseStart_2104096 baseEnd_2104096 := by
    simpa [prefixWord, tailWord_2104096, baseEnd_2104096] using wordTrace_append hprefix tailTrace_2104096
  have hstable : (prefixWord ++ tailWord_2104096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104096).length < 2 ^ (prefixWord ++ tailWord_2104096).sum := by decide
  have hdescent : baseEnd_2104096 < baseStart_2104096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104132 : List Nat := [2, 3, 4, 2, 1, 2, 1, 2, 5]
def baseStart_2104132 : Nat := 118140960795 + 2104132 * 2 ^ 59
def prefixEnd_2104132 : Nat := 4983230072969 + 3 ^ 40 * 2104132 * 2
def baseEnd_2104132 : Nat := 240095794779170401682951

theorem tailTrace_2104132 : CollatzResearch.WordTrace tailWord_2104132 prefixEnd_2104132 240095794779170401682951 := by
  unfold tailWord_2104132
  simp only [CollatzResearch.WordTrace]
  refine ⟨38371999406548297990413325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51162665875397730653884433 38371999406548297990413325)
  ·
    refine ⟨14389499777455611746404997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38371999406548297990413325 14389499777455611746404997)
    ·
      refine ⟨2698031208272927202450937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14389499777455611746404997 2698031208272927202450937)
      ·
        refine ⟨2023523406204695401838203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2698031208272927202450937 2023523406204695401838203)
        ·
          refine ⟨3035285109307043102757305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023523406204695401838203 3035285109307043102757305)
          ·
            refine ⟨2276463831980282327067979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3035285109307043102757305 2276463831980282327067979)
            ·
              refine ⟨3414695747970423490601969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276463831980282327067979 3414695747970423490601969)
              ·
                refine ⟨2561021810977817617951477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3414695747970423490601969 2561021810977817617951477)
                ·
                  refine ⟨240095794779170401682951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2561021810977817617951477 240095794779170401682951)
                  ·
                    rfl

theorem cell22_2104132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_2104132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104132 prefixEnd_2104132 := by exact prefixLift 2104132
  have htrace : WordTrace (prefixWord ++ tailWord_2104132) baseStart_2104132 baseEnd_2104132 := by
    simpa [prefixWord, tailWord_2104132, baseEnd_2104132] using wordTrace_append hprefix tailTrace_2104132
  have hstable : (prefixWord ++ tailWord_2104132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104132).length < 2 ^ (prefixWord ++ tailWord_2104132).sum := by decide
  have hdescent : baseEnd_2104132 < baseStart_2104132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104171 : List Nat := [1, 1, 1, 1, 2, 2, 8, 6]
def baseStart_2104171 : Nat := 118140960795 + 2104171 * 2 ^ 59
def prefixEnd_2104171 : Nat := 4983230072969 + 3 ^ 40 * 2104171 * 2
def baseEnd_2104171 : Nat := 80033414981614233702637

theorem tailTrace_2104171 : CollatzResearch.WordTrace tailWord_2104171 prefixEnd_2104171 80033414981614233702637 := by
  unfold tailWord_2104171
  simp only [CollatzResearch.WordTrace]
  refine ⟨76745421259955305641496367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51163614173303537094330911 76745421259955305641496367)
  ·
    refine ⟨115118131889932958462244551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76745421259955305641496367 115118131889932958462244551)
    ·
      refine ⟨172677197834899437693366827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115118131889932958462244551 172677197834899437693366827)
      ·
        refine ⟨259015796752349156540050241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172677197834899437693366827 259015796752349156540050241)
        ·
          refine ⟨194261847564261867405037681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259015796752349156540050241 194261847564261867405037681)
          ·
            refine ⟨145696385673196400553778261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194261847564261867405037681 145696385673196400553778261)
            ·
              refine ⟨1707379519607770318989589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 145696385673196400553778261 1707379519607770318989589)
              ·
                refine ⟨80033414981614233702637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1707379519607770318989589 80033414981614233702637)
                ·
                  rfl

theorem cell22_2104171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 6].length) (baseStart_2104171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104171 prefixEnd_2104171 := by exact prefixLift 2104171
  have htrace : WordTrace (prefixWord ++ tailWord_2104171) baseStart_2104171 baseEnd_2104171 := by
    simpa [prefixWord, tailWord_2104171, baseEnd_2104171] using wordTrace_append hprefix tailTrace_2104171
  have hstable : (prefixWord ++ tailWord_2104171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104171).length < 2 ^ (prefixWord ++ tailWord_2104171).sum := by decide
  have hdescent : baseEnd_2104171 < baseStart_2104171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104194 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 6]
def baseStart_2104194 : Nat := 118140960795 + 2104194 * 2 ^ 59
def prefixEnd_2104194 : Nat := 4983230072969 + 3 ^ 40 * 2104194 * 2
def baseEnd_2104194 : Nat := 240102869401521236666221

theorem tailTrace_2104194 : CollatzResearch.WordTrace tailWord_2104194 prefixEnd_2104194 240102869401521236666221 := by
  unfold tailWord_2104194
  simp only [CollatzResearch.WordTrace]
  refine ⟨19186565034717995142395909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51164173425914653713055757 19186565034717995142395909)
  ·
    refine ⟨3597480944009624089199233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19186565034717995142395909 3597480944009624089199233)
    ·
      refine ⟨2698110708007218066899425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3597480944009624089199233 2698110708007218066899425)
      ·
        refine ⟨2023583031005413550174569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2698110708007218066899425 2023583031005413550174569)
        ·
          refine ⟨1517687273254060162630927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2023583031005413550174569 1517687273254060162630927)
          ·
            refine ⟨2276530909881090243946391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517687273254060162630927 2276530909881090243946391)
            ·
              refine ⟨3414796364821635365919587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276530909881090243946391 3414796364821635365919587)
              ·
                refine ⟨5122194547232453048879381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3414796364821635365919587 5122194547232453048879381)
                ·
                  refine ⟨240102869401521236666221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5122194547232453048879381 240102869401521236666221)
                  ·
                    rfl

theorem cell22_2104194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_2104194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104194 prefixEnd_2104194 := by exact prefixLift 2104194
  have htrace : WordTrace (prefixWord ++ tailWord_2104194) baseStart_2104194 baseEnd_2104194 := by
    simpa [prefixWord, tailWord_2104194, baseEnd_2104194] using wordTrace_append hprefix tailTrace_2104194
  have hstable : (prefixWord ++ tailWord_2104194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104194).length < 2 ^ (prefixWord ++ tailWord_2104194).sum := by decide
  have hdescent : baseEnd_2104194 < baseStart_2104194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104203 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 3, 3]
def baseStart_2104203 : Nat := 118140960795 + 2104203 * 2 ^ 59
def prefixEnd_2104203 : Nat := 4983230072969 + 3 ^ 40 * 2104203 * 2
def baseEnd_2104203 : Nat := 720311689088490686523635

theorem tailTrace_2104203 : CollatzResearch.WordTrace tailWord_2104203 prefixEnd_2104203 720311689088490686523635 := by
  unfold tailWord_2104203
  simp only [CollatzResearch.WordTrace]
  refine ⟨76746588395839375106661263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51164392263892916737774175 76746588395839375106661263)
  ·
    refine ⟨115119882593759062659991895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76746588395839375106661263 115119882593759062659991895)
    ·
      refine ⟨172679823890638593989987843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115119882593759062659991895 172679823890638593989987843)
      ·
        refine ⟨259019735835957890984981765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172679823890638593989987843 259019735835957890984981765)
        ·
          refine ⟨48566200469242104559684081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 259019735835957890984981765 48566200469242104559684081)
          ·
            refine ⟨36424650351931578419763061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48566200469242104559684081 36424650351931578419763061)
            ·
              refine ⟨3414810970493585476852787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36424650351931578419763061 3414810970493585476852787)
              ·
                refine ⟨5122216455740378215279181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3414810970493585476852787 5122216455740378215279181)
                ·
                  refine ⟨1920831170902641830729693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5122216455740378215279181 1920831170902641830729693)
                  ·
                    refine ⟨720311689088490686523635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1920831170902641830729693 720311689088490686523635)
                    ·
                      rfl

theorem cell22_2104203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 3].length) (baseStart_2104203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104203 prefixEnd_2104203 := by exact prefixLift 2104203
  have htrace : WordTrace (prefixWord ++ tailWord_2104203) baseStart_2104203 baseEnd_2104203 := by
    simpa [prefixWord, tailWord_2104203, baseEnd_2104203] using wordTrace_append hprefix tailTrace_2104203
  have hstable : (prefixWord ++ tailWord_2104203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104203).length < 2 ^ (prefixWord ++ tailWord_2104203).sum := by decide
  have hdescent : baseEnd_2104203 < baseStart_2104203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104295 : List Nat := [1, 1, 5, 2, 2, 1, 1, 5, 4]
def baseStart_2104295 : Nat := 118140960795 + 2104295 * 2 ^ 59
def prefixEnd_2104295 : Nat := 4983230072969 + 3 ^ 40 * 2104295 * 2
def baseEnd_2104295 : Nat := 240114394189544371074451

theorem tailTrace_2104295 : CollatzResearch.WordTrace tailWord_2104295 prefixEnd_2104295 240114394189544371074451 := by
  unfold tailWord_2104295
  simp only [CollatzResearch.WordTrace]
  refine ⟨76749943911506074819010339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51166629274337383212673559 76749943911506074819010339)
  ·
    refine ⟨115124915867259112228515509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76749943911506074819010339 115124915867259112228515509)
    ·
      refine ⟨10792960862555541771423329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115124915867259112228515509 10792960862555541771423329)
      ·
        refine ⟨8094720646916656328567497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10792960862555541771423329 8094720646916656328567497)
        ·
          refine ⟨6071040485187492246425623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8094720646916656328567497 6071040485187492246425623)
          ·
            refine ⟨9106560727781238369638435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6071040485187492246425623 9106560727781238369638435)
            ·
              refine ⟨13659841091671857554457653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9106560727781238369638435 13659841091671857554457653)
              ·
                refine ⟨1280610102344236645730405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13659841091671857554457653 1280610102344236645730405)
                ·
                  refine ⟨240114394189544371074451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1280610102344236645730405 240114394189544371074451)
                  ·
                    rfl

theorem cell22_2104295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 4].length) (baseStart_2104295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104295 prefixEnd_2104295 := by exact prefixLift 2104295
  have htrace : WordTrace (prefixWord ++ tailWord_2104295) baseStart_2104295 baseEnd_2104295 := by
    simpa [prefixWord, tailWord_2104295, baseEnd_2104295] using wordTrace_append hprefix tailTrace_2104295
  have hstable : (prefixWord ++ tailWord_2104295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104295).length < 2 ^ (prefixWord ++ tailWord_2104295).sum := by decide
  have hdescent : baseEnd_2104295 < baseStart_2104295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
