import V185TrunkScan23Chunk0862

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5107029 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 1, 7]
def baseStart_5107029 : Nat := 118140960795 + 5107029 * 2 ^ 59
def prefixEnd_5107029 : Nat := 4983230072969 + 3 ^ 40 * 5107029 * 2
def baseEnd_5107029 : Nat := 874120197816868153083569

theorem tailTrace_5107029 : CollatzResearch.WordTrace tailWord_5107029 prefixEnd_5107029 874120197816868153083569 := by
  unfold tailWord_5107029
  simp only [CollatzResearch.WordTrace]
  refine ⟨186268650215113618958036141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124179100143409079305357427 186268650215113618958036141)
  ·
    refine ⟨69850743830667607109263553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186268650215113618958036141 69850743830667607109263553)
    ·
      refine ⟨52388057873000705331947665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69850743830667607109263553 52388057873000705331947665)
      ·
        refine ⟨39291043404750528998960749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52388057873000705331947665 39291043404750528998960749)
        ·
          refine ⟨14734141276781448374610281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39291043404750528998960749 14734141276781448374610281)
          ·
            refine ⟨11050605957586086280957711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14734141276781448374610281 11050605957586086280957711)
            ·
              refine ⟨16575908936379129421436567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11050605957586086280957711 16575908936379129421436567)
              ·
                refine ⟨24863863404568694132154851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16575908936379129421436567 24863863404568694132154851)
                ·
                  refine ⟨37295795106853041198232277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24863863404568694132154851 37295795106853041198232277)
                  ·
                    refine ⟨874120197816868153083569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37295795106853041198232277 874120197816868153083569)
                    ·
                      rfl

theorem cell23_5107029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_5107029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107029 prefixEnd_5107029 := by exact prefixLift 5107029
  have htrace : WordTrace (prefixWord ++ tailWord_5107029) baseStart_5107029 baseEnd_5107029 := by
    simpa [prefixWord, tailWord_5107029, baseEnd_5107029] using wordTrace_append hprefix tailTrace_5107029
  have hstable : (prefixWord ++ tailWord_5107029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107029).length < 2 ^ (prefixWord ++ tailWord_5107029).sum := by decide
  have hdescent : baseEnd_5107029 < baseStart_5107029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107069 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_5107069 : Nat := 118140960795 + 5107069 * 2 ^ 59
def prefixEnd_5107069 : Nat := 4983230072969 + 3 ^ 40 * 5107069 * 2
def baseEnd_5107069 : Nat := 2622381132676784302750523

theorem tailTrace_5107069 : CollatzResearch.WordTrace tailWord_5107069 prefixEnd_5107069 2622381132676784302750523 := by
  unfold tailWord_5107069
  simp only [CollatzResearch.WordTrace]
  refine ⟨186270109134968705789492261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124180072756645803859661507 186270109134968705789492261)
  ·
    refine ⟨34925645462806632335529799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186270109134968705789492261 34925645462806632335529799)
    ·
      refine ⟨52388468194209948503294699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34925645462806632335529799 52388468194209948503294699)
      ·
        refine ⟨78582702291314922754942049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52388468194209948503294699 78582702291314922754942049)
        ·
          refine ⟨58937026718486192066206537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78582702291314922754942049 58937026718486192066206537)
          ·
            refine ⟨44202770038864644049654903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58937026718486192066206537 44202770038864644049654903)
            ·
              refine ⟨66304155058296966074482355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44202770038864644049654903 66304155058296966074482355)
              ·
                refine ⟨99456232587445449111723533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66304155058296966074482355 99456232587445449111723533)
                ·
                  refine ⟨37296087220292043416896325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99456232587445449111723533 37296087220292043416896325)
                  ·
                    refine ⟨6993016353804758140668061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37296087220292043416896325 6993016353804758140668061)
                    ·
                      refine ⟨2622381132676784302750523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6993016353804758140668061 2622381132676784302750523)
                      ·
                        rfl

theorem cell23_5107069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_5107069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107069 prefixEnd_5107069 := by exact prefixLift 5107069
  have htrace : WordTrace (prefixWord ++ tailWord_5107069) baseStart_5107069 baseEnd_5107069 := by
    simpa [prefixWord, tailWord_5107069, baseEnd_5107069] using wordTrace_append hprefix tailTrace_5107069
  have hstable : (prefixWord ++ tailWord_5107069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107069).length < 2 ^ (prefixWord ++ tailWord_5107069).sum := by decide
  have hdescent : baseEnd_5107069 < baseStart_5107069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107076 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_5107076 : Nat := 118140960795 + 5107076 * 2 ^ 59
def prefixEnd_5107076 : Nat := 4983230072969 + 3 ^ 40 * 5107076 * 2
def baseEnd_5107076 : Nat := 874128242347121925120997

theorem tailTrace_5107076 : CollatzResearch.WordTrace tailWord_5107076 prefixEnd_5107076 874128242347121925120997 := by
  unfold tailWord_5107076
  simp only [CollatzResearch.WordTrace]
  refine ⟨93135182222971672992498541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124180242963962230656664721 93135182222971672992498541)
  ·
    refine ⟨34925693333614377372186953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93135182222971672992498541 34925693333614377372186953)
    ·
      refine ⟨26194270000210783029140215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34925693333614377372186953 26194270000210783029140215)
      ·
        refine ⟨39291405000316174543710323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26194270000210783029140215 39291405000316174543710323)
        ·
          refine ⟨58937107500474261815565485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39291405000316174543710323 58937107500474261815565485)
          ·
            refine ⟨22101415312677848180837057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58937107500474261815565485 22101415312677848180837057)
            ·
              refine ⟨16576061484508386135627793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22101415312677848180837057 16576061484508386135627793)
              ·
                refine ⟨12432046113381289601720845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16576061484508386135627793 12432046113381289601720845)
                ·
                  refine ⟨4662017292517983600645317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12432046113381289601720845 4662017292517983600645317)
                  ·
                    refine ⟨874128242347121925120997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4662017292517983600645317 874128242347121925120997)
                    ·
                      rfl

theorem cell23_5107076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_5107076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107076 prefixEnd_5107076 := by exact prefixLift 5107076
  have htrace : WordTrace (prefixWord ++ tailWord_5107076) baseStart_5107076 baseEnd_5107076 := by
    simpa [prefixWord, tailWord_5107076, baseEnd_5107076] using wordTrace_append hprefix tailTrace_5107076
  have hstable : (prefixWord ++ tailWord_5107076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107076).length < 2 ^ (prefixWord ++ tailWord_5107076).sum := by decide
  have hdescent : baseEnd_5107076 < baseStart_5107076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107093 : List Nat := [1, 3, 2, 1, 1, 2, 5, 3, 1, 4]
def baseStart_5107093 : Nat := 118140960795 + 5107093 * 2 ^ 59
def prefixEnd_5107093 : Nat := 4983230072969 + 3 ^ 40 * 5107093 * 2
def baseEnd_5107093 : Nat := 874131152070830736283471

theorem tailTrace_5107093 : CollatzResearch.WordTrace tailWord_5107093 prefixEnd_5107093 874131152070830736283471 := by
  unfold tailWord_5107093
  simp only [CollatzResearch.WordTrace]
  refine ⟨186270984486881757888365933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124180656324587838592243955 186270984486881757888365933)
  ·
    refine ⟨69851619182580659208137225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186270984486881757888365933 69851619182580659208137225)
    ·
      refine ⟨52388714386935494406102919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69851619182580659208137225 52388714386935494406102919)
      ·
        refine ⟨78583071580403241609154379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52388714386935494406102919 78583071580403241609154379)
        ·
          refine ⟨117874607370604862413731569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78583071580403241609154379 117874607370604862413731569)
          ·
            refine ⟨88405955527953646810298677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117874607370604862413731569 88405955527953646810298677)
            ·
              refine ⟨8288058330745654388465501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88405955527953646810298677 8288058330745654388465501)
              ·
                refine ⟨3108021874029620395674563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8288058330745654388465501 3108021874029620395674563)
                ·
                  refine ⟨4662032811044430593511845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108021874029620395674563 4662032811044430593511845)
                  ·
                    refine ⟨874131152070830736283471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4662032811044430593511845 874131152070830736283471)
                    ·
                      rfl

theorem cell23_5107093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_5107093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107093 prefixEnd_5107093 := by exact prefixLift 5107093
  have htrace : WordTrace (prefixWord ++ tailWord_5107093) baseStart_5107093 baseEnd_5107093 := by
    simpa [prefixWord, tailWord_5107093, baseEnd_5107093] using wordTrace_append hprefix tailTrace_5107093
  have hstable : (prefixWord ++ tailWord_5107093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107093).length < 2 ^ (prefixWord ++ tailWord_5107093).sum := by decide
  have hdescent : baseEnd_5107093 < baseStart_5107093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107136 : List Nat := [2, 1, 1, 2, 3, 1, 5, 2, 1, 5]
def baseStart_5107136 : Nat := 118140960795 + 5107136 * 2 ^ 59
def prefixEnd_5107136 : Nat := 4983230072969 + 3 ^ 40 * 5107136 * 2
def baseEnd_5107136 : Nat := 874138511960211846870905

theorem tailTrace_5107136 : CollatzResearch.WordTrace tailWord_5107136 prefixEnd_5107136 874138511960211846870905 := by
  unfold tailWord_5107136
  simp only [CollatzResearch.WordTrace]
  refine ⟨93136276412862988116090631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124181701883817317488120841 93136276412862988116090631)
  ·
    refine ⟨139704414619294482174135947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93136276412862988116090631 139704414619294482174135947)
    ·
      refine ⟨209556621928941723261203921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139704414619294482174135947 209556621928941723261203921)
      ·
        refine ⟨157167466446706292445902941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209556621928941723261203921 157167466446706292445902941)
        ·
          refine ⟨58937799917514859667213603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157167466446706292445902941 58937799917514859667213603)
          ·
            refine ⟨88406699876272289500820405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58937799917514859667213603 88406699876272289500820405)
            ·
              refine ⟨8288128113400527140701913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88406699876272289500820405 8288128113400527140701913)
              ·
                refine ⟨6216096085050395355526435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8288128113400527140701913 6216096085050395355526435)
                ·
                  refine ⟨9324144127575593033289653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6216096085050395355526435 9324144127575593033289653)
                  ·
                    refine ⟨874138511960211846870905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9324144127575593033289653 874138511960211846870905)
                    ·
                      rfl

theorem cell23_5107136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 1, 5].length) (baseStart_5107136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107136 prefixEnd_5107136 := by exact prefixLift 5107136
  have htrace : WordTrace (prefixWord ++ tailWord_5107136) baseStart_5107136 baseEnd_5107136 := by
    simpa [prefixWord, tailWord_5107136, baseEnd_5107136] using wordTrace_append hprefix tailTrace_5107136
  have hstable : (prefixWord ++ tailWord_5107136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107136).length < 2 ^ (prefixWord ++ tailWord_5107136).sum := by decide
  have hdescent : baseEnd_5107136 < baseStart_5107136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107143 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 2, 3, 2]
def baseStart_5107143 : Nat := 118140960795 + 5107143 * 2 ^ 59
def prefixEnd_5107143 : Nat := 4983230072969 + 3 ^ 40 * 5107143 * 2
def baseEnd_5107143 : Nat := 2622419130245217013225183

theorem tailTrace_5107143 : CollatzResearch.WordTrace tailWord_5107143 prefixEnd_5107143 2622419130245217013225183 := by
  unfold tailWord_5107143
  simp only [CollatzResearch.WordTrace]
  refine ⟨186272808136700616427686083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124181872091133744285124055 186272808136700616427686083)
  ·
    refine ⟨279409212205050924641529125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186272808136700616427686083 279409212205050924641529125)
    ·
      refine ⟨52389227288447048370286711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279409212205050924641529125 52389227288447048370286711)
      ·
        refine ⟨78583840932670572555430067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52389227288447048370286711 78583840932670572555430067)
        ·
          refine ⟨117875761399005858833145101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78583840932670572555430067 117875761399005858833145101)
          ·
            refine ⟨44203410524627197062429413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117875761399005858833145101 44203410524627197062429413)
            ·
              refine ⟨8288139473367599449205515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44203410524627197062429413 8288139473367599449205515)
              ·
                refine ⟨12432209210051399173808273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8288139473367599449205515 12432209210051399173808273)
                ·
                  refine ⟨9324156907538549380356205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12432209210051399173808273 9324156907538549380356205)
                  ·
                    refine ⟨3496558840326956017633577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9324156907538549380356205 3496558840326956017633577)
                    ·
                      refine ⟨2622419130245217013225183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3496558840326956017633577 2622419130245217013225183)
                      ·
                        rfl

theorem cell23_5107143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_5107143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107143 prefixEnd_5107143 := by exact prefixLift 5107143
  have htrace : WordTrace (prefixWord ++ tailWord_5107143) baseStart_5107143 baseEnd_5107143 := by
    simpa [prefixWord, tailWord_5107143, baseEnd_5107143] using wordTrace_append hprefix tailTrace_5107143
  have hstable : (prefixWord ++ tailWord_5107143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107143).length < 2 ^ (prefixWord ++ tailWord_5107143).sum := by decide
  have hdescent : baseEnd_5107143 < baseStart_5107143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107176 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_5107176 : Nat := 118140960795 + 5107176 * 2 ^ 59
def prefixEnd_5107176 : Nat := 4983230072969 + 3 ^ 40 * 5107176 * 2
def baseEnd_5107176 : Nat := 2622436075106815384112531

theorem tailTrace_5107176 : CollatzResearch.WordTrace tailWord_5107176 prefixEnd_5107176 2622436075106815384112531 := by
  unfold tailWord_5107176
  simp only [CollatzResearch.WordTrace]
  refine ⟨93137005872790531531818691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124182674497054042042424921 93137005872790531531818691)
  ·
    refine ⟨139705508809185797297728037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93137005872790531531818691 139705508809185797297728037)
    ·
      refine ⟨26194782901722336993324007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139705508809185797297728037 26194782901722336993324007)
      ·
        refine ⟨39292174352583505489986011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26194782901722336993324007 39292174352583505489986011)
        ·
          refine ⟨58938261528875258234979017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39292174352583505489986011 58938261528875258234979017)
          ·
            refine ⟨44203696146656443676234263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58938261528875258234979017 44203696146656443676234263)
            ·
              refine ⟨66305544219984665514351395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44203696146656443676234263 66305544219984665514351395)
              ·
                refine ⟨99458316329976998271527093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66305544219984665514351395 99458316329976998271527093)
                ·
                  refine ⟨9324217155935343587955665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99458316329976998271527093 9324217155935343587955665)
                  ·
                    refine ⟨6993162866951507690966749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9324217155935343587955665 6993162866951507690966749)
                    ·
                      refine ⟨2622436075106815384112531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6993162866951507690966749 2622436075106815384112531)
                      ·
                        rfl

theorem cell23_5107176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_5107176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107176 prefixEnd_5107176 := by exact prefixLift 5107176
  have htrace : WordTrace (prefixWord ++ tailWord_5107176) baseStart_5107176 baseEnd_5107176 := by
    simpa [prefixWord, tailWord_5107176, baseEnd_5107176] using wordTrace_append hprefix tailTrace_5107176
  have hstable : (prefixWord ++ tailWord_5107176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107176).length < 2 ^ (prefixWord ++ tailWord_5107176).sum := by decide
  have hdescent : baseEnd_5107176 < baseStart_5107176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107190 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_5107190 : Nat := 118140960795 + 5107190 * 2 ^ 59
def prefixEnd_5107190 : Nat := 4983230072969 + 3 ^ 40 * 5107190 * 2
def baseEnd_5107190 : Nat := 2622443263835978329337467

theorem tailTrace_5107190 : CollatzResearch.WordTrace tailWord_5107190 prefixEnd_5107190 2622443263835978329337467 := by
  unfold tailWord_5107190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11642157647970646465915439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124183014911686895636431349 11642157647970646465915439)
  ·
    refine ⟨17463236471955969698873159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11642157647970646465915439 17463236471955969698873159)
    ·
      refine ⟨26194854707933954548309739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17463236471955969698873159 26194854707933954548309739)
      ·
        refine ⟨39292282061900931822464609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26194854707933954548309739 39292282061900931822464609)
        ·
          refine ⟨29469211546425698866848457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39292282061900931822464609 29469211546425698866848457)
          ·
            refine ⟨22101908659819274150136343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29469211546425698866848457 22101908659819274150136343)
            ·
              refine ⟨33152862989728911225204515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22101908659819274150136343 33152862989728911225204515)
              ·
                refine ⟨49729294484593366837806773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33152862989728911225204515 49729294484593366837806773)
                ·
                  refine ⟨4662121357930628141044385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49729294484593366837806773 4662121357930628141044385)
                  ·
                    refine ⟨3496591018447971105783289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4662121357930628141044385 3496591018447971105783289)
                    ·
                      refine ⟨2622443263835978329337467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3496591018447971105783289 2622443263835978329337467)
                      ·
                        rfl

theorem cell23_5107190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_5107190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107190 prefixEnd_5107190 := by exact prefixLift 5107190
  have htrace : WordTrace (prefixWord ++ tailWord_5107190) baseStart_5107190 baseEnd_5107190 := by
    simpa [prefixWord, tailWord_5107190, baseEnd_5107190] using wordTrace_append hprefix tailTrace_5107190
  have hstable : (prefixWord ++ tailWord_5107190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107190).length < 2 ^ (prefixWord ++ tailWord_5107190).sum := by decide
  have hdescent : baseEnd_5107190 < baseStart_5107190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107207 : List Nat := [1, 1, 4, 3, 2, 1, 1, 5, 1, 2, 2]
def baseStart_5107207 : Nat := 118140960795 + 5107207 * 2 ^ 59
def prefixEnd_5107207 : Nat := 4983230072969 + 3 ^ 40 * 5107207 * 2
def baseEnd_5107207 : Nat := 2622451993007104762824889

theorem tailTrace_5107207 : CollatzResearch.WordTrace tailWord_5107207 prefixEnd_5107207 2622451993007104762824889 := by
  unfold tailWord_5107207
  simp only [CollatzResearch.WordTrace]
  refine ⟨186275142408468755358015875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124183428272312503572010583 186275142408468755358015875)
  ·
    refine ⟨279412713612703133037023813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186275142408468755358015875 279412713612703133037023813)
    ·
      refine ⟨52389883802381837444441965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279412713612703133037023813 52389883802381837444441965)
      ·
        refine ⟨19646206425893189041665737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52389883802381837444441965 19646206425893189041665737)
        ·
          refine ⟨14734654819419891781249303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19646206425893189041665737 14734654819419891781249303)
          ·
            refine ⟨22101982229129837671873955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14734654819419891781249303 22101982229129837671873955)
            ·
              refine ⟨33152973343694756507810933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22101982229129837671873955 33152973343694756507810933)
              ·
                refine ⟨3108091250971383422607275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33152973343694756507810933 3108091250971383422607275)
                ·
                  refine ⟨4662136876457075133910913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108091250971383422607275 4662136876457075133910913)
                  ·
                    refine ⟨3496602657342806350433185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4662136876457075133910913 3496602657342806350433185)
                    ·
                      refine ⟨2622451993007104762824889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3496602657342806350433185 2622451993007104762824889)
                      ·
                        rfl

theorem cell23_5107207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_5107207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107207 prefixEnd_5107207 := by exact prefixLift 5107207
  have htrace : WordTrace (prefixWord ++ tailWord_5107207) baseStart_5107207 baseEnd_5107207 := by
    simpa [prefixWord, tailWord_5107207, baseEnd_5107207] using wordTrace_append hprefix tailTrace_5107207
  have hstable : (prefixWord ++ tailWord_5107207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107207).length < 2 ^ (prefixWord ++ tailWord_5107207).sum := by decide
  have hdescent : baseEnd_5107207 < baseStart_5107207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107210 : List Nat := [3, 1, 2, 2, 2, 2, 4, 1, 1, 2, 3]
def baseStart_5107210 : Nat := 118140960795 + 5107210 * 2 ^ 59
def prefixEnd_5107210 : Nat := 4983230072969 + 3 ^ 40 * 5107210 * 2
def baseEnd_5107210 : Nat := 2622453533449068251087375

theorem tailTrace_5107210 : CollatzResearch.WordTrace tailWord_5107210 prefixEnd_5107210 2622453533449068251087375 := by
  unfold tailWord_5107210
  simp only [CollatzResearch.WordTrace]
  refine ⟨46568812956864471717593771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124183501218305257913583389 46568812956864471717593771)
  ·
    refine ⟨69853219435296707576390657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46568812956864471717593771 69853219435296707576390657)
    ·
      refine ⟨52389914576472530682292993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69853219435296707576390657 52389914576472530682292993)
      ·
        refine ⟨39292435932354398011719745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52389914576472530682292993 39292435932354398011719745)
        ·
          refine ⟨29469326949265798508789809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39292435932354398011719745 29469326949265798508789809)
          ·
            refine ⟨22101995211949348881592357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29469326949265798508789809 22101995211949348881592357)
            ·
              refine ⟨4144124102240502915298567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22101995211949348881592357 4144124102240502915298567)
              ·
                refine ⟨6216186153360754372947851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144124102240502915298567 6216186153360754372947851)
                ·
                  refine ⟨9324279230041131559421777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6216186153360754372947851 9324279230041131559421777)
                  ·
                    refine ⟨6993209422530848669566333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9324279230041131559421777 6993209422530848669566333)
                    ·
                      refine ⟨2622453533449068251087375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6993209422530848669566333 2622453533449068251087375)
                      ·
                        rfl

theorem cell23_5107210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_5107210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107210 prefixEnd_5107210 := by exact prefixLift 5107210
  have htrace : WordTrace (prefixWord ++ tailWord_5107210) baseStart_5107210 baseEnd_5107210 := by
    simpa [prefixWord, tailWord_5107210, baseEnd_5107210] using wordTrace_append hprefix tailTrace_5107210
  have hstable : (prefixWord ++ tailWord_5107210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107210).length < 2 ^ (prefixWord ++ tailWord_5107210).sum := by decide
  have hdescent : baseEnd_5107210 < baseStart_5107210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107279 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 9]
def baseStart_5107279 : Nat := 118140960795 + 5107279 * 2 ^ 59
def prefixEnd_5107279 : Nat := 4983230072969 + 3 ^ 40 * 5107279 * 2
def baseEnd_5107279 : Nat := 2622488963614228481124557

theorem tailTrace_5107279 : CollatzResearch.WordTrace tailWord_5107279 prefixEnd_5107279 2622488963614228481124557 := by
  unfold tailWord_5107279
  simp only [CollatzResearch.WordTrace]
  refine ⟨186277768464207911654636891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124185178976138607769757927 186277768464207911654636891)
  ·
    refine ⟨279416652696311867481955337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186277768464207911654636891 279416652696311867481955337)
    ·
      refine ⟨209562489522233900611466503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279416652696311867481955337 209562489522233900611466503)
      ·
        refine ⟨314343734283350850917199755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209562489522233900611466503 314343734283350850917199755)
        ·
          refine ⟨471515601425026276375799633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314343734283350850917199755 471515601425026276375799633)
          ·
            refine ⟨353636701068769707281849725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471515601425026276375799633 353636701068769707281849725)
            ·
              refine ⟨132613762900788640230693647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 353636701068769707281849725 132613762900788640230693647)
              ·
                refine ⟨198920644351182960346040471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132613762900788640230693647 198920644351182960346040471)
                ·
                  refine ⟨298380966526774440519060707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198920644351182960346040471 298380966526774440519060707)
                  ·
                    refine ⟨447571449790161660778591061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 298380966526774440519060707 447571449790161660778591061)
                    ·
                      refine ⟨2622488963614228481124557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 447571449790161660778591061 2622488963614228481124557)
                      ·
                        rfl

theorem cell23_5107279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_5107279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107279 prefixEnd_5107279 := by exact prefixLift 5107279
  have htrace : WordTrace (prefixWord ++ tailWord_5107279) baseStart_5107279 baseEnd_5107279 := by
    simpa [prefixWord, tailWord_5107279, baseEnd_5107279] using wordTrace_append hprefix tailTrace_5107279
  have hstable : (prefixWord ++ tailWord_5107279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107279).length < 2 ^ (prefixWord ++ tailWord_5107279).sum := by decide
  have hdescent : baseEnd_5107279 < baseStart_5107279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107280 : List Nat := [2, 1, 1, 1, 1, 3, 4, 4, 2, 2, 2]
def baseStart_5107280 : Nat := 118140960795 + 5107280 * 2 ^ 59
def prefixEnd_5107280 : Nat := 4983230072969 + 3 ^ 40 * 5107280 * 2
def baseEnd_5107280 : Nat := 2622489477094882977212053

theorem tailTrace_5107280 : CollatzResearch.WordTrace tailWord_5107280 prefixEnd_5107280 2622489477094882977212053 := by
  unfold tailWord_5107280
  simp only [CollatzResearch.WordTrace]
  refine ⟨93138902468602144412711647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124185203291469525883615529 93138902468602144412711647)
  ·
    refine ⟨139708353702903216619067471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93138902468602144412711647 139708353702903216619067471)
    ·
      refine ⟨209562530554354824928601207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139708353702903216619067471 209562530554354824928601207)
      ·
        refine ⟨314343795831532237392901811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209562530554354824928601207 314343795831532237392901811)
        ·
          refine ⟨471515693747298356089352717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314343795831532237392901811 471515693747298356089352717)
          ·
            refine ⟨176818385155236883533507269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 471515693747298356089352717 176818385155236883533507269)
            ·
              refine ⟨33153447216606915662532613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176818385155236883533507269 33153447216606915662532613)
              ·
                refine ⟨6216271353113796686724865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33153447216606915662532613 6216271353113796686724865)
                ·
                  refine ⟨4662203514835347515043649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6216271353113796686724865 4662203514835347515043649)
                  ·
                    refine ⟨3496652636126510636282737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4662203514835347515043649 3496652636126510636282737)
                    ·
                      refine ⟨2622489477094882977212053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3496652636126510636282737 2622489477094882977212053)
                      ·
                        rfl

theorem cell23_5107280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 2, 2, 2].length) (baseStart_5107280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107280 prefixEnd_5107280 := by exact prefixLift 5107280
  have htrace : WordTrace (prefixWord ++ tailWord_5107280) baseStart_5107280 baseEnd_5107280 := by
    simpa [prefixWord, tailWord_5107280, baseEnd_5107280] using wordTrace_append hprefix tailTrace_5107280
  have hstable : (prefixWord ++ tailWord_5107280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107280).length < 2 ^ (prefixWord ++ tailWord_5107280).sum := by decide
  have hdescent : baseEnd_5107280 < baseStart_5107280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107296 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 3]
def baseStart_5107296 : Nat := 118140960795 + 5107296 * 2 ^ 59
def prefixEnd_5107296 : Nat := 4983230072969 + 3 ^ 40 * 5107296 * 2
def baseEnd_5107296 : Nat := 2622497692785354914611979

theorem tailTrace_5107296 : CollatzResearch.WordTrace tailWord_5107296 prefixEnd_5107296 2622497692785354914611979 := by
  unfold tailWord_5107296
  simp only [CollatzResearch.WordTrace]
  refine ⟨93139194252573161779002871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124185592336764215705337161 93139194252573161779002871)
  ·
    refine ⟨139708791378859742668504307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93139194252573161779002871 139708791378859742668504307)
    ·
      refine ⟨209563187068289614002756461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139708791378859742668504307 209563187068289614002756461)
      ·
        refine ⟨78586195150608605251033673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209563187068289614002756461 78586195150608605251033673)
        ·
          refine ⟨58939646362956453938275255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78586195150608605251033673 58939646362956453938275255)
          ·
            refine ⟨88409469544434680907412883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58939646362956453938275255 88409469544434680907412883)
            ·
              refine ⟨132614204316652021361119325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88409469544434680907412883 132614204316652021361119325)
              ·
                refine ⟨49730326618744508010419747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132614204316652021361119325 49730326618744508010419747)
                ·
                  refine ⟨74595489928116762015629621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49730326618744508010419747 74595489928116762015629621)
                  ·
                    refine ⟨6993327180760946438965277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74595489928116762015629621 6993327180760946438965277)
                    ·
                      refine ⟨2622497692785354914611979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6993327180760946438965277 2622497692785354914611979)
                      ·
                        rfl

theorem cell23_5107296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_5107296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107296 prefixEnd_5107296 := by exact prefixLift 5107296
  have htrace : WordTrace (prefixWord ++ tailWord_5107296) baseStart_5107296 baseEnd_5107296 := by
    simpa [prefixWord, tailWord_5107296, baseEnd_5107296] using wordTrace_append hprefix tailTrace_5107296
  have hstable : (prefixWord ++ tailWord_5107296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107296).length < 2 ^ (prefixWord ++ tailWord_5107296).sum := by decide
  have hdescent : baseEnd_5107296 < baseStart_5107296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107363 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 3, 4]
def baseStart_5107363 : Nat := 118140960795 + 5107363 * 2 ^ 59
def prefixEnd_5107363 : Nat := 4983230072969 + 3 ^ 40 * 5107363 * 2
def baseEnd_5107363 : Nat := 874177365329735384158057

theorem tailTrace_5107363 : CollatzResearch.WordTrace tailWord_5107363 prefixEnd_5107363 874177365329735384158057 := by
  unfold tailWord_5107363
  simp only [CollatzResearch.WordTrace]
  refine ⟨186280832195903594000694743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124187221463935729333796495 186280832195903594000694743)
  ·
    refine ⟨279421248293855391001042115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186280832195903594000694743 279421248293855391001042115)
    ·
      refine ⟨419131872440783086501563173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279421248293855391001042115 419131872440783086501563173)
      ·
        refine ⟨78587226082646828719043095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 419131872440783086501563173 78587226082646828719043095)
        ·
          refine ⟨117880839123970243078564643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78587226082646828719043095 117880839123970243078564643)
          ·
            refine ⟨176821258685955364617846965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117880839123970243078564643 176821258685955364617846965)
            ·
              refine ⟨16576993001808315432923153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176821258685955364617846965 16576993001808315432923153)
              ·
                refine ⟨12432744751356236574692365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16576993001808315432923153 12432744751356236574692365)
                ·
                  refine ⟨4662279281758588715509637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12432744751356236574692365 4662279281758588715509637)
                  ·
                    refine ⟨874177365329735384158057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4662279281758588715509637 874177365329735384158057)
                    ·
                      rfl

theorem cell23_5107363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 4].length) (baseStart_5107363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107363 prefixEnd_5107363 := by exact prefixLift 5107363
  have htrace : WordTrace (prefixWord ++ tailWord_5107363) baseStart_5107363 baseEnd_5107363 := by
    simpa [prefixWord, tailWord_5107363, baseEnd_5107363] using wordTrace_append hprefix tailTrace_5107363
  have hstable : (prefixWord ++ tailWord_5107363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107363).length < 2 ^ (prefixWord ++ tailWord_5107363).sum := by decide
  have hdescent : baseEnd_5107363 < baseStart_5107363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107431 : List Nat := [1, 1, 5, 4, 1, 2, 1, 3, 1, 4]
def baseStart_5107431 : Nat := 118140960795 + 5107431 * 2 ^ 59
def prefixEnd_5107431 : Nat := 4983230072969 + 3 ^ 40 * 5107431 * 2
def baseEnd_5107431 : Nat := 874189004224570628807953

theorem tailTrace_5107431 : CollatzResearch.WordTrace tailWord_5107431 prefixEnd_5107431 874189004224570628807953 := by
  unfold tailWord_5107431
  simp only [CollatzResearch.WordTrace]
  refine ⟨186283312359657241614170147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124188874906438161076113431 186283312359657241614170147)
  ·
    refine ⟨279424968539485862421255221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186283312359657241614170147 279424968539485862421255221)
    ·
      refine ⟨26196090800576799601992677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 279424968539485862421255221 26196090800576799601992677)
      ·
        refine ⟨4911767025108149925373627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26196090800576799601992677 4911767025108149925373627)
        ·
          refine ⟨7367650537662224888060441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4911767025108149925373627 7367650537662224888060441)
          ·
            refine ⟨5525737903246668666045331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7367650537662224888060441 5525737903246668666045331)
            ·
              refine ⟨8288606854870002999067997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525737903246668666045331 8288606854870002999067997)
              ·
                refine ⟨3108227570576251124650499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8288606854870002999067997 3108227570576251124650499)
                ·
                  refine ⟨4662341355864376686975749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108227570576251124650499 4662341355864376686975749)
                  ·
                    refine ⟨874189004224570628807953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4662341355864376686975749 874189004224570628807953)
                    ·
                      rfl

theorem cell23_5107431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_5107431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107431 prefixEnd_5107431 := by exact prefixLift 5107431
  have htrace : WordTrace (prefixWord ++ tailWord_5107431) baseStart_5107431 baseEnd_5107431 := by
    simpa [prefixWord, tailWord_5107431, baseEnd_5107431] using wordTrace_append hprefix tailTrace_5107431
  have hstable : (prefixWord ++ tailWord_5107431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107431).length < 2 ^ (prefixWord ++ tailWord_5107431).sum := by decide
  have hdescent : baseEnd_5107431 < baseStart_5107431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107473 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_5107473 : Nat := 118140960795 + 5107473 * 2 ^ 59
def prefixEnd_5107473 : Nat := 4983230072969 + 3 ^ 40 * 5107473 * 2
def baseEnd_5107473 : Nat := 2622588578861200722098665

theorem tailTrace_5107473 : CollatzResearch.WordTrace tailWord_5107473 prefixEnd_5107473 2622588578861200722098665 := by
  unfold tailWord_5107473
  simp only [CollatzResearch.WordTrace]
  refine ⟨186284844225505082787199073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124189896150336721858132715 186284844225505082787199073)
  ·
    refine ⟨139713633169128812090399305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186284844225505082787199073 139713633169128812090399305)
    ·
      refine ⟨104785224876846609067799479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139713633169128812090399305 104785224876846609067799479)
      ·
        refine ⟨157177837315269913601699219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104785224876846609067799479 157177837315269913601699219)
        ·
          refine ⟨235766755972904870402548829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157177837315269913601699219 235766755972904870402548829)
          ·
            refine ⟨88412533489839326400955811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235766755972904870402548829 88412533489839326400955811)
            ·
              refine ⟨132618800234758989601433717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88412533489839326400955811 132618800234758989601433717)
              ·
                refine ⟨12433012522008655275134411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132618800234758989601433717 12433012522008655275134411)
                ·
                  refine ⟨18649518783012982912701617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12433012522008655275134411 18649518783012982912701617)
                  ·
                    refine ⟨13987139087259737184526213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18649518783012982912701617 13987139087259737184526213)
                    ·
                      refine ⟨2622588578861200722098665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13987139087259737184526213 2622588578861200722098665)
                      ·
                        rfl

theorem cell23_5107473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_5107473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107473 prefixEnd_5107473 := by exact prefixLift 5107473
  have htrace : WordTrace (prefixWord ++ tailWord_5107473) baseStart_5107473 baseEnd_5107473 := by
    simpa [prefixWord, tailWord_5107473, baseEnd_5107473] using wordTrace_append hprefix tailTrace_5107473
  have hstable : (prefixWord ++ tailWord_5107473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107473).length < 2 ^ (prefixWord ++ tailWord_5107473).sum := by decide
  have hdescent : baseEnd_5107473 < baseStart_5107473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107474 : List Nat := [3, 2, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_5107474 : Nat := 118140960795 + 5107474 * 2 ^ 59
def prefixEnd_5107474 : Nat := 4983230072969 + 3 ^ 40 * 5107474 * 2
def baseEnd_5107474 : Nat := 874196364113951739395387

theorem tailTrace_5107474 : CollatzResearch.WordTrace tailWord_5107474 prefixEnd_5107474 874196364113951739395387 := by
  unfold tailWord_5107474
  simp only [CollatzResearch.WordTrace]
  refine ⟨46571220174625364989496369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124189920465667639971990317 46571220174625364989496369)
  ·
    refine ⟨34928415130969023742122277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46571220174625364989496369 34928415130969023742122277)
    ·
      refine ⟨6549077837056691951647927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34928415130969023742122277 6549077837056691951647927)
      ·
        refine ⟨9823616755585037927471891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6549077837056691951647927 9823616755585037927471891)
        ·
          refine ⟨14735425133377556891207837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9823616755585037927471891 14735425133377556891207837)
          ·
            refine ⟨5525784425016583834202939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14735425133377556891207837 5525784425016583834202939)
            ·
              refine ⟨8288676637524875751304409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525784425016583834202939 8288676637524875751304409)
              ·
                refine ⟨6216507478143656813478307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8288676637524875751304409 6216507478143656813478307)
                ·
                  refine ⟨9324761217215485220217461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6216507478143656813478307 9324761217215485220217461)
                  ·
                    refine ⟨874196364113951739395387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9324761217215485220217461 874196364113951739395387)
                    ·
                      rfl

theorem cell23_5107474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_5107474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107474 prefixEnd_5107474 := by exact prefixLift 5107474
  have htrace : WordTrace (prefixWord ++ tailWord_5107474) baseStart_5107474 baseEnd_5107474 := by
    simpa [prefixWord, tailWord_5107474, baseEnd_5107474] using wordTrace_append hprefix tailTrace_5107474
  have hstable : (prefixWord ++ tailWord_5107474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107474).length < 2 ^ (prefixWord ++ tailWord_5107474).sum := by decide
  have hdescent : baseEnd_5107474 < baseStart_5107474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107477 : List Nat := [1, 3, 2, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_5107477 : Nat := 118140960795 + 5107477 * 2 ^ 59
def prefixEnd_5107477 : Nat := 4983230072969 + 3 ^ 40 * 5107477 * 2
def baseEnd_5107477 : Nat := 2622590632783818706448647

theorem tailTrace_5107477 : CollatzResearch.WordTrace tailWord_5107477 prefixEnd_5107477 2622590632783818706448647 := by
  unfold tailWord_5107477
  simp only [CollatzResearch.WordTrace]
  refine ⟨186284990117490591470344685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124189993411660394313563123 186284990117490591470344685)
  ·
    refine ⟨69856871294058971801379257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186284990117490591470344685 69856871294058971801379257)
    ·
      refine ⟨52392653470544228851034443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69856871294058971801379257 52392653470544228851034443)
      ·
        refine ⟨78588980205816343276551665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52392653470544228851034443 78588980205816343276551665)
        ·
          refine ⟨58941735154362257457413749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78588980205816343276551665 58941735154362257457413749)
          ·
            refine ⟨5525787670721461636632539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58941735154362257457413749 5525787670721461636632539)
            ·
              refine ⟨8288681506082192454948809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525787670721461636632539 8288681506082192454948809)
              ·
                refine ⟨6216511129561644341211607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8288681506082192454948809 6216511129561644341211607)
                ·
                  refine ⟨9324766694342466511817411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6216511129561644341211607 9324766694342466511817411)
                  ·
                    refine ⟨13987150041513699767726117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9324766694342466511817411 13987150041513699767726117)
                    ·
                      refine ⟨2622590632783818706448647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13987150041513699767726117 2622590632783818706448647)
                      ·
                        rfl

theorem cell23_5107477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_5107477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107477 prefixEnd_5107477 := by exact prefixLift 5107477
  have htrace : WordTrace (prefixWord ++ tailWord_5107477) baseStart_5107477 baseEnd_5107477 := by
    simpa [prefixWord, tailWord_5107477, baseEnd_5107477] using wordTrace_append hprefix tailTrace_5107477
  have hstable : (prefixWord ++ tailWord_5107477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107477).length < 2 ^ (prefixWord ++ tailWord_5107477).sum := by decide
  have hdescent : baseEnd_5107477 < baseStart_5107477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107490 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_5107490 : Nat := 118140960795 + 5107490 * 2 ^ 59
def prefixEnd_5107490 : Nat := 4983230072969 + 3 ^ 40 * 5107490 * 2
def baseEnd_5107490 : Nat := 2622597308032327155586087

theorem tailTrace_5107490 : CollatzResearch.WordTrace tailWord_5107490 prefixEnd_5107490 2622597308032327155586087 := by
  unfold tailWord_5107490
  simp only [CollatzResearch.WordTrace]
  refine ⟨46571366066610873672641981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124190309510962329793711949 46571366066610873672641981)
  ·
    refine ⟨17464262274979077627240743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46571366066610873672641981 17464262274979077627240743)
    ·
      refine ⟨26196393412468616440861115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17464262274979077627240743 26196393412468616440861115)
      ·
        refine ⟨39294590118702924661291673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26196393412468616440861115 39294590118702924661291673)
        ·
          refine ⟨29470942589027193495968755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39294590118702924661291673 29470942589027193495968755)
          ·
            refine ⟨44206413883540790243953133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29470942589027193495968755 44206413883540790243953133)
            ·
              refine ⟨16577405206327796341482425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44206413883540790243953133 16577405206327796341482425)
              ·
                refine ⟨12433053904745847256111819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16577405206327796341482425 12433053904745847256111819)
                ·
                  refine ⟨18649580857118770884167729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12433053904745847256111819 18649580857118770884167729)
                  ·
                    refine ⟨13987185642839078163125797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18649580857118770884167729 13987185642839078163125797)
                    ·
                      refine ⟨2622597308032327155586087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13987185642839078163125797 2622597308032327155586087)
                      ·
                        rfl

theorem cell23_5107490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_5107490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107490 prefixEnd_5107490 := by exact prefixLift 5107490
  have htrace : WordTrace (prefixWord ++ tailWord_5107490) baseStart_5107490 baseEnd_5107490 := by
    simpa [prefixWord, tailWord_5107490, baseEnd_5107490] using wordTrace_append hprefix tailTrace_5107490
  have hstable : (prefixWord ++ tailWord_5107490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107490).length < 2 ^ (prefixWord ++ tailWord_5107490).sum := by decide
  have hdescent : baseEnd_5107490 < baseStart_5107490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107527 : List Nat := [1, 1, 4, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_5107527 : Nat := 118140960795 + 5107527 * 2 ^ 59
def prefixEnd_5107527 : Nat := 4983230072969 + 3 ^ 40 * 5107527 * 2
def baseEnd_5107527 : Nat := 2622616306816543510823417

theorem tailTrace_5107527 : CollatzResearch.WordTrace tailWord_5107527 prefixEnd_5107527 2622616306816543510823417 := by
  unfold tailWord_5107527
  simp only [CollatzResearch.WordTrace]
  refine ⟨186286813767309450009664835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124191209178206300006443223 186286813767309450009664835)
  ·
    refine ⟨279430220650964175014497253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186286813767309450009664835 279430220650964175014497253)
    ·
      refine ⟨52393166372055782815218235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279430220650964175014497253 52393166372055782815218235)
      ·
        refine ⟨78589749558083674222827353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52393166372055782815218235 78589749558083674222827353)
        ·
          refine ⟨58942312168562755667120515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78589749558083674222827353 58942312168562755667120515)
          ·
            refine ⟨88413468252844133500680773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58942312168562755667120515 88413468252844133500680773)
            ·
              refine ⟨16577525297408275031377645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88413468252844133500680773 16577525297408275031377645)
              ·
                refine ⟨6216571986528103136766617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16577525297408275031377645 6216571986528103136766617)
                ·
                  refine ⟨4662428989896077352574963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6216571986528103136766617 4662428989896077352574963)
                  ·
                    refine ⟨6993643484844116028862445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4662428989896077352574963 6993643484844116028862445)
                    ·
                      refine ⟨2622616306816543510823417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6993643484844116028862445 2622616306816543510823417)
                      ·
                        rfl

theorem cell23_5107527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_5107527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107527 prefixEnd_5107527 := by exact prefixLift 5107527
  have htrace : WordTrace (prefixWord ++ tailWord_5107527) baseStart_5107527 baseEnd_5107527 := by
    simpa [prefixWord, tailWord_5107527, baseEnd_5107527] using wordTrace_append hprefix tailTrace_5107527
  have hstable : (prefixWord ++ tailWord_5107527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107527).length < 2 ^ (prefixWord ++ tailWord_5107527).sum := by decide
  have hdescent : baseEnd_5107527 < baseStart_5107527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107537 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 3, 3, 2]
def baseStart_5107537 : Nat := 118140960795 + 5107537 * 2 ^ 59
def prefixEnd_5107537 : Nat := 4983230072969 + 3 ^ 40 * 5107537 * 2
def baseEnd_5107537 : Nat := 2622621441623088471698371

theorem tailTrace_5107537 : CollatzResearch.WordTrace tailWord_5107537 prefixEnd_5107537 2622621441623088471698371 := by
  unfold tailWord_5107537
  simp only [CollatzResearch.WordTrace]
  refine ⟨186287178497273221717528865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124191452331515481145019243 186287178497273221717528865)
  ·
    refine ⟨139715383872954916288146649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186287178497273221717528865 139715383872954916288146649)
    ·
      refine ⟨104786537904716187216109987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139715383872954916288146649 104786537904716187216109987)
      ·
        refine ⟨157179806857074280824164981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104786537904716187216109987 157179806857074280824164981)
        ·
          refine ⟨14735606892850713827265467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157179806857074280824164981 14735606892850713827265467)
          ·
            refine ⟨22103410339276070740898201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14735606892850713827265467 22103410339276070740898201)
            ·
              refine ⟨16577557754457053055673651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22103410339276070740898201 16577557754457053055673651)
              ·
                refine ⟨24866336631685579583510477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16577557754457053055673651 24866336631685579583510477)
                ·
                  refine ⟨9324876236882092343816429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24866336631685579583510477 9324876236882092343816429)
                  ·
                    refine ⟨3496828588830784628931161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9324876236882092343816429 3496828588830784628931161)
                    ·
                      refine ⟨2622621441623088471698371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3496828588830784628931161 2622621441623088471698371)
                      ·
                        rfl

theorem cell23_5107537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 3, 2].length) (baseStart_5107537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107537 prefixEnd_5107537 := by exact prefixLift 5107537
  have htrace : WordTrace (prefixWord ++ tailWord_5107537) baseStart_5107537 baseEnd_5107537 := by
    simpa [prefixWord, tailWord_5107537, baseEnd_5107537] using wordTrace_append hprefix tailTrace_5107537
  have hstable : (prefixWord ++ tailWord_5107537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107537).length < 2 ^ (prefixWord ++ tailWord_5107537).sum := by decide
  have hdescent : baseEnd_5107537 < baseStart_5107537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107548 : List Nat := [2, 2, 4, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_5107548 : Nat := 118140960795 + 5107548 * 2 ^ 59
def prefixEnd_5107548 : Nat := 4983230072969 + 3 ^ 40 * 5107548 * 2
def baseEnd_5107548 : Nat := 2622627089910287928660821

theorem tailTrace_5107548 : CollatzResearch.WordTrace tailWord_5107548 prefixEnd_5107548 2622627089910287928660821 := by
  unfold tailWord_5107548
  simp only [CollatzResearch.WordTrace]
  refine ⟨93143789850116685298089649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124191719800155580397452865 93143789850116685298089649)
  ·
    refine ⟨69857842387587513973567237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93143789850116685298089649 69857842387587513973567237)
    ·
      refine ⟨13098345447672658870043857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69857842387587513973567237 13098345447672658870043857)
      ·
        refine ⟨9823759085754494152532893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13098345447672658870043857 9823759085754494152532893)
        ·
          refine ⟨3683909657157935307199835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9823759085754494152532893 3683909657157935307199835)
          ·
            refine ⟨5525864485736902960799753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683909657157935307199835 5525864485736902960799753)
            ·
              refine ⟨4144398364302677220599815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5525864485736902960799753 4144398364302677220599815)
              ·
                refine ⟨6216597546454015830899723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144398364302677220599815 6216597546454015830899723)
                ·
                  refine ⟨9324896319681023746349585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6216597546454015830899723 9324896319681023746349585)
                  ·
                    refine ⟨6993672239760767809762189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9324896319681023746349585 6993672239760767809762189)
                    ·
                      refine ⟨2622627089910287928660821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6993672239760767809762189 2622627089910287928660821)
                      ·
                        rfl

theorem cell23_5107548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_5107548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107548 prefixEnd_5107548 := by exact prefixLift 5107548
  have htrace : WordTrace (prefixWord ++ tailWord_5107548) baseStart_5107548 baseEnd_5107548 := by
    simpa [prefixWord, tailWord_5107548, baseEnd_5107548] using wordTrace_append hprefix tailTrace_5107548
  have hstable : (prefixWord ++ tailWord_5107548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107548).length < 2 ^ (prefixWord ++ tailWord_5107548).sum := by decide
  have hdescent : baseEnd_5107548 < baseStart_5107548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107553 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_5107553 : Nat := 118140960795 + 5107553 * 2 ^ 59
def prefixEnd_5107553 : Nat := 4983230072969 + 3 ^ 40 * 5107553 * 2
def baseEnd_5107553 : Nat := 2622629657313560409098297

theorem tailTrace_5107553 : CollatzResearch.WordTrace tailWord_5107553 prefixEnd_5107553 2622629657313560409098297 := by
  unfold tailWord_5107553
  simp only [CollatzResearch.WordTrace]
  refine ⟨186287762065215256450111313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124191841376810170966740875 186287762065215256450111313)
  ·
    refine ⟨139715821548911442337583485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186287762065215256450111313 139715821548911442337583485)
    ·
      refine ⟨52393433080841790876593807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139715821548911442337583485 52393433080841790876593807)
      ·
        refine ⟨78590149621262686314890711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52393433080841790876593807 78590149621262686314890711)
        ·
          refine ⟨117885224431894029472336067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78590149621262686314890711 117885224431894029472336067)
          ·
            refine ⟨176827836647841044208504101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117885224431894029472336067 176827836647841044208504101)
            ·
              refine ⟨33155219371470195789094519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176827836647841044208504101 33155219371470195789094519)
              ·
                refine ⟨49732829057205293683641779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33155219371470195789094519 49732829057205293683641779)
                ·
                  refine ⟨74599243585807940525462669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49732829057205293683641779 74599243585807940525462669)
                  ·
                    refine ⟨27974716344677977697048501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74599243585807940525462669 27974716344677977697048501)
                    ·
                      refine ⟨2622629657313560409098297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27974716344677977697048501 2622629657313560409098297)
                      ·
                        rfl

theorem cell23_5107553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_5107553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107553 prefixEnd_5107553 := by exact prefixLift 5107553
  have htrace : WordTrace (prefixWord ++ tailWord_5107553) baseStart_5107553 baseEnd_5107553 := by
    simpa [prefixWord, tailWord_5107553, baseEnd_5107553] using wordTrace_append hprefix tailTrace_5107553
  have hstable : (prefixWord ++ tailWord_5107553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107553).length < 2 ^ (prefixWord ++ tailWord_5107553).sum := by decide
  have hdescent : baseEnd_5107553 < baseStart_5107553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107607 : List Nat := [1, 1, 3, 3, 1, 3, 3, 3, 5]
def baseStart_5107607 : Nat := 118140960795 + 5107607 * 2 ^ 59
def prefixEnd_5107607 : Nat := 4983230072969 + 3 ^ 40 * 5107607 * 2
def baseEnd_5107607 : Nat := 291406376140989244202561

theorem tailTrace_5107607 : CollatzResearch.WordTrace tailWord_5107607 prefixEnd_5107607 291406376140989244202561 := by
  unfold tailWord_5107607
  simp only [CollatzResearch.WordTrace]
  refine ⟨186289731607019623672577075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124193154404679749115051383 186289731607019623672577075)
  ·
    refine ⟨279434597410529435508865613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186289731607019623672577075 279434597410529435508865613)
    ·
      refine ⟨104787974028948538315824605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279434597410529435508865613 104787974028948538315824605)
      ·
        refine ⟨39295490260855701868434227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104787974028948538315824605 39295490260855701868434227)
        ·
          refine ⟨58943235391283552802651341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39295490260855701868434227 58943235391283552802651341)
          ·
            refine ⟨22103713271731332300994253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58943235391283552802651341 22103713271731332300994253)
            ·
              refine ⟨8288892476899249612872845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22103713271731332300994253 8288892476899249612872845)
              ·
                refine ⟨3108334678837218604827317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8288892476899249612872845 3108334678837218604827317)
                ·
                  refine ⟨291406376140989244202561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3108334678837218604827317 291406376140989244202561)
                  ·
                    rfl

theorem cell23_5107607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 5].length) (baseStart_5107607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107607 prefixEnd_5107607 := by exact prefixLift 5107607
  have htrace : WordTrace (prefixWord ++ tailWord_5107607) baseStart_5107607 baseEnd_5107607 := by
    simpa [prefixWord, tailWord_5107607, baseEnd_5107607] using wordTrace_append hprefix tailTrace_5107607
  have hstable : (prefixWord ++ tailWord_5107607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107607).length < 2 ^ (prefixWord ++ tailWord_5107607).sum := by decide
  have hdescent : baseEnd_5107607 < baseStart_5107607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107620 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_5107620 : Nat := 118140960795 + 5107620 * 2 ^ 59
def prefixEnd_5107620 : Nat := 4983230072969 + 3 ^ 40 * 5107620 * 2
def baseEnd_5107620 : Nat := 874221353505803882320163

theorem tailTrace_5107620 : CollatzResearch.WordTrace tailWord_5107620 prefixEnd_5107620 874221353505803882320163 := by
  unfold tailWord_5107620
  simp only [CollatzResearch.WordTrace]
  refine ⟨93145102877986263446400157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124193470503981684595200209 93145102877986263446400157)
  ·
    refine ⟨34929413579244848792400059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93145102877986263446400157 34929413579244848792400059)
    ·
      refine ⟨52394120368867273188600089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34929413579244848792400059 52394120368867273188600089)
      ·
        refine ⟨39295590276650454891450067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52394120368867273188600089 39295590276650454891450067)
        ·
          refine ⟨58943385414975682337175101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39295590276650454891450067 58943385414975682337175101)
          ·
            refine ⟨22103769530615880876440663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58943385414975682337175101 22103769530615880876440663)
            ·
              refine ⟨33155654295923821314660995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22103769530615880876440663 33155654295923821314660995)
              ·
                refine ⟨49733481443885731971991493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33155654295923821314660995 49733481443885731971991493)
                ·
                  refine ⟨9325027770728574744748405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49733481443885731971991493 9325027770728574744748405)
                  ·
                    refine ⟨874221353505803882320163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9325027770728574744748405 874221353505803882320163)
                    ·
                      rfl

theorem cell23_5107620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_5107620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107620 prefixEnd_5107620 := by exact prefixLift 5107620
  have htrace : WordTrace (prefixWord ++ tailWord_5107620) baseStart_5107620 baseEnd_5107620 := by
    simpa [prefixWord, tailWord_5107620, baseEnd_5107620] using wordTrace_append hprefix tailTrace_5107620
  have hstable : (prefixWord ++ tailWord_5107620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107620).length < 2 ^ (prefixWord ++ tailWord_5107620).sum := by decide
  have hdescent : baseEnd_5107620 < baseStart_5107620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107640 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_5107640 : Nat := 118140960795 + 5107640 * 2 ^ 59
def prefixEnd_5107640 : Nat := 4983230072969 + 3 ^ 40 * 5107640 * 2
def baseEnd_5107640 : Nat := 2622674330130501568710397

theorem tailTrace_5107640 : CollatzResearch.WordTrace tailWord_5107640 prefixEnd_5107640 2622674330130501568710397 := by
  unfold tailWord_5107640
  simp only [CollatzResearch.WordTrace]
  refine ⟨93145467607950035154264187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124193956810600046872352249 93145467607950035154264187)
  ·
    refine ⟨139718201411925052731396281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93145467607950035154264187 139718201411925052731396281)
    ·
      refine ⟨104788651058943789548547211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139718201411925052731396281 104788651058943789548547211)
      ·
        refine ⟨157182976588415684322820817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104788651058943789548547211 157182976588415684322820817)
        ·
          refine ⟨117887232441311763242115613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157182976588415684322820817 117887232441311763242115613)
          ·
            refine ⟨44207712165491911215793355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117887232441311763242115613 44207712165491911215793355)
            ·
              refine ⟨66311568248237866823690033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44207712165491911215793355 66311568248237866823690033)
              ·
                refine ⟨49733676186178400117767525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66311568248237866823690033 49733676186178400117767525)
                ·
                  refine ⟨9325064284908450022081411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49733676186178400117767525 9325064284908450022081411)
                  ·
                    refine ⟨13987596427362675033122117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9325064284908450022081411 13987596427362675033122117)
                    ·
                      refine ⟨2622674330130501568710397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13987596427362675033122117 2622674330130501568710397)
                      ·
                        rfl

theorem cell23_5107640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_5107640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107640 prefixEnd_5107640 := by exact prefixLift 5107640
  have htrace : WordTrace (prefixWord ++ tailWord_5107640) baseStart_5107640 baseEnd_5107640 := by
    simpa [prefixWord, tailWord_5107640, baseEnd_5107640] using wordTrace_append hprefix tailTrace_5107640
  have hstable : (prefixWord ++ tailWord_5107640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107640).length < 2 ^ (prefixWord ++ tailWord_5107640).sum := by decide
  have hdescent : baseEnd_5107640 < baseStart_5107640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107684 : List Nat := [2, 3, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_5107684 : Nat := 118140960795 + 5107684 * 2 ^ 59
def prefixEnd_5107684 : Nat := 4983230072969 + 3 ^ 40 * 5107684 * 2
def baseEnd_5107684 : Nat := 874232307759766465520065

theorem tailTrace_5107684 : CollatzResearch.WordTrace tailWord_5107684 prefixEnd_5107684 874232307759766465520065 := by
  unfold tailWord_5107684
  simp only [CollatzResearch.WordTrace]
  refine ⟨93146270013870332911565053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124195026685160443882086737 93146270013870332911565053)
  ·
    refine ⟨34929851255201374841836895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93146270013870332911565053 34929851255201374841836895)
    ·
      refine ⟨52394776882802062262755343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34929851255201374841836895 52394776882802062262755343)
      ·
        refine ⟨78592165324203093394133015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52394776882802062262755343 78592165324203093394133015)
        ·
          refine ⟨117888247986304640091199523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78592165324203093394133015 117888247986304640091199523)
          ·
            refine ⟨176832371979456960136799285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117888247986304640091199523 176832371979456960136799285)
            ·
              refine ⟨16578034873074090012824933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176832371979456960136799285 16578034873074090012824933)
              ·
                refine ⟨3108381538701391877404675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16578034873074090012824933 3108381538701391877404675)
                ·
                  refine ⟨4662572308052087816107013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108381538701391877404675 4662572308052087816107013)
                  ·
                    refine ⟨874232307759766465520065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4662572308052087816107013 874232307759766465520065)
                    ·
                      rfl

theorem cell23_5107684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_5107684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107684 prefixEnd_5107684 := by exact prefixLift 5107684
  have htrace : WordTrace (prefixWord ++ tailWord_5107684) baseStart_5107684 baseEnd_5107684 := by
    simpa [prefixWord, tailWord_5107684, baseEnd_5107684] using wordTrace_append hprefix tailTrace_5107684
  have hstable : (prefixWord ++ tailWord_5107684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107684).length < 2 ^ (prefixWord ++ tailWord_5107684).sum := by decide
  have hdescent : baseEnd_5107684 < baseStart_5107684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107707 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 5, 1, 3]
def baseStart_5107707 : Nat := 118140960795 + 5107707 * 2 ^ 59
def prefixEnd_5107707 : Nat := 4983230072969 + 3 ^ 40 * 5107707 * 2
def baseEnd_5107707 : Nat := 2622708733334352806572589

theorem tailTrace_5107707 : CollatzResearch.WordTrace tailWord_5107707 prefixEnd_5107707 2622708733334352806572589 := by
  unfold tailWord_5107707
  simp only [CollatzResearch.WordTrace]
  refine ⟨186293378906657340751217375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124195585937771560500811583 186293378906657340751217375)
  ·
    refine ⟨279440068359986011126826063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186293378906657340751217375 279440068359986011126826063)
    ·
      refine ⟨419160102539979016690239095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279440068359986011126826063 419160102539979016690239095)
      ·
        refine ⟨628740153809968525035358643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419160102539979016690239095 628740153809968525035358643)
        ·
          refine ⟨943110230714952787553037965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628740153809968525035358643 943110230714952787553037965)
          ·
            refine ⟨353666336518107295332389237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 943110230714952787553037965 353666336518107295332389237)
            ·
              refine ⟨33156219048572558937411491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 353666336518107295332389237 33156219048572558937411491)
              ·
                refine ⟨49734328572858838406117237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33156219048572558937411491 49734328572858838406117237)
                ·
                  refine ⟨4662593303705516100573491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49734328572858838406117237 4662593303705516100573491)
                  ·
                    refine ⟨6993889955558274150860237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4662593303705516100573491 6993889955558274150860237)
                    ·
                      refine ⟨2622708733334352806572589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6993889955558274150860237 2622708733334352806572589)
                      ·
                        rfl

theorem cell23_5107707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 1, 3].length) (baseStart_5107707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107707 prefixEnd_5107707 := by exact prefixLift 5107707
  have htrace : WordTrace (prefixWord ++ tailWord_5107707) baseStart_5107707 baseEnd_5107707 := by
    simpa [prefixWord, tailWord_5107707, baseEnd_5107707] using wordTrace_append hprefix tailTrace_5107707
  have hstable : (prefixWord ++ tailWord_5107707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107707).length < 2 ^ (prefixWord ++ tailWord_5107707).sum := by decide
  have hdescent : baseEnd_5107707 < baseStart_5107707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107741 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_5107741 : Nat := 118140960795 + 5107741 * 2 ^ 59
def prefixEnd_5107741 : Nat := 4983230072969 + 3 ^ 40 * 5107741 * 2
def baseEnd_5107741 : Nat := 2622726191676605673547433

theorem tailTrace_5107741 : CollatzResearch.WordTrace tailWord_5107741 prefixEnd_5107741 2622726191676605673547433 := by
  unfold tailWord_5107741
  simp only [CollatzResearch.WordTrace]
  refine ⟨186294618988534164557955077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124196412659022776371970051 186294618988534164557955077)
  ·
    refine ⟨34930241060350155854616577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186294618988534164557955077 34930241060350155854616577)
    ·
      refine ⟨26197680795262616890962433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34930241060350155854616577 26197680795262616890962433)
      ·
        refine ⟨19648260596446962668221825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26197680795262616890962433 19648260596446962668221825)
        ·
          refine ⟨14736195447335222001166369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19648260596446962668221825 14736195447335222001166369)
          ·
            refine ⟨11052146585501416500874777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14736195447335222001166369 11052146585501416500874777)
            ·
              refine ⟨8289109939126062375656083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11052146585501416500874777 8289109939126062375656083)
              ·
                refine ⟨12433664908689093563484125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8289109939126062375656083 12433664908689093563484125)
                ·
                  refine ⟨4662624340758410086306547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12433664908689093563484125 4662624340758410086306547)
                  ·
                    refine ⟨6993936511137615129459821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4662624340758410086306547 6993936511137615129459821)
                    ·
                      refine ⟨2622726191676605673547433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6993936511137615129459821 2622726191676605673547433)
                      ·
                        rfl

theorem cell23_5107741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_5107741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107741 prefixEnd_5107741 := by exact prefixLift 5107741
  have htrace : WordTrace (prefixWord ++ tailWord_5107741) baseStart_5107741 baseEnd_5107741 := by
    simpa [prefixWord, tailWord_5107741, baseEnd_5107741] using wordTrace_append hprefix tailTrace_5107741
  have hstable : (prefixWord ++ tailWord_5107741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107741).length < 2 ^ (prefixWord ++ tailWord_5107741).sum := by decide
  have hdescent : baseEnd_5107741 < baseStart_5107741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107767 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 3]
def baseStart_5107767 : Nat := 118140960795 + 5107767 * 2 ^ 59
def prefixEnd_5107767 : Nat := 4983230072969 + 3 ^ 40 * 5107767 * 2
def baseEnd_5107767 : Nat := 2622739542173622571822313

theorem tailTrace_5107767 : CollatzResearch.WordTrace tailWord_5107767 prefixEnd_5107767 2622739542173622571822313 := by
  unfold tailWord_5107767
  simp only [CollatzResearch.WordTrace]
  refine ⟨186295567286439970998401555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124197044857626647332267703 186295567286439970998401555)
  ·
    refine ⟨279443350929659956497602333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186295567286439970998401555 279443350929659956497602333)
    ·
      refine ⟨104791256598622483686600875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279443350929659956497602333 104791256598622483686600875)
      ·
        refine ⟨157186884897933725529901313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104791256598622483686600875 157186884897933725529901313)
        ·
          refine ⟨117890163673450294147425985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157186884897933725529901313 117890163673450294147425985)
          ·
            refine ⟨88417622755087720610569489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117890163673450294147425985 88417622755087720610569489)
            ·
              refine ⟨66313217066315790457927117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88417622755087720610569489 66313217066315790457927117)
              ·
                refine ⟨24867456399868421421722669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66313217066315790457927117 24867456399868421421722669)
                ·
                  refine ⟨9325296149950658033146001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24867456399868421421722669 9325296149950658033146001)
                  ·
                    refine ⟨6993972112462993524859501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9325296149950658033146001 6993972112462993524859501)
                    ·
                      refine ⟨2622739542173622571822313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6993972112462993524859501 2622739542173622571822313)
                      ·
                        rfl

theorem cell23_5107767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_5107767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107767 prefixEnd_5107767 := by exact prefixLift 5107767
  have htrace : WordTrace (prefixWord ++ tailWord_5107767) baseStart_5107767 baseEnd_5107767 := by
    simpa [prefixWord, tailWord_5107767, baseEnd_5107767] using wordTrace_append hprefix tailTrace_5107767
  have hstable : (prefixWord ++ tailWord_5107767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107767).length < 2 ^ (prefixWord ++ tailWord_5107767).sum := by decide
  have hdescent : baseEnd_5107767 < baseStart_5107767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107818 : List Nat := [3, 1, 3, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_5107818 : Nat := 118140960795 + 5107818 * 2 ^ 59
def prefixEnd_5107818 : Nat := 4983230072969 + 3 ^ 40 * 5107818 * 2
def baseEnd_5107818 : Nat := 2622765729687001872284579

theorem tailTrace_5107818 : CollatzResearch.WordTrace tailWord_5107818 prefixEnd_5107818 2622765729687001872284579 := by
  unfold tailWord_5107818
  simp only [CollatzResearch.WordTrace]
  refine ⟨46574356852313801677127027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124198284939503471139005405 46574356852313801677127027)
  ·
    refine ⟨69861535278470702515690541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46574356852313801677127027 69861535278470702515690541)
    ·
      refine ⟨26198075729426513443383953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69861535278470702515690541 26198075729426513443383953)
      ·
        refine ⟨19648556797069885082537965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26198075729426513443383953 19648556797069885082537965)
        ·
          refine ⟨7368208798901206905951737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19648556797069885082537965 7368208798901206905951737)
          ·
            refine ⟨5526156599175905179463803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7368208798901206905951737 5526156599175905179463803)
            ·
              refine ⟨8289234898763857769195705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5526156599175905179463803 8289234898763857769195705)
              ·
                refine ⟨6216926174072893326896779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8289234898763857769195705 6216926174072893326896779)
                ·
                  refine ⟨9325389261109339990345169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6216926174072893326896779 9325389261109339990345169)
                  ·
                    refine ⟨6994041945832004992758877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9325389261109339990345169 6994041945832004992758877)
                    ·
                      refine ⟨2622765729687001872284579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6994041945832004992758877 2622765729687001872284579)
                      ·
                        rfl

theorem cell23_5107818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_5107818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107818 prefixEnd_5107818 := by exact prefixLift 5107818
  have htrace : WordTrace (prefixWord ++ tailWord_5107818) baseStart_5107818 baseEnd_5107818 := by
    simpa [prefixWord, tailWord_5107818, baseEnd_5107818] using wordTrace_append hprefix tailTrace_5107818
  have hstable : (prefixWord ++ tailWord_5107818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107818).length < 2 ^ (prefixWord ++ tailWord_5107818).sum := by decide
  have hdescent : baseEnd_5107818 < baseStart_5107818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107848 : List Nat := [2, 1, 3, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_5107848 : Nat := 118140960795 + 5107848 * 2 ^ 59
def prefixEnd_5107848 : Nat := 4983230072969 + 3 ^ 40 * 5107848 * 2
def baseEnd_5107848 : Nat := 2622781134106636754909441

theorem tailTrace_5107848 : CollatzResearch.WordTrace tailWord_5107848 prefixEnd_5107848 2622781134106636754909441 := by
  unfold tailWord_5107848
  simp only [CollatzResearch.WordTrace]
  refine ⟨93149260799573260916050099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124199014399431014554733465 93149260799573260916050099)
  ·
    refine ⟨139723891199359891374075149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93149260799573260916050099 139723891199359891374075149)
    ·
      refine ⟨52396459199759959265278181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139723891199359891374075149 52396459199759959265278181)
      ·
        refine ⟨9824336099954992362239659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52396459199759959265278181 9824336099954992362239659)
        ·
          refine ⟨14736504149932488543359489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9824336099954992362239659 14736504149932488543359489)
          ·
            refine ⟨11052378112449366407519617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14736504149932488543359489 11052378112449366407519617)
            ·
              refine ⟨8289283584337024805639713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11052378112449366407519617 8289283584337024805639713)
              ·
                refine ⟨6216962688252768604229785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8289283584337024805639713 6216962688252768604229785)
                ·
                  refine ⟨4662722016189576453172339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6216962688252768604229785 4662722016189576453172339)
                  ·
                    refine ⟨6994083024284364679758509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4662722016189576453172339 6994083024284364679758509)
                    ·
                      refine ⟨2622781134106636754909441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6994083024284364679758509 2622781134106636754909441)
                      ·
                        rfl

theorem cell23_5107848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_5107848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107848 prefixEnd_5107848 := by exact prefixLift 5107848
  have htrace : WordTrace (prefixWord ++ tailWord_5107848) baseStart_5107848 baseEnd_5107848 := by
    simpa [prefixWord, tailWord_5107848, baseEnd_5107848] using wordTrace_append hprefix tailTrace_5107848
  have hstable : (prefixWord ++ tailWord_5107848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107848).length < 2 ^ (prefixWord ++ tailWord_5107848).sum := by decide
  have hdescent : baseEnd_5107848 < baseStart_5107848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107862 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5107862 : Nat := 118140960795 + 5107862 * 2 ^ 59
def prefixEnd_5107862 : Nat := 4983230072969 + 3 ^ 40 * 5107862 * 2
def baseEnd_5107862 : Nat := 2622788322835799700134377

theorem tailTrace_5107862 : CollatzResearch.WordTrace tailWord_5107862 prefixEnd_5107862 2622788322835799700134377 := by
  unfold tailWord_5107862
  simp only [CollatzResearch.WordTrace]
  refine ⟨11643689513818487638944365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124199354814063868148739893 11643689513818487638944365)
  ·
    refine ⟨4366383567681932864604137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11643689513818487638944365 4366383567681932864604137)
    ·
      refine ⟨3274787675761449648453103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4366383567681932864604137 3274787675761449648453103)
      ·
        refine ⟨4912181513642174472679655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3274787675761449648453103 4912181513642174472679655)
        ·
          refine ⟨7368272270463261709019483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4912181513642174472679655 7368272270463261709019483)
          ·
            refine ⟨11052408405694892563529225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7368272270463261709019483 11052408405694892563529225)
            ·
              refine ⟨8289306304271169422646919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11052408405694892563529225 8289306304271169422646919)
              ·
                refine ⟨12433959456406754133970379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8289306304271169422646919 12433959456406754133970379)
                ·
                  refine ⟨18650939184610131200955569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12433959456406754133970379 18650939184610131200955569)
                  ·
                    refine ⟨13988204388457598400716677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18650939184610131200955569 13988204388457598400716677)
                    ·
                      refine ⟨2622788322835799700134377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13988204388457598400716677 2622788322835799700134377)
                      ·
                        rfl

theorem cell23_5107862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5107862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107862 prefixEnd_5107862 := by exact prefixLift 5107862
  have htrace : WordTrace (prefixWord ++ tailWord_5107862) baseStart_5107862 baseEnd_5107862 := by
    simpa [prefixWord, tailWord_5107862, baseEnd_5107862] using wordTrace_append hprefix tailTrace_5107862
  have hstable : (prefixWord ++ tailWord_5107862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107862).length < 2 ^ (prefixWord ++ tailWord_5107862).sum := by decide
  have hdescent : baseEnd_5107862 < baseStart_5107862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107864 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 2, 6]
def baseStart_5107864 : Nat := 118140960795 + 5107864 * 2 ^ 59
def prefixEnd_5107864 : Nat := 4983230072969 + 3 ^ 40 * 5107864 * 2
def baseEnd_5107864 : Nat := 874263116599036230769789

theorem tailTrace_5107864 : CollatzResearch.WordTrace tailWord_5107864 prefixEnd_5107864 874263116599036230769789 := by
  unfold tailWord_5107864
  simp only [CollatzResearch.WordTrace]
  refine ⟨93149552583544278282341323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124199403444725704376455097 93149552583544278282341323)
  ·
    refine ⟨139724328875316417423511985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93149552583544278282341323 139724328875316417423511985)
    ·
      refine ⟨104793246656487313067633989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139724328875316417423511985 104793246656487313067633989)
      ·
        refine ⟨19648733748091371200181373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104793246656487313067633989 19648733748091371200181373)
        ·
          refine ⟨7368275155534264200068015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19648733748091371200181373 7368275155534264200068015)
          ·
            refine ⟨11052412733301396300102023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7368275155534264200068015 11052412733301396300102023)
            ·
              refine ⟨16578619099952094450153035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11052412733301396300102023 16578619099952094450153035)
              ·
                refine ⟨24867928649928141675229553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16578619099952094450153035 24867928649928141675229553)
                ·
                  refine ⟨18650946487446106256422165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24867928649928141675229553 18650946487446106256422165)
                  ·
                    refine ⟨874263116599036230769789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18650946487446106256422165 874263116599036230769789)
                    ·
                      rfl

theorem cell23_5107864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_5107864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107864 prefixEnd_5107864 := by exact prefixLift 5107864
  have htrace : WordTrace (prefixWord ++ tailWord_5107864) baseStart_5107864 baseEnd_5107864 := by
    simpa [prefixWord, tailWord_5107864, baseEnd_5107864] using wordTrace_append hprefix tailTrace_5107864
  have hstable : (prefixWord ++ tailWord_5107864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107864).length < 2 ^ (prefixWord ++ tailWord_5107864).sum := by decide
  have hdescent : baseEnd_5107864 < baseStart_5107864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107871 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 1, 4, 2]
def baseStart_5107871 : Nat := 118140960795 + 5107871 * 2 ^ 59
def prefixEnd_5107871 : Nat := 4983230072969 + 3 ^ 40 * 5107871 * 2
def baseEnd_5107871 : Nat := 2622792944161690164921835

theorem tailTrace_5107871 : CollatzResearch.WordTrace tailWord_5107871 prefixEnd_5107871 2622792944161690164921835 := by
  unfold tailWord_5107871
  simp only [CollatzResearch.WordTrace]
  refine ⟨186299360478063196760187467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124199573652042131173458311 186299360478063196760187467)
  ·
    refine ⟨279449040717094795140281201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186299360478063196760187467 279449040717094795140281201)
    ·
      refine ⟨209586780537821096355210901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279449040717094795140281201 209586780537821096355210901)
      ·
        refine ⟨9824380337710363891650511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 209586780537821096355210901 9824380337710363891650511)
        ·
          refine ⟨14736570506565545837475767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9824380337710363891650511 14736570506565545837475767)
          ·
            refine ⟨22104855759848318756213651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14736570506565545837475767 22104855759848318756213651)
            ·
              refine ⟨33157283639772478134320477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22104855759848318756213651 33157283639772478134320477)
              ·
                refine ⟨12433981364914679300370179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33157283639772478134320477 12433981364914679300370179)
                ·
                  refine ⟨18650972047372018950555269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12433981364914679300370179 18650972047372018950555269)
                  ·
                    refine ⟨3497057258882253553229113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18650972047372018950555269 3497057258882253553229113)
                    ·
                      refine ⟨2622792944161690164921835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3497057258882253553229113 2622792944161690164921835)
                      ·
                        rfl

theorem cell23_5107871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_5107871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107871 prefixEnd_5107871 := by exact prefixLift 5107871
  have htrace : WordTrace (prefixWord ++ tailWord_5107871) baseStart_5107871 baseEnd_5107871 := by
    simpa [prefixWord, tailWord_5107871, baseEnd_5107871] using wordTrace_append hprefix tailTrace_5107871
  have hstable : (prefixWord ++ tailWord_5107871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107871).length < 2 ^ (prefixWord ++ tailWord_5107871).sum := by decide
  have hdescent : baseEnd_5107871 < baseStart_5107871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107877 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 7]
def baseStart_5107877 : Nat := 118140960795 + 5107877 * 2 ^ 59
def prefixEnd_5107877 : Nat := 4983230072969 + 3 ^ 40 * 5107877 * 2
def baseEnd_5107877 : Nat := 291421780560624126827423

theorem tailTrace_5107877 : CollatzResearch.WordTrace tailWord_5107877 prefixEnd_5107877 291421780560624126827423 := by
  unfold tailWord_5107877
  simp only [CollatzResearch.WordTrace]
  refine ⟨186299579316041459784905885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124199719544027639856603923 186299579316041459784905885)
  ·
    refine ⟨69862342243515547419339707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186299579316041459784905885 69862342243515547419339707)
    ·
      refine ⟨104793513365273321129009561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69862342243515547419339707 104793513365273321129009561)
      ·
        refine ⟨78595135023954990846757171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104793513365273321129009561 78595135023954990846757171)
        ·
          refine ⟨117892702535932486270135757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78595135023954990846757171 117892702535932486270135757)
          ·
            refine ⟨44209763450974682351300909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117892702535932486270135757 44209763450974682351300909)
            ·
              refine ⟨16578661294115505881737841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44209763450974682351300909 16578661294115505881737841)
              ·
                refine ⟨12433995970586629411303381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16578661294115505881737841 12433995970586629411303381)
                ·
                  refine ⟨291421780560624126827423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12433995970586629411303381 291421780560624126827423)
                  ·
                    rfl

theorem cell23_5107877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_5107877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107877 prefixEnd_5107877 := by exact prefixLift 5107877
  have htrace : WordTrace (prefixWord ++ tailWord_5107877) baseStart_5107877 baseEnd_5107877 := by
    simpa [prefixWord, tailWord_5107877, baseEnd_5107877] using wordTrace_append hprefix tailTrace_5107877
  have hstable : (prefixWord ++ tailWord_5107877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107877).length < 2 ^ (prefixWord ++ tailWord_5107877).sum := by decide
  have hdescent : baseEnd_5107877 < baseStart_5107877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107887 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 3]
def baseStart_5107887 : Nat := 118140960795 + 5107887 * 2 ^ 59
def prefixEnd_5107887 : Nat := 4983230072969 + 3 ^ 40 * 5107887 * 2
def baseEnd_5107887 : Nat := 2622801159852162102321761

theorem tailTrace_5107887 : CollatzResearch.WordTrace tailWord_5107887 prefixEnd_5107887 2622801159852162102321761 := by
  unfold tailWord_5107887
  simp only [CollatzResearch.WordTrace]
  refine ⟨186299944046005231492769915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124199962697336820995179943 186299944046005231492769915)
  ·
    refine ⟨279449916069007847239154873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186299944046005231492769915 279449916069007847239154873)
    ·
      refine ⟨209587437051755885429366155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279449916069007847239154873 209587437051755885429366155)
      ·
        refine ⟨314381155577633828144049233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209587437051755885429366155 314381155577633828144049233)
        ·
          refine ⟨235785866683225371108036925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314381155577633828144049233 235785866683225371108036925)
          ·
            refine ⟨88419700006209514165513847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235785866683225371108036925 88419700006209514165513847)
            ·
              refine ⟨132629550009314271248270771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88419700006209514165513847 132629550009314271248270771)
              ·
                refine ⟨198944325013971406872406157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132629550009314271248270771 198944325013971406872406157)
                ·
                  refine ⟨74604121880239277577152309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198944325013971406872406157 74604121880239277577152309)
                  ·
                    refine ⟨6994136426272432272858029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74604121880239277577152309 6994136426272432272858029)
                    ·
                      refine ⟨2622801159852162102321761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6994136426272432272858029 2622801159852162102321761)
                      ·
                        rfl

theorem cell23_5107887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 3].length) (baseStart_5107887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107887 prefixEnd_5107887 := by exact prefixLift 5107887
  have htrace : WordTrace (prefixWord ++ tailWord_5107887) baseStart_5107887 baseEnd_5107887 := by
    simpa [prefixWord, tailWord_5107887, baseEnd_5107887] using wordTrace_append hprefix tailTrace_5107887
  have hstable : (prefixWord ++ tailWord_5107887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107887).length < 2 ^ (prefixWord ++ tailWord_5107887).sum := by decide
  have hdescent : baseEnd_5107887 < baseStart_5107887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107904 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 3]
def baseStart_5107904 : Nat := 118140960795 + 5107904 * 2 ^ 59
def prefixEnd_5107904 : Nat := 4983230072969 + 3 ^ 40 * 5107904 * 2
def baseEnd_5107904 : Nat := 2622809889023288535809183

theorem tailTrace_5107904 : CollatzResearch.WordTrace tailWord_5107904 prefixEnd_5107904 2622809889023288535809183 := by
  unfold tailWord_5107904
  simp only [CollatzResearch.WordTrace]
  refine ⟨93150282043471821698069383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124200376057962428930759177 93150282043471821698069383)
  ·
    refine ⟨139725423065207732547104075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93150282043471821698069383 139725423065207732547104075)
    ·
      refine ⟨209588134597811598820656113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139725423065207732547104075 209588134597811598820656113)
      ·
        refine ⟨157191100948358699115492085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209588134597811598820656113 157191100948358699115492085)
        ·
          refine ⟨14736665713908628042077383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157191100948358699115492085 14736665713908628042077383)
          ·
            refine ⟨22104998570862942063116075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14736665713908628042077383 22104998570862942063116075)
            ·
              refine ⟨33157497856294413094674113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22104998570862942063116075 33157497856294413094674113)
              ·
                refine ⟨24868123392220809821005585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33157497856294413094674113 24868123392220809821005585)
                ·
                  refine ⟨18651092544165607365754189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24868123392220809821005585 18651092544165607365754189)
                  ·
                    refine ⟨6994159704062102762157821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18651092544165607365754189 6994159704062102762157821)
                    ·
                      refine ⟨2622809889023288535809183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6994159704062102762157821 2622809889023288535809183)
                      ·
                        rfl

theorem cell23_5107904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_5107904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107904 prefixEnd_5107904 := by exact prefixLift 5107904
  have htrace : WordTrace (prefixWord ++ tailWord_5107904) baseStart_5107904 baseEnd_5107904 := by
    simpa [prefixWord, tailWord_5107904, baseEnd_5107904] using wordTrace_append hprefix tailTrace_5107904
  have hstable : (prefixWord ++ tailWord_5107904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107904).length < 2 ^ (prefixWord ++ tailWord_5107904).sum := by decide
  have hdescent : baseEnd_5107904 < baseStart_5107904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107905 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_5107905 : Nat := 118140960795 + 5107905 * 2 ^ 59
def prefixEnd_5107905 : Nat := 4983230072969 + 3 ^ 40 * 5107905 * 2
def baseEnd_5107905 : Nat := 2622810402503943031896679

theorem tailTrace_5107905 : CollatzResearch.WordTrace tailWord_5107905 prefixEnd_5107905 2622810402503943031896679 := by
  unfold tailWord_5107905
  simp only [CollatzResearch.WordTrace]
  refine ⟨186300600559940020566925169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124200400373293347044616779 186300600559940020566925169)
  ·
    refine ⟨139725450419955015425193877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186300600559940020566925169 139725450419955015425193877)
    ·
      refine ⟨6549630488435391348055963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139725450419955015425193877 6549630488435391348055963)
      ·
        refine ⟨9824445732653087022083945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6549630488435391348055963 9824445732653087022083945)
        ·
          refine ⟨7368334299489815266562959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9824445732653087022083945 7368334299489815266562959)
          ·
            refine ⟨11052501449234722899844439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7368334299489815266562959 11052501449234722899844439)
            ·
              refine ⟨16578752173852084349766659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11052501449234722899844439 16578752173852084349766659)
              ·
                refine ⟨24868128260778126524649989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16578752173852084349766659 24868128260778126524649989)
                ·
                  refine ⟨4662774048895898723371873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24868128260778126524649989 4662774048895898723371873)
                  ·
                    refine ⟨3497080536671924042528905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4662774048895898723371873 3497080536671924042528905)
                    ·
                      refine ⟨2622810402503943031896679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3497080536671924042528905 2622810402503943031896679)
                      ·
                        rfl

theorem cell23_5107905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_5107905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107905 prefixEnd_5107905 := by exact prefixLift 5107905
  have htrace : WordTrace (prefixWord ++ tailWord_5107905) baseStart_5107905 baseEnd_5107905 := by
    simpa [prefixWord, tailWord_5107905, baseEnd_5107905] using wordTrace_append hprefix tailTrace_5107905
  have hstable : (prefixWord ++ tailWord_5107905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107905).length < 2 ^ (prefixWord ++ tailWord_5107905).sum := by decide
  have hdescent : baseEnd_5107905 < baseStart_5107905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107937 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 2, 8]
def baseStart_5107937 : Nat := 118140960795 + 5107937 * 2 ^ 59
def prefixEnd_5107937 : Nat := 4983230072969 + 3 ^ 40 * 5107937 * 2
def baseEnd_5107937 : Nat := 874275611294962302232177

theorem tailTrace_5107937 : CollatzResearch.WordTrace tailWord_5107937 prefixEnd_5107937 874275611294962302232177 := by
  unfold tailWord_5107937
  simp only [CollatzResearch.WordTrace]
  refine ⟨186301767695824090032090065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124201178463882726688060043 186301767695824090032090065)
  ·
    refine ⟨139726325771868067524067549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186301767695824090032090065 139726325771868067524067549)
    ·
      refine ⟨52397372164450525321525331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139726325771868067524067549 52397372164450525321525331)
      ·
        refine ⟨78596058246675787982287997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52397372164450525321525331 78596058246675787982287997)
        ·
          refine ⟨29473521842503420493357999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78596058246675787982287997 29473521842503420493357999)
          ·
            refine ⟨44210282763755130740036999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29473521842503420493357999 44210282763755130740036999)
            ·
              refine ⟨66315424145632696110055499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44210282763755130740036999 66315424145632696110055499)
              ·
                refine ⟨99473136218449044165083249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66315424145632696110055499 99473136218449044165083249)
                ·
                  refine ⟨74604852163836783123812437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99473136218449044165083249 74604852163836783123812437)
                  ·
                    refine ⟨874275611294962302232177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74604852163836783123812437 874275611294962302232177)
                    ·
                      rfl

theorem cell23_5107937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_5107937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107937 prefixEnd_5107937 := by exact prefixLift 5107937
  have htrace : WordTrace (prefixWord ++ tailWord_5107937) baseStart_5107937 baseEnd_5107937 := by
    simpa [prefixWord, tailWord_5107937, baseEnd_5107937] using wordTrace_append hprefix tailTrace_5107937
  have hstable : (prefixWord ++ tailWord_5107937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107937).length < 2 ^ (prefixWord ++ tailWord_5107937).sum := by decide
  have hdescent : baseEnd_5107937 < baseStart_5107937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107944 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_5107944 : Nat := 118140960795 + 5107944 * 2 ^ 59
def prefixEnd_5107944 : Nat := 4983230072969 + 3 ^ 40 * 5107944 * 2
def baseEnd_5107944 : Nat := 2622830428249468379308999

theorem tailTrace_5107944 : CollatzResearch.WordTrace tailWord_5107944 prefixEnd_5107944 2622830428249468379308999 := by
  unfold tailWord_5107944
  simp only [CollatzResearch.WordTrace]
  refine ⟨93151011503399365113797443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124201348671199153485063257 93151011503399365113797443)
  ·
    refine ⟨139726517255099047670696165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93151011503399365113797443 139726517255099047670696165)
    ·
      refine ⟨26198721985331071438255531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139726517255099047670696165 26198721985331071438255531)
      ·
        refine ⟨39298082977996607157383297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26198721985331071438255531 39298082977996607157383297)
        ·
          refine ⟨29473562233497455368037473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39298082977996607157383297 29473562233497455368037473)
          ·
            refine ⟨22105171675123091526028105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29473562233497455368037473 22105171675123091526028105)
            ·
              refine ⟨16578878756342318644521079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22105171675123091526028105 16578878756342318644521079)
              ·
                refine ⟨24868318134513477966781619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16578878756342318644521079 24868318134513477966781619)
                ·
                  refine ⟨37302477201770216950172429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24868318134513477966781619 37302477201770216950172429)
                  ·
                    refine ⟨13988428950663831356314661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37302477201770216950172429 13988428950663831356314661)
                    ·
                      refine ⟨2622830428249468379308999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13988428950663831356314661 2622830428249468379308999)
                      ·
                        rfl

theorem cell23_5107944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_5107944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107944 prefixEnd_5107944 := by exact prefixLift 5107944
  have htrace : WordTrace (prefixWord ++ tailWord_5107944) baseStart_5107944 baseEnd_5107944 := by
    simpa [prefixWord, tailWord_5107944, baseEnd_5107944] using wordTrace_append hprefix tailTrace_5107944
  have hstable : (prefixWord ++ tailWord_5107944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107944).length < 2 ^ (prefixWord ++ tailWord_5107944).sum := by decide
  have hdescent : baseEnd_5107944 < baseStart_5107944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107967 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 8]
def baseStart_5107967 : Nat := 118140960795 + 5107967 * 2 ^ 59
def prefixEnd_5107967 : Nat := 4983230072969 + 3 ^ 40 * 5107967 * 2
def baseEnd_5107967 : Nat := 291426915367169087702377

theorem tailTrace_5107967 : CollatzResearch.WordTrace tailWord_5107967 prefixEnd_5107967 291426915367169087702377 := by
  unfold tailWord_5107967
  simp only [CollatzResearch.WordTrace]
  refine ⟨186302861885715405155682155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124201907923810270103788103 186302861885715405155682155)
  ·
    refine ⟨279454292828573107733523233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186302861885715405155682155 279454292828573107733523233)
    ·
      refine ⟨209590719621429830800142425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279454292828573107733523233 209590719621429830800142425)
      ·
        refine ⟨157193039716072373100106819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209590719621429830800142425 157193039716072373100106819)
        ·
          refine ⟨235789559574108559650160229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157193039716072373100106819 235789559574108559650160229)
          ·
            refine ⟨44210542420145354934405043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235789559574108559650160229 44210542420145354934405043)
            ·
              refine ⟨66315813630218032401607565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44210542420145354934405043 66315813630218032401607565)
              ·
                refine ⟨24868430111331762150602837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66315813630218032401607565 24868430111331762150602837)
                ·
                  refine ⟨291426915367169087702377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24868430111331762150602837 291426915367169087702377)
                  ·
                    rfl

theorem cell23_5107967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 8].length) (baseStart_5107967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107967 prefixEnd_5107967 := by exact prefixLift 5107967
  have htrace : WordTrace (prefixWord ++ tailWord_5107967) baseStart_5107967 baseEnd_5107967 := by
    simpa [prefixWord, tailWord_5107967, baseEnd_5107967] using wordTrace_append hprefix tailTrace_5107967
  have hstable : (prefixWord ++ tailWord_5107967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107967).length < 2 ^ (prefixWord ++ tailWord_5107967).sum := by decide
  have hdescent : baseEnd_5107967 < baseStart_5107967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5107987 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 6]
def baseStart_5107987 : Nat := 118140960795 + 5107987 * 2 ^ 59
def prefixEnd_5107987 : Nat := 4983230072969 + 3 ^ 40 * 5107987 * 2
def baseEnd_5107987 : Nat := 2622852507917611711071301

theorem tailTrace_5107987 : CollatzResearch.WordTrace tailWord_5107987 prefixEnd_5107987 2622852507917611711071301 := by
  unfold tailWord_5107987
  simp only [CollatzResearch.WordTrace]
  refine ⟨186303591345642948571410215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124202394230428632380940143 186303591345642948571410215)
  ·
    refine ⟨279455387018464422857115323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186303591345642948571410215 279455387018464422857115323)
    ·
      refine ⟨419183080527696634285672985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279455387018464422857115323 419183080527696634285672985)
      ·
        refine ⟨314387310395772475714254739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419183080527696634285672985 314387310395772475714254739)
        ·
          refine ⟨471580965593658713571382109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314387310395772475714254739 471580965593658713571382109)
          ·
            refine ⟨176842862097622017589268291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 471580965593658713571382109 176842862097622017589268291)
            ·
              refine ⟨265264293146433026383902437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176842862097622017589268291 265264293146433026383902437)
              ·
                refine ⟨49737054964956192446981707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 265264293146433026383902437 49737054964956192446981707)
                ·
                  refine ⟨74605582447434288670472561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49737054964956192446981707 74605582447434288670472561)
                  ·
                    refine ⟨55954186835575716502854421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74605582447434288670472561 55954186835575716502854421)
                    ·
                      refine ⟨2622852507917611711071301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55954186835575716502854421 2622852507917611711071301)
                      ·
                        rfl

theorem cell23_5107987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_5107987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5107987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5107987 prefixEnd_5107987 := by exact prefixLift 5107987
  have htrace : WordTrace (prefixWord ++ tailWord_5107987) baseStart_5107987 baseEnd_5107987 := by
    simpa [prefixWord, tailWord_5107987, baseEnd_5107987] using wordTrace_append hprefix tailTrace_5107987
  have hstable : (prefixWord ++ tailWord_5107987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5107987).length < 2 ^ (prefixWord ++ tailWord_5107987).sum := by decide
  have hdescent : baseEnd_5107987 < baseStart_5107987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5107987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108068 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 5, 2, 2]
def baseStart_5108068 : Nat := 118140960795 + 5108068 * 2 ^ 59
def prefixEnd_5108068 : Nat := 4983230072969 + 3 ^ 40 * 5108068 * 2
def baseEnd_5108068 : Nat := 2622894099850625894158429

theorem tailTrace_5108068 : CollatzResearch.WordTrace tailWord_5108068 prefixEnd_5108068 2622894099850625894158429 := by
  unfold tailWord_5108068
  simp only [CollatzResearch.WordTrace]
  refine ⟨93153272829174749702554429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124204363772232999603405905 93153272829174749702554429)
  ·
    refine ⟨34932477310940531138457911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93153272829174749702554429 34932477310940531138457911)
    ·
      refine ⟨52398715966410796707686867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34932477310940531138457911 52398715966410796707686867)
      ·
        refine ⟨78598073949616195061530301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52398715966410796707686867 78598073949616195061530301)
        ·
          refine ⟨29474277731106073148073863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78598073949616195061530301 29474277731106073148073863)
          ·
            refine ⟨44211416596659109722110795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29474277731106073148073863 44211416596659109722110795)
            ·
              refine ⟨66317124894988664583166193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44211416596659109722110795 66317124894988664583166193)
              ·
                refine ⟨49737843671241498437374645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66317124894988664583166193 49737843671241498437374645)
                ·
                  refine ⟨4662922844178890478503873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49737843671241498437374645 4662922844178890478503873)
                  ·
                    refine ⟨3497192133134167858877905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4662922844178890478503873 3497192133134167858877905)
                    ·
                      refine ⟨2622894099850625894158429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3497192133134167858877905 2622894099850625894158429)
                      ·
                        rfl

theorem cell23_5108068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_5108068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108068 prefixEnd_5108068 := by exact prefixLift 5108068
  have htrace : WordTrace (prefixWord ++ tailWord_5108068) baseStart_5108068 baseEnd_5108068 := by
    simpa [prefixWord, tailWord_5108068, baseEnd_5108068] using wordTrace_append hprefix tailTrace_5108068
  have hstable : (prefixWord ++ tailWord_5108068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108068).length < 2 ^ (prefixWord ++ tailWord_5108068).sum := by decide
  have hdescent : baseEnd_5108068 < baseStart_5108068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108085 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_5108085 : Nat := 118140960795 + 5108085 * 2 ^ 59
def prefixEnd_5108085 : Nat := 4983230072969 + 3 ^ 40 * 5108085 * 2
def baseEnd_5108085 : Nat := 2622902829021752327645851

theorem tailTrace_5108085 : CollatzResearch.WordTrace tailWord_5108085 prefixEnd_5108085 2622902829021752327645851 := by
  unfold tailWord_5108085
  simp only [CollatzResearch.WordTrace]
  refine ⟨186307165699287911308477709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124204777132858607538985139 186307165699287911308477709)
  ·
    refine ⟨69865187137232966740679141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186307165699287911308477709 69865187137232966740679141)
    ·
      refine ⟨13099722588231181263877339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69865187137232966740679141 13099722588231181263877339)
      ·
        refine ⟨19649583882346771895816009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13099722588231181263877339 19649583882346771895816009)
        ·
          refine ⟨14737187911760078921862007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19649583882346771895816009 14737187911760078921862007)
          ·
            refine ⟨22105781867640118382793011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14737187911760078921862007 22105781867640118382793011)
            ·
              refine ⟨33158672801460177574189517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22105781867640118382793011 33158672801460177574189517)
              ·
                refine ⟨12434502300547566590321069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33158672801460177574189517 12434502300547566590321069)
                ·
                  refine ⟨4662938362705337471370401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12434502300547566590321069 4662938362705337471370401)
                  ·
                    refine ⟨3497203772029003103527801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4662938362705337471370401 3497203772029003103527801)
                    ·
                      refine ⟨2622902829021752327645851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3497203772029003103527801 2622902829021752327645851)
                      ·
                        rfl

theorem cell23_5108085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_5108085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108085 prefixEnd_5108085 := by exact prefixLift 5108085
  have htrace : WordTrace (prefixWord ++ tailWord_5108085) baseStart_5108085 baseEnd_5108085 := by
    simpa [prefixWord, tailWord_5108085, baseEnd_5108085] using wordTrace_append hprefix tailTrace_5108085
  have hstable : (prefixWord ++ tailWord_5108085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108085).length < 2 ^ (prefixWord ++ tailWord_5108085).sum := by decide
  have hdescent : baseEnd_5108085 < baseStart_5108085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108136 : List Nat := [2, 1, 6, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_5108136 : Nat := 118140960795 + 5108136 * 2 ^ 59
def prefixEnd_5108136 : Nat := 4983230072969 + 3 ^ 40 * 5108136 * 2
def baseEnd_5108136 : Nat := 2622929016535131628108117

theorem tailTrace_5108136 : CollatzResearch.WordTrace tailWord_5108136 prefixEnd_5108136 2622929016535131628108117 := by
  unfold tailWord_5108136
  simp only [CollatzResearch.WordTrace]
  refine ⟨93154512911051573509292131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124206017214735431345722841 93154512911051573509292131)
  ·
    refine ⟨139731769366577360263938197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93154512911051573509292131 139731769366577360263938197)
    ·
      refine ⟨6549926689058313762372103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139731769366577360263938197 6549926689058313762372103)
      ·
        refine ⟨9824890033587470643558155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6549926689058313762372103 9824890033587470643558155)
        ·
          refine ⟨14737335050381205965337233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9824890033587470643558155 14737335050381205965337233)
          ·
            refine ⟨11053001287785904474002925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14737335050381205965337233 11053001287785904474002925)
            ·
              refine ⟨4144875482919714177751097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11053001287785904474002925 4144875482919714177751097)
              ·
                refine ⟨3108656612189785633313323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4144875482919714177751097 3108656612189785633313323)
                ·
                  refine ⟨4662984918284678449969985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108656612189785633313323 4662984918284678449969985)
                  ·
                    refine ⟨3497238688713508837477489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4662984918284678449969985 3497238688713508837477489)
                    ·
                      refine ⟨2622929016535131628108117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3497238688713508837477489 2622929016535131628108117)
                      ·
                        rfl

theorem cell23_5108136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_5108136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108136 prefixEnd_5108136 := by exact prefixLift 5108136
  have htrace : WordTrace (prefixWord ++ tailWord_5108136) baseStart_5108136 baseEnd_5108136 := by
    simpa [prefixWord, tailWord_5108136, baseEnd_5108136] using wordTrace_append hprefix tailTrace_5108136
  have hstable : (prefixWord ++ tailWord_5108136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108136).length < 2 ^ (prefixWord ++ tailWord_5108136).sum := by decide
  have hdescent : baseEnd_5108136 < baseStart_5108136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108154 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_5108154 : Nat := 118140960795 + 5108154 * 2 ^ 59
def prefixEnd_5108154 : Nat := 4983230072969 + 3 ^ 40 * 5108154 * 2
def baseEnd_5108154 : Nat := 2622938259186912557683033

theorem tailTrace_5108154 : CollatzResearch.WordTrace tailWord_5108154 prefixEnd_5108154 2622938259186912557683033 := by
  unfold tailWord_5108154
  simp only [CollatzResearch.WordTrace]
  refine ⟨46577420584009484023184879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124206454890691957395159677 46577420584009484023184879)
  ·
    refine ⟨69866130876014226034777319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46577420584009484023184879 69866130876014226034777319)
    ·
      refine ⟨104799196314021339052165979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69866130876014226034777319 104799196314021339052165979)
      ·
        refine ⟨157198794471032008578248969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104799196314021339052165979 157198794471032008578248969)
        ·
          refine ⟨117899095853274006433686727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157198794471032008578248969 117899095853274006433686727)
          ·
            refine ⟨176848643779911009650530091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117899095853274006433686727 176848643779911009650530091)
            ·
              refine ⟨265272965669866514475795137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176848643779911009650530091 265272965669866514475795137)
              ·
                refine ⟨198954724252399885856846353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265272965669866514475795137 198954724252399885856846353)
                ·
                  refine ⟨149216043189299914392634765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198954724252399885856846353 149216043189299914392634765)
                  ·
                    refine ⟨55956016195987467897238037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149216043189299914392634765 55956016195987467897238037)
                    ·
                      refine ⟨2622938259186912557683033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55956016195987467897238037 2622938259186912557683033)
                      ·
                        rfl

theorem cell23_5108154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_5108154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108154 prefixEnd_5108154 := by exact prefixLift 5108154
  have htrace : WordTrace (prefixWord ++ tailWord_5108154) baseStart_5108154 baseEnd_5108154 := by
    simpa [prefixWord, tailWord_5108154, baseEnd_5108154] using wordTrace_append hprefix tailTrace_5108154
  have hstable : (prefixWord ++ tailWord_5108154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108154).length < 2 ^ (prefixWord ++ tailWord_5108154).sum := by decide
  have hdescent : baseEnd_5108154 < baseStart_5108154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108228 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_5108228 : Nat := 118140960795 + 5108228 * 2 ^ 59
def prefixEnd_5108228 : Nat := 4983230072969 + 3 ^ 40 * 5108228 * 2
def baseEnd_5108228 : Nat := 874325418918448422719231

theorem tailTrace_5108228 : CollatzResearch.WordTrace tailWord_5108228 prefixEnd_5108228 874325418918448422719231 := by
  unfold tailWord_5108228
  simp only [CollatzResearch.WordTrace]
  refine ⟨93156190668884923365466669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124208254225179897820622225 93156190668884923365466669)
  ·
    refine ⟨34933571500831846262050001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93156190668884923365466669 34933571500831846262050001)
    ·
      refine ⟨26200178625623884696537501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34933571500831846262050001 26200178625623884696537501)
      ·
        refine ⟨9825066984608956761201563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26200178625623884696537501 9825066984608956761201563)
        ·
          refine ⟨14737600476913435141802345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9825066984608956761201563 14737600476913435141802345)
          ·
            refine ⟨11053200357685076356351759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14737600476913435141802345 11053200357685076356351759)
            ·
              refine ⟨16579800536527614534527639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11053200357685076356351759 16579800536527614534527639)
              ·
                refine ⟨24869700804791421801791459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16579800536527614534527639 24869700804791421801791459)
                ·
                  refine ⟨37304551207187132702687189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24869700804791421801791459 37304551207187132702687189)
                  ·
                    refine ⟨874325418918448422719231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37304551207187132702687189 874325418918448422719231)
                    ·
                      rfl

theorem cell23_5108228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_5108228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108228 prefixEnd_5108228 := by exact prefixLift 5108228
  have htrace : WordTrace (prefixWord ++ tailWord_5108228) baseStart_5108228 baseEnd_5108228 := by
    simpa [prefixWord, tailWord_5108228, baseEnd_5108228] using wordTrace_append hprefix tailTrace_5108228
  have hstable : (prefixWord ++ tailWord_5108228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108228).length < 2 ^ (prefixWord ++ tailWord_5108228).sum := by decide
  have hdescent : baseEnd_5108228 < baseStart_5108228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108322 : List Nat := [3, 3, 2, 3, 1, 1, 1, 3, 6]
def baseStart_5108322 : Nat := 118140960795 + 5108322 * 2 ^ 59
def prefixEnd_5108322 : Nat := 4983230072969 + 3 ^ 40 * 5108322 * 2
def baseEnd_5108322 : Nat := 291447169326318655598029

theorem tailTrace_5108322 : CollatzResearch.WordTrace tailWord_5108322 prefixEnd_5108322 291447169326318655598029 := by
  unfold tailWord_5108322
  simp only [CollatzResearch.WordTrace]
  refine ⟨46578952449857325196213805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124210539866286200523236813 46578952449857325196213805)
  ·
    refine ⟨17467107168696496948580177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46578952449857325196213805 17467107168696496948580177)
    ·
      refine ⟨13100330376522372711435133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17467107168696496948580177 13100330376522372711435133)
      ·
        refine ⟨4912623891195889766788175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13100330376522372711435133 4912623891195889766788175)
        ·
          refine ⟨7368935836793834650182263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4912623891195889766788175 7368935836793834650182263)
          ·
            refine ⟨11053403755190751975273395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7368935836793834650182263 11053403755190751975273395)
            ·
              refine ⟨16580105632786127962910093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11053403755190751975273395 16580105632786127962910093)
              ·
                refine ⟨6217539612294797986091285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16580105632786127962910093 6217539612294797986091285)
                ·
                  refine ⟨291447169326318655598029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6217539612294797986091285 291447169326318655598029)
                  ·
                    rfl

theorem cell23_5108322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_5108322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108322 prefixEnd_5108322 := by exact prefixLift 5108322
  have htrace : WordTrace (prefixWord ++ tailWord_5108322) baseStart_5108322 baseEnd_5108322 := by
    simpa [prefixWord, tailWord_5108322, baseEnd_5108322] using wordTrace_append hprefix tailTrace_5108322
  have hstable : (prefixWord ++ tailWord_5108322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108322).length < 2 ^ (prefixWord ++ tailWord_5108322).sum := by decide
  have hdescent : baseEnd_5108322 < baseStart_5108322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108348 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 6, 4]
def baseStart_5108348 : Nat := 118140960795 + 5108348 * 2 ^ 59
def prefixEnd_5108348 : Nat := 4983230072969 + 3 ^ 40 * 5108348 * 2
def baseEnd_5108348 : Nat := 874345958144628266219047

theorem tailTrace_5108348 : CollatzResearch.WordTrace tailWord_5108348 prefixEnd_5108348 874345958144628266219047 := by
  unfold tailWord_5108348
  simp only [CollatzResearch.WordTrace]
  refine ⟨93158379048667553612650849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124211172064890071483534465 93158379048667553612650849)
  ·
    refine ⟨69868784286500665209488137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93158379048667553612650849 69868784286500665209488137)
    ·
      refine ⟨52401588214875498907116103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69868784286500665209488137 52401588214875498907116103)
      ·
        refine ⟨78602382322313248360674155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52401588214875498907116103 78602382322313248360674155)
        ·
          refine ⟨117903573483469872541011233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78602382322313248360674155 117903573483469872541011233)
          ·
            refine ⟨88427680112602404405758425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117903573483469872541011233 88427680112602404405758425)
            ·
              refine ⟨66320760084451803304318819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88427680112602404405758425 66320760084451803304318819)
              ·
                refine ⟨99481140126677704956478229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66320760084451803304318819 99481140126677704956478229)
                ·
                  refine ⟨4663178443438017419834917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99481140126677704956478229 4663178443438017419834917)
                  ·
                    refine ⟨874345958144628266219047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4663178443438017419834917 874345958144628266219047)
                    ·
                      rfl

theorem cell23_5108348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_5108348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108348 prefixEnd_5108348 := by exact prefixLift 5108348
  have htrace : WordTrace (prefixWord ++ tailWord_5108348) baseStart_5108348 baseEnd_5108348 := by
    simpa [prefixWord, tailWord_5108348, baseEnd_5108348] using wordTrace_append hprefix tailTrace_5108348
  have hstable : (prefixWord ++ tailWord_5108348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108348).length < 2 ^ (prefixWord ++ tailWord_5108348).sum := by decide
  have hdescent : baseEnd_5108348 < baseStart_5108348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108351 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 6]
def baseStart_5108351 : Nat := 118140960795 + 5108351 * 2 ^ 59
def prefixEnd_5108351 : Nat := 4983230072969 + 3 ^ 40 * 5108351 * 2
def baseEnd_5108351 : Nat := 2623039414875848286919627

theorem tailTrace_5108351 : CollatzResearch.WordTrace tailWord_5108351 prefixEnd_5108351 2623039414875848286919627 := by
  unfold tailWord_5108351
  simp only [CollatzResearch.WordTrace]
  refine ⟨186316867516324238737660907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124211245010882825825107271 186316867516324238737660907)
  ·
    refine ⟨279475301274486358106491361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186316867516324238737660907 279475301274486358106491361)
    ·
      refine ⟨209606475955864768579868521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279475301274486358106491361 209606475955864768579868521)
      ·
        refine ⟨157204856966898576434901391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209606475955864768579868521 157204856966898576434901391)
        ·
          refine ⟨235807285450347864652352087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157204856966898576434901391 235807285450347864652352087)
          ·
            refine ⟨353710928175521796978528131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235807285450347864652352087 353710928175521796978528131)
            ·
              refine ⟨530566392263282695467792197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353710928175521796978528131 530566392263282695467792197)
              ·
                refine ⟨99481198549365505400211037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530566392263282695467792197 99481198549365505400211037)
                ·
                  refine ⟨37305449456012064525079139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99481198549365505400211037 37305449456012064525079139)
                  ·
                    refine ⟨55958174184018096787618709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37305449456012064525079139 55958174184018096787618709)
                    ·
                      refine ⟨2623039414875848286919627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55958174184018096787618709 2623039414875848286919627)
                      ·
                        rfl

theorem cell23_5108351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_5108351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108351 prefixEnd_5108351 := by exact prefixLift 5108351
  have htrace : WordTrace (prefixWord ++ tailWord_5108351) baseStart_5108351 baseEnd_5108351 := by
    simpa [prefixWord, tailWord_5108351, baseEnd_5108351] using wordTrace_append hprefix tailTrace_5108351
  have hstable : (prefixWord ++ tailWord_5108351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108351).length < 2 ^ (prefixWord ++ tailWord_5108351).sum := by decide
  have hdescent : baseEnd_5108351 < baseStart_5108351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108382 : List Nat := [4, 3, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_5108382 : Nat := 118140960795 + 5108382 * 2 ^ 59
def prefixEnd_5108382 : Nat := 4983230072969 + 3 ^ 40 * 5108382 * 2
def baseEnd_5108382 : Nat := 874351777592045888543995

theorem tailTrace_5108382 : CollatzResearch.WordTrace tailWord_5108382 prefixEnd_5108382 874351777592045888543995 := by
  unfold tailWord_5108382
  simp only [CollatzResearch.WordTrace]
  refine ⟨23289749772401491379004925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124211998786141287354692933 23289749772401491379004925)
  ·
    refine ⟨8733656164650559267126847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23289749772401491379004925 8733656164650559267126847)
    ·
      refine ⟨13100484246975838900690271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8733656164650559267126847 13100484246975838900690271)
      ·
        refine ⟨19650726370463758351035407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13100484246975838900690271 19650726370463758351035407)
        ·
          refine ⟨29476089555695637526553111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19650726370463758351035407 29476089555695637526553111)
          ·
            refine ⟨44214134333543456289829667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29476089555695637526553111 44214134333543456289829667)
            ·
              refine ⟨66321201500315184434744501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44214134333543456289829667 66321201500315184434744501)
              ·
                refine ⟨6217612640654548540757297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66321201500315184434744501 6217612640654548540757297)
                ·
                  refine ⟨4663209480490911405567973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6217612640654548540757297 4663209480490911405567973)
                  ·
                    refine ⟨874351777592045888543995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4663209480490911405567973 874351777592045888543995)
                    ·
                      rfl

theorem cell23_5108382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_5108382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108382 prefixEnd_5108382 := by exact prefixLift 5108382
  have htrace : WordTrace (prefixWord ++ tailWord_5108382) baseStart_5108382 baseEnd_5108382 := by
    simpa [prefixWord, tailWord_5108382, baseEnd_5108382] using wordTrace_append hprefix tailTrace_5108382
  have hstable : (prefixWord ++ tailWord_5108382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108382).length < 2 ^ (prefixWord ++ tailWord_5108382).sum := by decide
  have hdescent : baseEnd_5108382 < baseStart_5108382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108439 : List Nat := [1, 1, 3, 2, 1, 5, 3, 1, 2, 1, 3]
def baseStart_5108439 : Nat := 118140960795 + 5108439 * 2 ^ 59
def prefixEnd_5108439 : Nat := 4983230072969 + 3 ^ 40 * 5108439 * 2
def baseEnd_5108439 : Nat := 2623084601173443942619223

theorem tailTrace_5108439 : CollatzResearch.WordTrace tailWord_5108439 prefixEnd_5108439 2623084601173443942619223 := by
  unfold tailWord_5108439
  simp only [CollatzResearch.WordTrace]
  refine ⟨186320077140005429766864371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124213384760003619844576247 186320077140005429766864371)
  ·
    refine ⟨279480115710008144650296557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186320077140005429766864371 279480115710008144650296557)
    ·
      refine ⟨104805043391253054243861209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279480115710008144650296557 104805043391253054243861209)
      ·
        refine ⟨78603782543439790682895907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104805043391253054243861209 78603782543439790682895907)
        ·
          refine ⟨117905673815159686024343861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78603782543439790682895907 117905673815159686024343861)
          ·
            refine ⟨11053656920171220564782237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117905673815159686024343861 11053656920171220564782237)
            ·
              refine ⟨4145121345064207711793339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11053656920171220564782237 4145121345064207711793339)
              ·
                refine ⟨6217682017596311567690009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4145121345064207711793339 6217682017596311567690009)
                ·
                  refine ⟨4663261513197233675767507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6217682017596311567690009 4663261513197233675767507)
                  ·
                    refine ⟨6994892269795850513651261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4663261513197233675767507 6994892269795850513651261)
                    ·
                      refine ⟨2623084601173443942619223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6994892269795850513651261 2623084601173443942619223)
                      ·
                        rfl

theorem cell23_5108439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_5108439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108439 prefixEnd_5108439 := by exact prefixLift 5108439
  have htrace : WordTrace (prefixWord ++ tailWord_5108439) baseStart_5108439 baseEnd_5108439 := by
    simpa [prefixWord, tailWord_5108439, baseEnd_5108439] using wordTrace_append hprefix tailTrace_5108439
  have hstable : (prefixWord ++ tailWord_5108439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108439).length < 2 ^ (prefixWord ++ tailWord_5108439).sum := by decide
  have hdescent : baseEnd_5108439 < baseStart_5108439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108448 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 5]
def baseStart_5108448 : Nat := 118140960795 + 5108448 * 2 ^ 59
def prefixEnd_5108448 : Nat := 4983230072969 + 3 ^ 40 * 5108448 * 2
def baseEnd_5108448 : Nat := 2623089222499334407406681

theorem tailTrace_5108448 : CollatzResearch.WordTrace tailWord_5108448 prefixEnd_5108448 2623089222499334407406681 := by
  unfold tailWord_5108448
  simp only [CollatzResearch.WordTrace]
  refine ⟨93160202698486412151970999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124213603597981882869294665 93160202698486412151970999)
  ·
    refine ⟨139740304047729618227956499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93160202698486412151970999 139740304047729618227956499)
    ·
      refine ⟨209610456071594427341934749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139740304047729618227956499 209610456071594427341934749)
      ·
        refine ⟨78603921026847910253225531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209610456071594427341934749 78603921026847910253225531)
        ·
          refine ⟨117905881540271865379838297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78603921026847910253225531 117905881540271865379838297)
          ·
            refine ⟨88429411155203899034878723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117905881540271865379838297 88429411155203899034878723)
            ·
              refine ⟨132644116732805848552318085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88429411155203899034878723 132644116732805848552318085)
              ·
                refine ⟨24870771887401096603559641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132644116732805848552318085 24870771887401096603559641)
                ·
                  refine ⟨18653078915550822452669731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24870771887401096603559641 18653078915550822452669731)
                  ·
                    refine ⟨27979618373326233679004597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18653078915550822452669731 27979618373326233679004597)
                    ·
                      refine ⟨2623089222499334407406681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27979618373326233679004597 2623089222499334407406681)
                      ·
                        rfl

theorem cell23_5108448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_5108448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108448 prefixEnd_5108448 := by exact prefixLift 5108448
  have htrace : WordTrace (prefixWord ++ tailWord_5108448) baseStart_5108448 baseEnd_5108448 := by
    simpa [prefixWord, tailWord_5108448, baseEnd_5108448] using wordTrace_append hprefix tailTrace_5108448
  have hstable : (prefixWord ++ tailWord_5108448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108448).length < 2 ^ (prefixWord ++ tailWord_5108448).sum := by decide
  have hdescent : baseEnd_5108448 < baseStart_5108448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108449 : List Nat := [1, 2, 3, 1, 4, 2, 2, 2, 1, 3, 2]
def baseStart_5108449 : Nat := 118140960795 + 5108449 * 2 ^ 59
def prefixEnd_5108449 : Nat := 4983230072969 + 3 ^ 40 * 5108449 * 2
def baseEnd_5108449 : Nat := 2623089735979988903494177

theorem tailTrace_5108449 : CollatzResearch.WordTrace tailWord_5108449 prefixEnd_5108449 2623089735979988903494177 := by
  unfold tailWord_5108449
  simp only [CollatzResearch.WordTrace]
  refine ⟨186320441869969201474728401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124213627913312800983152267 186320441869969201474728401)
  ·
    refine ⟨139740331402476901106046301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186320441869969201474728401 139740331402476901106046301)
    ·
      refine ⟨52402624275928837914767363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139740331402476901106046301 52402624275928837914767363)
      ·
        refine ⟨78603936413893256872151045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52402624275928837914767363 78603936413893256872151045)
        ·
          refine ⟨14738238077604985663528321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78603936413893256872151045 14738238077604985663528321)
          ·
            refine ⟨11053678558203739247646241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14738238077604985663528321 11053678558203739247646241)
            ·
              refine ⟨8290258918652804435734681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11053678558203739247646241 8290258918652804435734681)
              ·
                refine ⟨6217694188989603326801011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8290258918652804435734681 6217694188989603326801011)
                ·
                  refine ⟨9326541283484404990201517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6217694188989603326801011 9326541283484404990201517)
                  ·
                    refine ⟨3497452981306651871325569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9326541283484404990201517 3497452981306651871325569)
                    ·
                      refine ⟨2623089735979988903494177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3497452981306651871325569 2623089735979988903494177)
                      ·
                        rfl

theorem cell23_5108449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_5108449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108449 prefixEnd_5108449 := by exact prefixLift 5108449
  have htrace : WordTrace (prefixWord ++ tailWord_5108449) baseStart_5108449 baseEnd_5108449 := by
    simpa [prefixWord, tailWord_5108449, baseEnd_5108449] using wordTrace_append hprefix tailTrace_5108449
  have hstable : (prefixWord ++ tailWord_5108449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108449).length < 2 ^ (prefixWord ++ tailWord_5108449).sum := by decide
  have hdescent : baseEnd_5108449 < baseStart_5108449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108485 : List Nat := [1, 3, 1, 1, 2, 1, 1, 8, 5]
def baseStart_5108485 : Nat := 118140960795 + 5108485 * 2 ^ 59
def prefixEnd_5108485 : Nat := 4983230072969 + 3 ^ 40 * 5108485 * 2
def baseEnd_5108485 : Nat := 291456469031505640293779

theorem tailTrace_5108485 : CollatzResearch.WordTrace tailWord_5108485 prefixEnd_5108485 291456469031505640293779 := by
  unfold tailWord_5108485
  simp only [CollatzResearch.WordTrace]
  refine ⟨186321754897838779623038909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124214503265225853082025939 186321754897838779623038909)
  ·
    refine ⟨69870658086689542358639591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186321754897838779623038909 69870658086689542358639591)
    ·
      refine ⟨104805987130034313537959387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69870658086689542358639591 104805987130034313537959387)
      ·
        refine ⟨157208980695051470306939081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104805987130034313537959387 157208980695051470306939081)
        ·
          refine ⟨117906735521288602730204311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157208980695051470306939081 117906735521288602730204311)
          ·
            refine ⟨176860103281932904095306467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117906735521288602730204311 176860103281932904095306467)
            ·
              refine ⟨265290154922899356142959701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176860103281932904095306467 265290154922899356142959701)
              ·
                refine ⟨3108869003002726829800309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 265290154922899356142959701 3108869003002726829800309)
                ·
                  refine ⟨291456469031505640293779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3108869003002726829800309 291456469031505640293779)
                  ·
                    rfl

theorem cell23_5108485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_5108485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108485 prefixEnd_5108485 := by exact prefixLift 5108485
  have htrace : WordTrace (prefixWord ++ tailWord_5108485) baseStart_5108485 baseEnd_5108485 := by
    simpa [prefixWord, tailWord_5108485, baseEnd_5108485] using wordTrace_append hprefix tailTrace_5108485
  have hstable : (prefixWord ++ tailWord_5108485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108485).length < 2 ^ (prefixWord ++ tailWord_5108485).sum := by decide
  have hdescent : baseEnd_5108485 < baseStart_5108485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108505 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 4, 5, 2]
def baseStart_5108505 : Nat := 118140960795 + 5108505 * 2 ^ 59
def prefixEnd_5108505 : Nat := 4983230072969 + 3 ^ 40 * 5108505 * 2
def baseEnd_5108505 : Nat := 2623118490896640684393919

theorem tailTrace_5108505 : CollatzResearch.WordTrace tailWord_5108505 prefixEnd_5108505 2623118490896640684393919 := by
  unfold tailWord_5108505
  simp only [CollatzResearch.WordTrace]
  refine ⟨186322484357766323038766969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124214989571844215359177979 186322484357766323038766969)
  ·
    refine ⟨139741863268324742279075227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186322484357766323038766969 139741863268324742279075227)
    ·
      refine ⟨209612794902487113418612841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139741863268324742279075227 209612794902487113418612841)
      ·
        refine ⟨157209596176865335063959631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209612794902487113418612841 157209596176865335063959631)
        ·
          refine ⟨235814394265298002595939447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157209596176865335063959631 235814394265298002595939447)
          ·
            refine ⟨353721591397947003893909171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235814394265298002595939447 353721591397947003893909171)
            ·
              refine ⟨530582387096920505840863757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353721591397947003893909171 530582387096920505840863757)
              ·
                refine ⟨198968395161345189690323909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 530582387096920505840863757 198968395161345189690323909)
                ·
                  refine ⟨37306574092752223066935733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198968395161345189690323909 37306574092752223066935733)
                  ·
                    refine ⟨3497491321195520912525225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37306574092752223066935733 3497491321195520912525225)
                    ·
                      refine ⟨2623118490896640684393919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3497491321195520912525225 2623118490896640684393919)
                      ·
                        rfl

theorem cell23_5108505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 5, 2].length) (baseStart_5108505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108505 prefixEnd_5108505 := by exact prefixLift 5108505
  have htrace : WordTrace (prefixWord ++ tailWord_5108505) baseStart_5108505 baseEnd_5108505 := by
    simpa [prefixWord, tailWord_5108505, baseEnd_5108505] using wordTrace_append hprefix tailTrace_5108505
  have hstable : (prefixWord ++ tailWord_5108505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108505).length < 2 ^ (prefixWord ++ tailWord_5108505).sum := by decide
  have hdescent : baseEnd_5108505 < baseStart_5108505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108535 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_5108535 : Nat := 118140960795 + 5108535 * 2 ^ 59
def prefixEnd_5108535 : Nat := 4983230072969 + 3 ^ 40 * 5108535 * 2
def baseEnd_5108535 : Nat := 2623133895316275567018781

theorem tailTrace_5108535 : CollatzResearch.WordTrace tailWord_5108535 prefixEnd_5108535 2623133895316275567018781 := by
  unfold tailWord_5108535
  simp only [CollatzResearch.WordTrace]
  refine ⟨186323578547657638162359059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124215719031771758774906039 186323578547657638162359059)
  ·
    refine ⟨279485367821486457243538589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186323578547657638162359059 279485367821486457243538589)
    ·
      refine ⟨104807012933057421466326971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279485367821486457243538589 104807012933057421466326971)
      ·
        refine ⟨157210519399586132199490457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104807012933057421466326971 157210519399586132199490457)
        ·
          refine ⟨117907889549689599149617843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157210519399586132199490457 117907889549689599149617843)
          ·
            refine ⟨176861834324534398724426765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117907889549689599149617843 176861834324534398724426765)
            ·
              refine ⟨66323187871700399521660037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176861834324534398724426765 66323187871700399521660037)
              ·
                refine ⟨12435597725943824910311257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66323187871700399521660037 12435597725943824910311257)
                ·
                  refine ⟨9326698294457868682733443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12435597725943824910311257 9326698294457868682733443)
                  ·
                    refine ⟨13990047441686803024100165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9326698294457868682733443 13990047441686803024100165)
                    ·
                      refine ⟨2623133895316275567018781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13990047441686803024100165 2623133895316275567018781)
                      ·
                        rfl

theorem cell23_5108535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_5108535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108535 prefixEnd_5108535 := by exact prefixLift 5108535
  have htrace : WordTrace (prefixWord ++ tailWord_5108535) baseStart_5108535 baseEnd_5108535 := by
    simpa [prefixWord, tailWord_5108535, baseEnd_5108535] using wordTrace_append hprefix tailTrace_5108535
  have hstable : (prefixWord ++ tailWord_5108535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108535).length < 2 ^ (prefixWord ++ tailWord_5108535).sum := by decide
  have hdescent : baseEnd_5108535 < baseStart_5108535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108552 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 2, 4, 2]
def baseStart_5108552 : Nat := 118140960795 + 5108552 * 2 ^ 59
def prefixEnd_5108552 : Nat := 4983230072969 + 3 ^ 40 * 5108552 * 2
def baseEnd_5108552 : Nat := 2623142624487402000506203

theorem tailTrace_5108552 : CollatzResearch.WordTrace tailWord_5108552 prefixEnd_5108552 2623142624487402000506203 := by
  unfold tailWord_5108552
  simp only [CollatzResearch.WordTrace]
  refine ⟨93162099294298025032863955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124216132392397366710485273 93162099294298025032863955)
  ·
    refine ⟨139743148941447037549295933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93162099294298025032863955 139743148941447037549295933)
    ·
      refine ⟨52403680853042639080985975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139743148941447037549295933 52403680853042639080985975)
      ·
        refine ⟨78605521279563958621478963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52403680853042639080985975 78605521279563958621478963)
        ·
          refine ⟨117908281919345937932218445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78605521279563958621478963 117908281919345937932218445)
          ·
            refine ⟨44215605719754726724581917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117908281919345937932218445 44215605719754726724581917)
            ·
              refine ⟨16580852144908022521718219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44215605719754726724581917 16580852144908022521718219)
              ·
                refine ⟨24871278217362033782577329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16580852144908022521718219 24871278217362033782577329)
                ·
                  refine ⟨18653458663021525336932997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24871278217362033782577329 18653458663021525336932997)
                  ·
                    refine ⟨3497523499316536000674937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18653458663021525336932997 3497523499316536000674937)
                    ·
                      refine ⟨2623142624487402000506203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3497523499316536000674937 2623142624487402000506203)
                      ·
                        rfl

theorem cell23_5108552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_5108552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108552 prefixEnd_5108552 := by exact prefixLift 5108552
  have htrace : WordTrace (prefixWord ++ tailWord_5108552) baseStart_5108552 baseEnd_5108552 := by
    simpa [prefixWord, tailWord_5108552, baseEnd_5108552] using wordTrace_append hprefix tailTrace_5108552
  have hstable : (prefixWord ++ tailWord_5108552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108552).length < 2 ^ (prefixWord ++ tailWord_5108552).sum := by decide
  have hdescent : baseEnd_5108552 < baseStart_5108552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108562 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_5108562 : Nat := 118140960795 + 5108562 * 2 ^ 59
def prefixEnd_5108562 : Nat := 4983230072969 + 3 ^ 40 * 5108562 * 2
def baseEnd_5108562 : Nat := 874382586431315653793719

theorem tailTrace_5108562 : CollatzResearch.WordTrace tailWord_5108562 prefixEnd_5108562 874382586431315653793719 := by
  unfold tailWord_5108562
  simp only [CollatzResearch.WordTrace]
  refine ⟨46581140829639955443397985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124216375545706547849061293 46581140829639955443397985)
  ·
    refine ⟨34935855622229966582548489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46581140829639955443397985 34935855622229966582548489)
    ·
      refine ⟨26201891716672474936911367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34935855622229966582548489 26201891716672474936911367)
      ·
        refine ⟨39302837575008712405367051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26201891716672474936911367 39302837575008712405367051)
        ·
          refine ⟨58954256362513068608050577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39302837575008712405367051 58954256362513068608050577)
          ·
            refine ⟨44215692271884801456037933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58954256362513068608050577 44215692271884801456037933)
            ·
              refine ⟨16580884601956800546014225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44215692271884801456037933 16580884601956800546014225)
              ·
                refine ⟨12435663451467600409510669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16580884601956800546014225 12435663451467600409510669)
                ·
                  refine ⟨4663373794300350153566501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12435663451467600409510669 4663373794300350153566501)
                  ·
                    refine ⟨874382586431315653793719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4663373794300350153566501 874382586431315653793719)
                    ·
                      rfl

theorem cell23_5108562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_5108562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108562 prefixEnd_5108562 := by exact prefixLift 5108562
  have htrace : WordTrace (prefixWord ++ tailWord_5108562) baseStart_5108562 baseEnd_5108562 := by
    simpa [prefixWord, tailWord_5108562, baseEnd_5108562] using wordTrace_append hprefix tailTrace_5108562
  have hstable : (prefixWord ++ tailWord_5108562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108562).length < 2 ^ (prefixWord ++ tailWord_5108562).sum := by decide
  have hdescent : baseEnd_5108562 < baseStart_5108562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108579 : List Nat := [1, 1, 1, 5, 3, 1, 1, 5, 1, 4]
def baseStart_5108579 : Nat := 118140960795 + 5108579 * 2 ^ 59
def prefixEnd_5108579 : Nat := 4983230072969 + 3 ^ 40 * 5108579 * 2
def baseEnd_5108579 : Nat := 874385496155024464956193

theorem tailTrace_5108579 : CollatzResearch.WordTrace tailWord_5108579 prefixEnd_5108579 874385496155024464956193 := by
  unfold tailWord_5108579
  simp only [CollatzResearch.WordTrace]
  refine ⟨186325183359498233676960791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124216788906332155784640527 186325183359498233676960791)
  ·
    refine ⟨279487775039247350515441187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186325183359498233676960791 279487775039247350515441187)
    ·
      refine ⟨419231662558871025773161781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279487775039247350515441187 419231662558871025773161781)
      ·
        refine ⟨39302968364894158666233917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 419231662558871025773161781 39302968364894158666233917)
        ·
          refine ⟨14738613136835309499837719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39302968364894158666233917 14738613136835309499837719)
          ·
            refine ⟨22107919705252964249756579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14738613136835309499837719 22107919705252964249756579)
            ·
              refine ⟨33161879557879446374634869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22107919705252964249756579 33161879557879446374634869)
              ·
                refine ⟨3108926208551198097622019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33161879557879446374634869 3108926208551198097622019)
                ·
                  refine ⟨4663389312826797146433029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108926208551198097622019 4663389312826797146433029)
                  ·
                    refine ⟨874385496155024464956193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4663389312826797146433029 874385496155024464956193)
                    ·
                      rfl

theorem cell23_5108579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 1, 4].length) (baseStart_5108579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108579 prefixEnd_5108579 := by exact prefixLift 5108579
  have htrace : WordTrace (prefixWord ++ tailWord_5108579) baseStart_5108579 baseEnd_5108579 := by
    simpa [prefixWord, tailWord_5108579, baseEnd_5108579] using wordTrace_append hprefix tailTrace_5108579
  have hstable : (prefixWord ++ tailWord_5108579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108579).length < 2 ^ (prefixWord ++ tailWord_5108579).sum := by decide
  have hdescent : baseEnd_5108579 < baseStart_5108579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108605 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_5108605 : Nat := 118140960795 + 5108605 * 2 ^ 59
def prefixEnd_5108605 : Nat := 4983230072969 + 3 ^ 40 * 5108605 * 2
def baseEnd_5108605 : Nat := 874389946320696764381153

theorem tailTrace_5108605 : CollatzResearch.WordTrace tailWord_5108605 prefixEnd_5108605 874389946320696764381153 := by
  unfold tailWord_5108605
  simp only [CollatzResearch.WordTrace]
  refine ⟨186326131657404040117407269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124217421104936026744938179 186326131657404040117407269)
  ·
    refine ⟨34936149685763257522013863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186326131657404040117407269 34936149685763257522013863)
    ·
      refine ⟨52404224528644886283020795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34936149685763257522013863 52404224528644886283020795)
      ·
        refine ⟨78606336792967329424531193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52404224528644886283020795 78606336792967329424531193)
        ·
          refine ⟨58954752594725497068398395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78606336792967329424531193 58954752594725497068398395)
          ·
            refine ⟨88432128892088245602597593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58954752594725497068398395 88432128892088245602597593)
            ·
              refine ⟨66324096669066184201948195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88432128892088245602597593 66324096669066184201948195)
              ·
                refine ⟨99486145003599276302922293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66324096669066184201948195 99486145003599276302922293)
                ·
                  refine ⟨9326826094087432153398965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99486145003599276302922293 9326826094087432153398965)
                  ·
                    refine ⟨874389946320696764381153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9326826094087432153398965 874389946320696764381153)
                    ·
                      rfl

theorem cell23_5108605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_5108605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108605 prefixEnd_5108605 := by exact prefixLift 5108605
  have htrace : WordTrace (prefixWord ++ tailWord_5108605) baseStart_5108605 baseEnd_5108605 := by
    simpa [prefixWord, tailWord_5108605, baseEnd_5108605] using wordTrace_append hprefix tailTrace_5108605
  have hstable : (prefixWord ++ tailWord_5108605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108605).length < 2 ^ (prefixWord ++ tailWord_5108605).sum := by decide
  have hdescent : baseEnd_5108605 < baseStart_5108605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108630 : List Nat := [5, 3, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_5108630 : Nat := 118140960795 + 5108630 * 2 ^ 59
def prefixEnd_5108630 : Nat := 4983230072969 + 3 ^ 40 * 5108630 * 2
def baseEnd_5108630 : Nat := 874394225326150898443615

theorem tailTrace_5108630 : CollatzResearch.WordTrace tailWord_5108630 prefixEnd_5108630 874394225326150898443615 := by
  unfold tailWord_5108630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11645440217644591836691709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124218028988208979591378229 11645440217644591836691709)
  ·
    refine ⟨4367040081616721938759391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11645440217644591836691709 4367040081616721938759391)
    ·
      refine ⟨6550560122425082908139087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4367040081616721938759391 6550560122425082908139087)
      ·
        refine ⟨9825840183637624362208631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6550560122425082908139087 9825840183637624362208631)
        ·
          refine ⟨14738760275456436543312947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9825840183637624362208631 14738760275456436543312947)
          ·
            refine ⟨22108140413184654814969421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14738760275456436543312947 22108140413184654814969421)
            ·
              refine ⟨8290552654944245555613533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22108140413184654814969421 8290552654944245555613533)
              ·
                refine ⟨3108957245604092083355075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8290552654944245555613533 3108957245604092083355075)
                ·
                  refine ⟨4663435868406138125032613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108957245604092083355075 4663435868406138125032613)
                  ·
                    refine ⟨874394225326150898443615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4663435868406138125032613 874394225326150898443615)
                    ·
                      rfl

theorem cell23_5108630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_5108630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108630 prefixEnd_5108630 := by exact prefixLift 5108630
  have htrace : WordTrace (prefixWord ++ tailWord_5108630) baseStart_5108630 baseEnd_5108630 := by
    simpa [prefixWord, tailWord_5108630, baseEnd_5108630] using wordTrace_append hprefix tailTrace_5108630
  have hstable : (prefixWord ++ tailWord_5108630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108630).length < 2 ^ (prefixWord ++ tailWord_5108630).sum := by decide
  have hdescent : baseEnd_5108630 < baseStart_5108630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108655 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 4]
def baseStart_5108655 : Nat := 118140960795 + 5108655 * 2 ^ 59
def prefixEnd_5108655 : Nat := 4983230072969 + 3 ^ 40 * 5108655 * 2
def baseEnd_5108655 : Nat := 2623195512994815097518229

theorem tailTrace_5108655 : CollatzResearch.WordTrace tailWord_5108655 prefixEnd_5108655 2623195512994815097518229 := by
  unfold tailWord_5108655
  simp only [CollatzResearch.WordTrace]
  refine ⟨186327955307222898656727419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124218636871481932437818279 186327955307222898656727419)
  ·
    refine ⟨279491932960834347985091129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186327955307222898656727419 279491932960834347985091129)
    ·
      refine ⟨209618949720625760988818347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279491932960834347985091129 209618949720625760988818347)
      ·
        refine ⟨314428424580938641483227521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209618949720625760988818347 314428424580938641483227521)
        ·
          refine ⟨235821318435703981112420641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314428424580938641483227521 235821318435703981112420641)
          ·
            refine ⟨176865988826777985834315481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235821318435703981112420641 176865988826777985834315481)
            ·
              refine ⟨132649491620083489375736611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176865988826777985834315481 132649491620083489375736611)
              ·
                refine ⟨198974237430125234063604917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132649491620083489375736611 198974237430125234063604917)
                ·
                  refine ⟨18653834759074240693462961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198974237430125234063604917 18653834759074240693462961)
                  ·
                    refine ⟨13990376069305680520097221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18653834759074240693462961 13990376069305680520097221)
                    ·
                      refine ⟨2623195512994815097518229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13990376069305680520097221 2623195512994815097518229)
                      ·
                        rfl

theorem cell23_5108655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_5108655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108655 prefixEnd_5108655 := by exact prefixLift 5108655
  have htrace : WordTrace (prefixWord ++ tailWord_5108655) baseStart_5108655 baseEnd_5108655 := by
    simpa [prefixWord, tailWord_5108655, baseEnd_5108655] using wordTrace_append hprefix tailTrace_5108655
  have hstable : (prefixWord ++ tailWord_5108655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108655).length < 2 ^ (prefixWord ++ tailWord_5108655).sum := by decide
  have hdescent : baseEnd_5108655 < baseStart_5108655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108659 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 3, 2, 2]
def baseStart_5108659 : Nat := 118140960795 + 5108659 * 2 ^ 59
def prefixEnd_5108659 : Nat := 4983230072969 + 3 ^ 40 * 5108659 * 2
def baseEnd_5108659 : Nat := 2623197566917433081868211

theorem tailTrace_5108659 : CollatzResearch.WordTrace tailWord_5108659 prefixEnd_5108659 2623197566917433081868211 := by
  unfold tailWord_5108659
  simp only [CollatzResearch.WordTrace]
  refine ⟨186328101199208407339873031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124218734132805604893248687 186328101199208407339873031)
  ·
    refine ⟨279492151798812611009809547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186328101199208407339873031 279492151798812611009809547)
    ·
      refine ⟨419238227698218916514714321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279492151798812611009809547 419238227698218916514714321)
      ·
        refine ⟨314428670773664187386035741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419238227698218916514714321 314428670773664187386035741)
        ·
          refine ⟨117910751540124070269763403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314428670773664187386035741 117910751540124070269763403)
          ·
            refine ⟨176866127310186105404645105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117910751540124070269763403 176866127310186105404645105)
            ·
              refine ⟨132649595482639579053483829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176866127310186105404645105 132649595482639579053483829)
              ·
                refine ⟨12435899576497460536264109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132649595482639579053483829 12435899576497460536264109)
                ·
                  refine ⟨4663462341186547701099041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12435899576497460536264109 4663462341186547701099041)
                  ·
                    refine ⟨3497596755889910775824281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4663462341186547701099041 3497596755889910775824281)
                    ·
                      refine ⟨2623197566917433081868211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3497596755889910775824281 2623197566917433081868211)
                      ·
                        rfl

theorem cell23_5108659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 2, 2].length) (baseStart_5108659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108659 prefixEnd_5108659 := by exact prefixLift 5108659
  have htrace : WordTrace (prefixWord ++ tailWord_5108659) baseStart_5108659 baseEnd_5108659 := by
    simpa [prefixWord, tailWord_5108659, baseEnd_5108659] using wordTrace_append hprefix tailTrace_5108659
  have hstable : (prefixWord ++ tailWord_5108659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108659).length < 2 ^ (prefixWord ++ tailWord_5108659).sum := by decide
  have hdescent : baseEnd_5108659 < baseStart_5108659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108665 : List Nat := [1, 2, 1, 4, 2, 2, 1, 10]
def baseStart_5108665 : Nat := 118140960795 + 5108665 * 2 ^ 59
def prefixEnd_5108665 : Nat := 4983230072969 + 3 ^ 40 * 5108665 * 2
def baseEnd_5108665 : Nat := 97155579548198520681229

theorem tailTrace_5108665 : CollatzResearch.WordTrace tailWord_5108665 prefixEnd_5108665 97155579548198520681229 := by
  unfold tailWord_5108665
  simp only [CollatzResearch.WordTrace]
  refine ⟨186328320037186670364591449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124218880024791113576394299 186328320037186670364591449)
  ·
    refine ⟨139746240027890002773443587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186328320037186670364591449 139746240027890002773443587)
    ·
      refine ⟨209619360041835004160165381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139746240027890002773443587 209619360041835004160165381)
      ·
        refine ⟨39303630007844063280031009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209619360041835004160165381 39303630007844063280031009)
        ·
          refine ⟨29477722505883047460023257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39303630007844063280031009 29477722505883047460023257)
          ·
            refine ⟨22108291879412285595017443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29477722505883047460023257 22108291879412285595017443)
            ·
              refine ⟨33162437819118428392526165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22108291879412285595017443 33162437819118428392526165)
              ·
                refine ⟨97155579548198520681229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33162437819118428392526165 97155579548198520681229)
                ·
                  rfl

theorem cell23_5108665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 10].length) (baseStart_5108665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108665 prefixEnd_5108665 := by exact prefixLift 5108665
  have htrace : WordTrace (prefixWord ++ tailWord_5108665) baseStart_5108665 baseEnd_5108665 := by
    simpa [prefixWord, tailWord_5108665, baseEnd_5108665] using wordTrace_append hprefix tailTrace_5108665
  have hstable : (prefixWord ++ tailWord_5108665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108665).length < 2 ^ (prefixWord ++ tailWord_5108665).sum := by decide
  have hdescent : baseEnd_5108665 < baseStart_5108665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108676 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_5108676 : Nat := 118140960795 + 5108676 * 2 ^ 59
def prefixEnd_5108676 : Nat := 4983230072969 + 3 ^ 40 * 5108676 * 2
def baseEnd_5108676 : Nat := 2623206296088559515355633

theorem tailTrace_5108676 : CollatzResearch.WordTrace tailWord_5108676 prefixEnd_5108676 2623206296088559515355633 := by
  unfold tailWord_5108676
  simp only [CollatzResearch.WordTrace]
  refine ⟨93164360620073409621620941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124219147493431212828827921 93164360620073409621620941)
  ·
    refine ⟨34936635232527528608107853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93164360620073409621620941 34936635232527528608107853)
    ·
      refine ⟨13101238212197823228040445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34936635232527528608107853 13101238212197823228040445)
      ·
        refine ⟨4912964329574183710515167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13101238212197823228040445 4912964329574183710515167)
        ·
          refine ⟨7369446494361275565772751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4912964329574183710515167 7369446494361275565772751)
          ·
            refine ⟨11054169741541913348659127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7369446494361275565772751 11054169741541913348659127)
            ·
              refine ⟨16581254612312870022988691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11054169741541913348659127 16581254612312870022988691)
              ·
                refine ⟨24871881918469305034483037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16581254612312870022988691 24871881918469305034483037)
                ·
                  refine ⟨9326955719425989387931139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24871881918469305034483037 9326955719425989387931139)
                  ·
                    refine ⟨13990433579138984081896709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9326955719425989387931139 13990433579138984081896709)
                    ·
                      refine ⟨2623206296088559515355633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13990433579138984081896709 2623206296088559515355633)
                      ·
                        rfl

theorem cell23_5108676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_5108676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108676 prefixEnd_5108676 := by exact prefixLift 5108676
  have htrace : WordTrace (prefixWord ++ tailWord_5108676) baseStart_5108676 baseEnd_5108676 := by
    simpa [prefixWord, tailWord_5108676, baseEnd_5108676] using wordTrace_append hprefix tailTrace_5108676
  have hstable : (prefixWord ++ tailWord_5108676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108676).length < 2 ^ (prefixWord ++ tailWord_5108676).sum := by decide
  have hdescent : baseEnd_5108676 < baseStart_5108676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108679 : List Nat := [1, 1, 4, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_5108679 : Nat := 118140960795 + 5108679 * 2 ^ 59
def prefixEnd_5108679 : Nat := 4983230072969 + 3 ^ 40 * 5108679 * 2
def baseEnd_5108679 : Nat := 2623207836530523003618119

theorem tailTrace_5108679 : CollatzResearch.WordTrace tailWord_5108679 prefixEnd_5108679 2623207836530523003618119 := by
  unfold tailWord_5108679
  simp only [CollatzResearch.WordTrace]
  refine ⟨186328830659135950755601091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124219220439423967170400727 186328830659135950755601091)
  ·
    refine ⟨279493245988703926133401637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186328830659135950755601091 279493245988703926133401637)
    ·
      refine ⟨52404983622881986150012807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279493245988703926133401637 52404983622881986150012807)
      ·
        refine ⟨78607475434322979225019211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52404983622881986150012807 78607475434322979225019211)
        ·
          refine ⟨117911213151484468837528817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78607475434322979225019211 117911213151484468837528817)
          ·
            refine ⟨88433409863613351628146613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117911213151484468837528817 88433409863613351628146613)
            ·
              refine ⟨8290632174713751715138745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88433409863613351628146613 8290632174713751715138745)
              ·
                refine ⟨6217974131035313786354059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8290632174713751715138745 6217974131035313786354059)
                ·
                  refine ⟨9326961196552970679531089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6217974131035313786354059 9326961196552970679531089)
                  ·
                    refine ⟨6995220897414728009648317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9326961196552970679531089 6995220897414728009648317)
                    ·
                      refine ⟨2623207836530523003618119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6995220897414728009648317 2623207836530523003618119)
                      ·
                        rfl

theorem cell23_5108679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_5108679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108679 prefixEnd_5108679 := by exact prefixLift 5108679
  have htrace : WordTrace (prefixWord ++ tailWord_5108679) baseStart_5108679 baseEnd_5108679 := by
    simpa [prefixWord, tailWord_5108679, baseEnd_5108679] using wordTrace_append hprefix tailTrace_5108679
  have hstable : (prefixWord ++ tailWord_5108679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108679).length < 2 ^ (prefixWord ++ tailWord_5108679).sum := by decide
  have hdescent : baseEnd_5108679 < baseStart_5108679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108696 : List Nat := [2, 1, 2, 2, 2, 4, 3, 1, 1, 2, 3]
def baseStart_5108696 : Nat := 118140960795 + 5108696 * 2 ^ 59
def prefixEnd_5108696 : Nat := 4983230072969 + 3 ^ 40 * 5108696 * 2
def baseEnd_5108696 : Nat := 2623216565701649437105541

theorem tailTrace_5108696 : CollatzResearch.WordTrace tailWord_5108696 prefixEnd_5108696 2623216565701649437105541 := by
  unfold tailWord_5108696
  simp only [CollatzResearch.WordTrace]
  refine ⟨93164725350037181329484971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124219633800049575105979961 93164725350037181329484971)
  ·
    refine ⟨139747088025055771994227457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93164725350037181329484971 139747088025055771994227457)
    ·
      refine ⟨104810316018791828995670593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139747088025055771994227457 104810316018791828995670593)
      ·
        refine ⟨78607737014093871746752945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104810316018791828995670593 78607737014093871746752945)
        ·
          refine ⟨58955802760570403810064709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78607737014093871746752945 58955802760570403810064709)
          ·
            refine ⟨11054213017606950714387133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58955802760570403810064709 11054213017606950714387133)
            ·
              refine ⟨4145329881602606517895175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11054213017606950714387133 4145329881602606517895175)
              ·
                refine ⟨6217994822403909776842763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4145329881602606517895175 6217994822403909776842763)
                ·
                  refine ⟨9326992233605864665264145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6217994822403909776842763 9326992233605864665264145)
                  ·
                    refine ⟨6995244175204398498948109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9326992233605864665264145 6995244175204398498948109)
                    ·
                      refine ⟨2623216565701649437105541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6995244175204398498948109 2623216565701649437105541)
                      ·
                        rfl

theorem cell23_5108696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_5108696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108696 prefixEnd_5108696 := by exact prefixLift 5108696
  have htrace : WordTrace (prefixWord ++ tailWord_5108696) baseStart_5108696 baseEnd_5108696 := by
    simpa [prefixWord, tailWord_5108696, baseEnd_5108696] using wordTrace_append hprefix tailTrace_5108696
  have hstable : (prefixWord ++ tailWord_5108696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108696).length < 2 ^ (prefixWord ++ tailWord_5108696).sum := by decide
  have hdescent : baseEnd_5108696 < baseStart_5108696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108719 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 3, 3, 2]
def baseStart_5108719 : Nat := 118140960795 + 5108719 * 2 ^ 59
def prefixEnd_5108719 : Nat := 4983230072969 + 3 ^ 40 * 5108719 * 2
def baseEnd_5108719 : Nat := 2623228375756702847117935

theorem tailTrace_5108719 : CollatzResearch.WordTrace tailWord_5108719 prefixEnd_5108719 2623228375756702847117935 := by
  unfold tailWord_5108719
  simp only [CollatzResearch.WordTrace]
  refine ⟨186330289578991037587057211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124220193052660691724704807 186330289578991037587057211)
  ·
    refine ⟨279495434368486556380585817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186330289578991037587057211 279495434368486556380585817)
    ·
      refine ⟨209621575776364917285439363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279495434368486556380585817 209621575776364917285439363)
      ·
        refine ⟨314432363664547375928159045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209621575776364917285439363 314432363664547375928159045)
        ·
          refine ⟨58956068187102632986529821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 314432363664547375928159045 58956068187102632986529821)
          ·
            refine ⟨22108525570163487369948683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58956068187102632986529821 22108525570163487369948683)
            ·
              refine ⟨33162788355245231054923025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22108525570163487369948683 33162788355245231054923025)
              ·
                refine ⟨24872091266433923291192269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33162788355245231054923025 24872091266433923291192269)
                ·
                  refine ⟨9327034224912721234197101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24872091266433923291192269 9327034224912721234197101)
                  ·
                    refine ⟨3497637834342270462823913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9327034224912721234197101 3497637834342270462823913)
                    ·
                      refine ⟨2623228375756702847117935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3497637834342270462823913 2623228375756702847117935)
                      ·
                        rfl

theorem cell23_5108719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 3, 2].length) (baseStart_5108719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108719 prefixEnd_5108719 := by exact prefixLift 5108719
  have htrace : WordTrace (prefixWord ++ tailWord_5108719) baseStart_5108719 baseEnd_5108719 := by
    simpa [prefixWord, tailWord_5108719, baseEnd_5108719] using wordTrace_append hprefix tailTrace_5108719
  have hstable : (prefixWord ++ tailWord_5108719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108719).length < 2 ^ (prefixWord ++ tailWord_5108719).sum := by decide
  have hdescent : baseEnd_5108719 < baseStart_5108719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108726 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_5108726 : Nat := 118140960795 + 5108726 * 2 ^ 59
def prefixEnd_5108726 : Nat := 4983230072969 + 3 ^ 40 * 5108726 * 2
def baseEnd_5108726 : Nat := 2623231970121284319730403

theorem tailTrace_5108726 : CollatzResearch.WordTrace tailWord_5108726 prefixEnd_5108726 2623231970121284319730403 := by
  unfold tailWord_5108726
  simp only [CollatzResearch.WordTrace]
  refine ⟨11645659055622854861410127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124220363259977118521708021 11645659055622854861410127)
  ·
    refine ⟨17468488583434282292115191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11645659055622854861410127 17468488583434282292115191)
    ·
      refine ⟨26202732875151423438172787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17468488583434282292115191 26202732875151423438172787)
      ·
        refine ⟨39304099312727135157259181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26202732875151423438172787 39304099312727135157259181)
        ·
          refine ⟨14739037242272675683972193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39304099312727135157259181 14739037242272675683972193)
          ·
            refine ⟨11054277931704506762979145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14739037242272675683972193 11054277931704506762979145)
            ·
              refine ⟨8290708448778380072234359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11054277931704506762979145 8290708448778380072234359)
              ·
                refine ⟨12436062673167570108351539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8290708448778380072234359 12436062673167570108351539)
                ·
                  refine ⟨18654094009751355162527309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12436062673167570108351539 18654094009751355162527309)
                  ·
                    refine ⟨6995285253656758185947741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18654094009751355162527309 6995285253656758185947741)
                    ·
                      refine ⟨2623231970121284319730403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6995285253656758185947741 2623231970121284319730403)
                      ·
                        rfl

theorem cell23_5108726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_5108726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108726 prefixEnd_5108726 := by exact prefixLift 5108726
  have htrace : WordTrace (prefixWord ++ tailWord_5108726) baseStart_5108726 baseEnd_5108726 := by
    simpa [prefixWord, tailWord_5108726, baseEnd_5108726] using wordTrace_append hprefix tailTrace_5108726
  have hstable : (prefixWord ++ tailWord_5108726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108726).length < 2 ^ (prefixWord ++ tailWord_5108726).sum := by decide
  have hdescent : baseEnd_5108726 < baseStart_5108726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108755 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 11]
def baseStart_5108755 : Nat := 118140960795 + 5108755 * 2 ^ 59
def prefixEnd_5108755 : Nat := 4983230072969 + 3 ^ 40 * 5108755 * 2
def baseEnd_5108755 : Nat := 291471873451140522918641

theorem tailTrace_5108755 : CollatzResearch.WordTrace tailWord_5108755 prefixEnd_5108755 291471873451140522918641 := by
  unfold tailWord_5108755
  simp only [CollatzResearch.WordTrace]
  refine ⟨186331602606860615735367719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124221068404573743823578479 186331602606860615735367719)
  ·
    refine ⟨279497403910290923603051579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186331602606860615735367719 279497403910290923603051579)
    ·
      refine ⟨419246105865436385404577369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279497403910290923603051579 419246105865436385404577369)
      ·
        refine ⟨314434579399077289053433027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419246105865436385404577369 314434579399077289053433027)
        ·
          refine ⟨471651869098615933580149541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314434579399077289053433027 471651869098615933580149541)
          ·
            refine ⟨88434725455990487546278039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 471651869098615933580149541 88434725455990487546278039)
            ·
              refine ⟨132652088183985731319417059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88434725455990487546278039 132652088183985731319417059)
              ·
                refine ⟨198978132275978596979125589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132652088183985731319417059 198978132275978596979125589)
                ·
                  refine ⟨291471873451140522918641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 198978132275978596979125589 291471873451140522918641)
                  ·
                    rfl

theorem cell23_5108755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 11].length) (baseStart_5108755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108755 prefixEnd_5108755 := by exact prefixLift 5108755
  have htrace : WordTrace (prefixWord ++ tailWord_5108755) baseStart_5108755 baseEnd_5108755 := by
    simpa [prefixWord, tailWord_5108755, baseEnd_5108755] using wordTrace_append hprefix tailTrace_5108755
  have hstable : (prefixWord ++ tailWord_5108755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108755).length < 2 ^ (prefixWord ++ tailWord_5108755).sum := by decide
  have hdescent : baseEnd_5108755 < baseStart_5108755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108762 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_5108762 : Nat := 118140960795 + 5108762 * 2 ^ 59
def prefixEnd_5108762 : Nat := 4983230072969 + 3 ^ 40 * 5108762 * 2
def baseEnd_5108762 : Nat := 2623250455424846178880237

theorem tailTrace_5108762 : CollatzResearch.WordTrace tailWord_5108762 prefixEnd_5108762 2623250455424846178880237 := by
  unfold tailWord_5108762
  simp only [CollatzResearch.WordTrace]
  refine ⟨46582964479458813982718135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124221238611890170620581693 46582964479458813982718135)
  ·
    refine ⟨69874446719188220974077203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46582964479458813982718135 69874446719188220974077203)
    ·
      refine ⟨104811670078782331461115805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69874446719188220974077203 104811670078782331461115805)
      ·
        refine ⟨39304376279543374297918427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104811670078782331461115805 39304376279543374297918427)
        ·
          refine ⟨58956564419315061446877641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39304376279543374297918427 58956564419315061446877641)
          ·
            refine ⟨44217423314486296085158231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58956564419315061446877641 44217423314486296085158231)
            ·
              refine ⟨66326134971729444127737347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44217423314486296085158231 66326134971729444127737347)
              ·
                refine ⟨99489202457594166191606021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66326134971729444127737347 99489202457594166191606021)
                ·
                  refine ⟨18654225460798906160926129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99489202457594166191606021 18654225460798906160926129)
                  ·
                    refine ⟨13990669095599179620694597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18654225460798906160926129 13990669095599179620694597)
                    ·
                      refine ⟨2623250455424846178880237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13990669095599179620694597 2623250455424846178880237)
                      ·
                        rfl

theorem cell23_5108762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_5108762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108762 prefixEnd_5108762 := by exact prefixLift 5108762
  have htrace : WordTrace (prefixWord ++ tailWord_5108762) baseStart_5108762 baseEnd_5108762 := by
    simpa [prefixWord, tailWord_5108762, baseEnd_5108762] using wordTrace_append hprefix tailTrace_5108762
  have hstable : (prefixWord ++ tailWord_5108762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108762).length < 2 ^ (prefixWord ++ tailWord_5108762).sum := by decide
  have hdescent : baseEnd_5108762 < baseStart_5108762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108812 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_5108812 : Nat := 118140960795 + 5108812 * 2 ^ 59
def prefixEnd_5108812 : Nat := 4983230072969 + 3 ^ 40 * 5108812 * 2
def baseEnd_5108812 : Nat := 2623276129457570983255007

theorem tailTrace_5108812 : CollatzResearch.WordTrace tailWord_5108812 prefixEnd_5108812 2623276129457570983255007 := by
  unfold tailWord_5108812
  simp only [CollatzResearch.WordTrace]
  refine ⟨93166840783827057235096345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124222454378436076313461793 93166840783827057235096345)
  ·
    refine ⟨69875130587870292926322259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93166840783827057235096345 69875130587870292926322259)
    ·
      refine ⟨104812695881805439389483389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69875130587870292926322259 104812695881805439389483389)
      ·
        refine ⟨39304760955677039771056271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104812695881805439389483389 39304760955677039771056271)
        ·
          refine ⟨58957141433515559656584407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39304760955677039771056271 58957141433515559656584407)
          ·
            refine ⟨88435712150273339484876611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58957141433515559656584407 88435712150273339484876611)
            ·
              refine ⟨132653568225410009227314917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88435712150273339484876611 132653568225410009227314917)
              ·
                refine ⟨24872544042264376730121547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132653568225410009227314917 24872544042264376730121547)
                ·
                  refine ⟨37308816063396565095182321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24872544042264376730121547 37308816063396565095182321)
                  ·
                    refine ⟨27981612047547423821386741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37308816063396565095182321 27981612047547423821386741)
                    ·
                      refine ⟨2623276129457570983255007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27981612047547423821386741 2623276129457570983255007)
                      ·
                        rfl

theorem cell23_5108812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_5108812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108812 prefixEnd_5108812 := by exact prefixLift 5108812
  have htrace : WordTrace (prefixWord ++ tailWord_5108812) baseStart_5108812 baseEnd_5108812 := by
    simpa [prefixWord, tailWord_5108812, baseEnd_5108812] using wordTrace_append hprefix tailTrace_5108812
  have hstable : (prefixWord ++ tailWord_5108812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108812).length < 2 ^ (prefixWord ++ tailWord_5108812).sum := by decide
  have hdescent : baseEnd_5108812 < baseStart_5108812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108853 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 2, 5]
def baseStart_5108853 : Nat := 118140960795 + 5108853 * 2 ^ 59
def prefixEnd_5108853 : Nat := 4983230072969 + 3 ^ 40 * 5108853 * 2
def baseEnd_5108853 : Nat := 874432394054801774280773

theorem tailTrace_5108853 : CollatzResearch.WordTrace tailWord_5108853 prefixEnd_5108853 874432394054801774280773 := by
  unfold tailWord_5108853
  simp only [CollatzResearch.WordTrace]
  refine ⟨186335176960505578472435213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124223451307003718981623475 186335176960505578472435213)
  ·
    refine ⟨69875691360189591927163205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186335176960505578472435213 69875691360189591927163205)
    ·
      refine ⟨13101692130035548486343101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69875691360189591927163205 13101692130035548486343101)
      ·
        refine ⟨4913134548763330682378663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13101692130035548486343101 4913134548763330682378663)
        ·
          refine ⟨7369701823144996023567995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4913134548763330682378663 7369701823144996023567995)
          ·
            refine ⟨11054552734717494035351993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7369701823144996023567995 11054552734717494035351993)
            ·
              refine ⟨8290914551038120526513995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11054552734717494035351993 8290914551038120526513995)
              ·
                refine ⟨12436371826557180789770993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8290914551038120526513995 12436371826557180789770993)
                ·
                  refine ⟨9327278869917885592328245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12436371826557180789770993 9327278869917885592328245)
                  ·
                    refine ⟨874432394054801774280773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9327278869917885592328245 874432394054801774280773)
                    ·
                      rfl

theorem cell23_5108853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_5108853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108853 prefixEnd_5108853 := by exact prefixLift 5108853
  have htrace : WordTrace (prefixWord ++ tailWord_5108853) baseStart_5108853 baseEnd_5108853 := by
    simpa [prefixWord, tailWord_5108853, baseEnd_5108853] using wordTrace_append hprefix tailTrace_5108853
  have hstable : (prefixWord ++ tailWord_5108853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108853).length < 2 ^ (prefixWord ++ tailWord_5108853).sum := by decide
  have hdescent : baseEnd_5108853 < baseStart_5108853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108883 : List Nat := [1, 1, 1, 2, 1, 2, 8, 2, 1, 4]
def baseStart_5108883 : Nat := 118140960795 + 5108883 * 2 ^ 59
def prefixEnd_5108883 : Nat := 4983230072969 + 3 ^ 40 * 5108883 * 2
def baseEnd_5108883 : Nat := 874437528861346735155727

theorem tailTrace_5108883 : CollatzResearch.WordTrace tailWord_5108883 prefixEnd_5108883 874437528861346735155727 := by
  unfold tailWord_5108883
  simp only [CollatzResearch.WordTrace]
  refine ⟨186336271150396893596027303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124224180766931262397351535 186336271150396893596027303)
  ·
    refine ⟨279504406725595340394040955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186336271150396893596027303 279504406725595340394040955)
    ·
      refine ⟨419256610088393010591061433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279504406725595340394040955 419256610088393010591061433)
      ·
        refine ⟨314442457566294757943296075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419256610088393010591061433 314442457566294757943296075)
        ·
          refine ⟨471663686349442136914944113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314442457566294757943296075 471663686349442136914944113)
          ·
            refine ⟨353747764762081602686208085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471663686349442136914944113 353747764762081602686208085)
            ·
              refine ⟨4145481618305643781479001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 353747764762081602686208085 4145481618305643781479001)
              ·
                refine ⟨3109111213729232836109251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4145481618305643781479001 3109111213729232836109251)
                ·
                  refine ⟨4663666820593849254163877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3109111213729232836109251 4663666820593849254163877)
                  ·
                    refine ⟨874437528861346735155727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4663666820593849254163877 874437528861346735155727)
                    ·
                      rfl

theorem cell23_5108883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 1, 4].length) (baseStart_5108883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108883 prefixEnd_5108883 := by exact prefixLift 5108883
  have htrace : WordTrace (prefixWord ++ tailWord_5108883) baseStart_5108883 baseEnd_5108883 := by
    simpa [prefixWord, tailWord_5108883, baseEnd_5108883] using wordTrace_append hprefix tailTrace_5108883
  have hstable : (prefixWord ++ tailWord_5108883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108883).length < 2 ^ (prefixWord ++ tailWord_5108883).sum := by decide
  have hdescent : baseEnd_5108883 < baseStart_5108883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5108997 : List Nat := [1, 3, 1, 1, 2, 1, 7, 2, 1, 2, 2]
def baseStart_5108997 : Nat := 118140960795 + 5108997 * 2 ^ 59
def prefixEnd_5108997 : Nat := 4983230072969 + 3 ^ 40 * 5108997 * 2
def baseEnd_5108997 : Nat := 2623371123378652759441657

theorem tailTrace_5108997 : CollatzResearch.WordTrace tailWord_5108997 prefixEnd_5108997 2623371123378652759441657 := by
  unfold tailWord_5108997
  simp only [CollatzResearch.WordTrace]
  refine ⟨186340429071983891065677245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124226952714655927377118163 186340429071983891065677245)
  ·
    refine ⟨69877660901993959149628967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186340429071983891065677245 69877660901993959149628967)
    ·
      refine ⟨104816491352990938724443451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69877660901993959149628967 104816491352990938724443451)
      ·
        refine ⟨157224737029486408086665177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104816491352990938724443451 157224737029486408086665177)
        ·
          refine ⟨117918552772114806064998883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157224737029486408086665177 117918552772114806064998883)
          ·
            refine ⟨176877829158172209097498325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117918552772114806064998883 176877829158172209097498325)
            ·
              refine ⟨4145574120894661150722617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 176877829158172209097498325 4145574120894661150722617)
              ·
                refine ⟨3109180590670995863041963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4145574120894661150722617 3109180590670995863041963)
                ·
                  refine ⟨4663770886006493794562945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3109180590670995863041963 4663770886006493794562945)
                  ·
                    refine ⟨3497828164504870345922209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4663770886006493794562945 3497828164504870345922209)
                    ·
                      refine ⟨2623371123378652759441657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3497828164504870345922209 2623371123378652759441657)
                      ·
                        rfl

theorem cell23_5108997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 1, 2, 2].length) (baseStart_5108997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5108997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5108997 prefixEnd_5108997 := by exact prefixLift 5108997
  have htrace : WordTrace (prefixWord ++ tailWord_5108997) baseStart_5108997 baseEnd_5108997 := by
    simpa [prefixWord, tailWord_5108997, baseEnd_5108997] using wordTrace_append hprefix tailTrace_5108997
  have hstable : (prefixWord ++ tailWord_5108997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5108997).length < 2 ^ (prefixWord ++ tailWord_5108997).sum := by decide
  have hdescent : baseEnd_5108997 < baseStart_5108997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5108997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109040 : List Nat := [2, 1, 1, 1, 2, 2, 7, 1, 1, 3, 2]
def baseStart_5109040 : Nat := 118140960795 + 5109040 * 2 ^ 59
def prefixEnd_5109040 : Nat := 4983230072969 + 3 ^ 40 * 5109040 * 2
def baseEnd_5109040 : Nat := 2623393203046796091203959

theorem tailTrace_5109040 : CollatzResearch.WordTrace tailWord_5109040 prefixEnd_5109040 2623393203046796091203959 := by
  unfold tailWord_5109040
  simp only [CollatzResearch.WordTrace]
  refine ⟨93170998705414054704746287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124227998273885406272995049 93170998705414054704746287)
  ·
    refine ⟨139756498058121082057119431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93170998705414054704746287 139756498058121082057119431)
    ·
      refine ⟨209634747087181623085679147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139756498058121082057119431 209634747087181623085679147)
      ·
        refine ⟨314452120630772434628518721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209634747087181623085679147 314452120630772434628518721)
        ·
          refine ⟨235839090473079325971389041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314452120630772434628518721 235839090473079325971389041)
          ·
            refine ⟨176879317854809494478541781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235839090473079325971389041 176879317854809494478541781)
            ·
              refine ⟨4145609012222097526840823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 176879317854809494478541781 4145609012222097526840823)
              ·
                refine ⟨6218413518333146290261235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4145609012222097526840823 6218413518333146290261235)
                ·
                  refine ⟨9327620277499719435391853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6218413518333146290261235 9327620277499719435391853)
                  ·
                    refine ⟨3497857604062394788271945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9327620277499719435391853 3497857604062394788271945)
                    ·
                      refine ⟨2623393203046796091203959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3497857604062394788271945 2623393203046796091203959)
                      ·
                        rfl

theorem cell23_5109040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 1, 3, 2].length) (baseStart_5109040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109040 prefixEnd_5109040 := by exact prefixLift 5109040
  have htrace : WordTrace (prefixWord ++ tailWord_5109040) baseStart_5109040 baseEnd_5109040 := by
    simpa [prefixWord, tailWord_5109040, baseEnd_5109040] using wordTrace_append hprefix tailTrace_5109040
  have hstable : (prefixWord ++ tailWord_5109040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109040).length < 2 ^ (prefixWord ++ tailWord_5109040).sum := by decide
  have hdescent : baseEnd_5109040 < baseStart_5109040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109059 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 7]
def baseStart_5109059 : Nat := 118140960795 + 5109059 * 2 ^ 59
def prefixEnd_5109059 : Nat := 4983230072969 + 3 ^ 40 * 5109059 * 2
def baseEnd_5109059 : Nat := 291489217686581279651819

theorem tailTrace_5109059 : CollatzResearch.WordTrace tailWord_5109059 prefixEnd_5109059 291489217686581279651819 := by
  unfold tailWord_5109059
  simp only [CollatzResearch.WordTrace]
  refine ⟨186342690397759275654434231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124228460265172850436289487 186342690397759275654434231)
  ·
    refine ⟨279514035596638913481651347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186342690397759275654434231 279514035596638913481651347)
    ·
      refine ⟨419271053394958370222477021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279514035596638913481651347 419271053394958370222477021)
      ·
        refine ⟨157226645023109388833428883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 419271053394958370222477021 157226645023109388833428883)
        ·
          refine ⟨235839967534664083250143325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157226645023109388833428883 235839967534664083250143325)
          ·
            refine ⟨88439987825499031218803747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235839967534664083250143325 88439987825499031218803747)
            ·
              refine ⟨132659981738248546828205621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88439987825499031218803747 132659981738248546828205621)
              ·
                refine ⟨12436873287960801265144277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132659981738248546828205621 12436873287960801265144277)
                ·
                  refine ⟨291489217686581279651819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12436873287960801265144277 291489217686581279651819)
                  ·
                    rfl

theorem cell23_5109059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 7].length) (baseStart_5109059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109059 prefixEnd_5109059 := by exact prefixLift 5109059
  have htrace : WordTrace (prefixWord ++ tailWord_5109059) baseStart_5109059 baseEnd_5109059 := by
    simpa [prefixWord, tailWord_5109059, baseEnd_5109059] using wordTrace_append hprefix tailTrace_5109059
  have hstable : (prefixWord ++ tailWord_5109059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109059).length < 2 ^ (prefixWord ++ tailWord_5109059).sum := by decide
  have hdescent : baseEnd_5109059 < baseStart_5109059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109070 : List Nat := [4, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2]
def baseStart_5109070 : Nat := 118140960795 + 5109070 * 2 ^ 59
def prefixEnd_5109070 : Nat := 4983230072969 + 3 ^ 40 * 5109070 * 2
def baseEnd_5109070 : Nat := 2623408607466430973828821

theorem tailTrace_5109070 : CollatzResearch.WordTrace tailWord_5109070 prefixEnd_5109070 2623408607466430973828821 := by
  unfold tailWord_5109070
  simp only [CollatzResearch.WordTrace]
  refine ⟨23292886450089928066635583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124228727733812949688723109 23292886450089928066635583)
  ·
    refine ⟨34939329675134892099953375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23292886450089928066635583 34939329675134892099953375)
    ·
      refine ⟨52408994512702338149930063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34939329675134892099953375 52408994512702338149930063)
      ·
        refine ⟨78613491769053507224895095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52408994512702338149930063 78613491769053507224895095)
        ·
          refine ⟨117920237653580260837342643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78613491769053507224895095 117920237653580260837342643)
          ·
            refine ⟨176880356480370391256013965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117920237653580260837342643 176880356480370391256013965)
            ·
              refine ⟨66330133680138896721005237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176880356480370391256013965 66330133680138896721005237)
              ·
                refine ⟨6218450032513021567594241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66330133680138896721005237 6218450032513021567594241)
                ·
                  refine ⟨4663837524384766175695681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6218450032513021567594241 4663837524384766175695681)
                  ·
                    refine ⟨3497878143288574631771761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4663837524384766175695681 3497878143288574631771761)
                    ·
                      refine ⟨2623408607466430973828821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3497878143288574631771761 2623408607466430973828821)
                      ·
                        rfl

theorem cell23_5109070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_5109070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109070 prefixEnd_5109070 := by exact prefixLift 5109070
  have htrace : WordTrace (prefixWord ++ tailWord_5109070) baseStart_5109070 baseEnd_5109070 := by
    simpa [prefixWord, tailWord_5109070, baseEnd_5109070] using wordTrace_append hprefix tailTrace_5109070
  have hstable : (prefixWord ++ tailWord_5109070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109070).length < 2 ^ (prefixWord ++ tailWord_5109070).sum := by decide
  have hdescent : baseEnd_5109070 < baseStart_5109070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109076 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 7]
def baseStart_5109076 : Nat := 118140960795 + 5109076 * 2 ^ 59
def prefixEnd_5109076 : Nat := 4983230072969 + 3 ^ 40 * 5109076 * 2
def baseEnd_5109076 : Nat := 291490187594484216705977

theorem tailTrace_5109076 : CollatzResearch.WordTrace tailWord_5109076 prefixEnd_5109076 291490187594484216705977 := by
  unfold tailWord_5109076
  simp only [CollatzResearch.WordTrace]
  refine ⟨93171655219348843778901541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124228873625798458371868721 93171655219348843778901541)
  ·
    refine ⟨17469685353627908208544039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93171655219348843778901541 17469685353627908208544039)
    ·
      refine ⟨26204528030441862312816059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17469685353627908208544039 26204528030441862312816059)
      ·
        refine ⟨39306792045662793469224089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26204528030441862312816059 39306792045662793469224089)
        ·
          refine ⟨29480094034247095101918067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39306792045662793469224089 29480094034247095101918067)
          ·
            refine ⟨44220141051370642652877101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29480094034247095101918067 44220141051370642652877101)
            ·
              refine ⟨16582552894263990994828913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44220141051370642652877101 16582552894263990994828913)
              ·
                refine ⟨12436914670697993246121685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16582552894263990994828913 12436914670697993246121685)
                ·
                  refine ⟨291490187594484216705977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12436914670697993246121685 291490187594484216705977)
                  ·
                    rfl

theorem cell23_5109076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_5109076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109076 prefixEnd_5109076 := by exact prefixLift 5109076
  have htrace : WordTrace (prefixWord ++ tailWord_5109076) baseStart_5109076 baseEnd_5109076 := by
    simpa [prefixWord, tailWord_5109076, baseEnd_5109076] using wordTrace_append hprefix tailTrace_5109076
  have hstable : (prefixWord ++ tailWord_5109076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109076).length < 2 ^ (prefixWord ++ tailWord_5109076).sum := by decide
  have hdescent : baseEnd_5109076 < baseStart_5109076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109093 : List Nat := [1, 3, 1, 3, 1, 2, 4, 3, 5]
def baseStart_5109093 : Nat := 118140960795 + 5109093 * 2 ^ 59
def prefixEnd_5109093 : Nat := 4983230072969 + 3 ^ 40 * 5109093 * 2
def baseEnd_5109093 : Nat := 291491157502387153760135

theorem tailTrace_5109093 : CollatzResearch.WordTrace tailWord_5109093 prefixEnd_5109093 291491157502387153760135 := by
  unfold tailWord_5109093
  simp only [CollatzResearch.WordTrace]
  refine ⟨186343930479636099461171933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124229286986424066307447955 186343930479636099461171933)
  ·
    refine ⟨69878973929863537297939475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186343930479636099461171933 69878973929863537297939475)
    ·
      refine ⟨104818460894795305946909213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69878973929863537297939475 104818460894795305946909213)
      ·
        refine ⟨39306922835548239730090955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104818460894795305946909213 39306922835548239730090955)
        ·
          refine ⟨58960384253322359595136433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39306922835548239730090955 58960384253322359595136433)
          ·
            refine ⟨44220288189991769696352325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58960384253322359595136433 44220288189991769696352325)
            ·
              refine ⟨8291304035623456818066061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44220288189991769696352325 8291304035623456818066061)
              ·
                refine ⟨3109239013358796306774773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8291304035623456818066061 3109239013358796306774773)
                ·
                  refine ⟨291491157502387153760135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3109239013358796306774773 291491157502387153760135)
                  ·
                    rfl

theorem cell23_5109093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_5109093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109093 prefixEnd_5109093 := by exact prefixLift 5109093
  have htrace : WordTrace (prefixWord ++ tailWord_5109093) baseStart_5109093 baseEnd_5109093 := by
    simpa [prefixWord, tailWord_5109093, baseEnd_5109093] using wordTrace_append hprefix tailTrace_5109093
  have hstable : (prefixWord ++ tailWord_5109093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109093).length < 2 ^ (prefixWord ++ tailWord_5109093).sum := by decide
  have hdescent : baseEnd_5109093 < baseStart_5109093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109106 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_5109106 : Nat := 118140960795 + 5109106 * 2 ^ 59
def prefixEnd_5109106 : Nat := 4983230072969 + 3 ^ 40 * 5109106 * 2
def baseEnd_5109106 : Nat := 874475697589997610992885

theorem tailTrace_5109106 : CollatzResearch.WordTrace tailWord_5109106 prefixEnd_5109106 874475697589997610992885 := by
  unfold tailWord_5109106
  simp only [CollatzResearch.WordTrace]
  refine ⟨46586101157147250670348793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124229603085726001787596781 46586101157147250670348793)
  ·
    refine ⟨34939575867860438002761595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46586101157147250670348793 34939575867860438002761595)
    ·
      refine ⟨52409363801790657004142393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34939575867860438002761595 52409363801790657004142393)
      ·
        refine ⟨39307022851342992753106795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52409363801790657004142393 39307022851342992753106795)
        ·
          refine ⟨58960534277014489129660193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39307022851342992753106795 58960534277014489129660193)
          ·
            refine ⟨44220400707760866847245145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58960534277014489129660193 44220400707760866847245145)
            ·
              refine ⟨33165300530820650135433859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44220400707760866847245145 33165300530820650135433859)
              ·
                refine ⟨49747950796230975203150789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33165300530820650135433859 49747950796230975203150789)
                ·
                  refine ⟨9327740774293307850590773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49747950796230975203150789 9327740774293307850590773)
                  ·
                    refine ⟨874475697589997610992885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9327740774293307850590773 874475697589997610992885)
                    ·
                      rfl

theorem cell23_5109106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_5109106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109106 prefixEnd_5109106 := by exact prefixLift 5109106
  have htrace : WordTrace (prefixWord ++ tailWord_5109106) baseStart_5109106 baseEnd_5109106 := by
    simpa [prefixWord, tailWord_5109106, baseEnd_5109106] using wordTrace_append hprefix tailTrace_5109106
  have hstable : (prefixWord ++ tailWord_5109106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109106).length < 2 ^ (prefixWord ++ tailWord_5109106).sum := by decide
  have hdescent : baseEnd_5109106 < baseStart_5109106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109119 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 4, 8]
def baseStart_5109119 : Nat := 118140960795 + 5109119 * 2 ^ 59
def prefixEnd_5109119 : Nat := 4983230072969 + 3 ^ 40 * 5109119 * 2
def baseEnd_5109119 : Nat := 874477922672833760705365

theorem tailTrace_5109119 : CollatzResearch.WordTrace tailWord_5109119 prefixEnd_5109119 874477922672833760705365 := by
  unfold tailWord_5109119
  simp only [CollatzResearch.WordTrace]
  refine ⟨186344878777541905901618411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124229919185027937267745607 186344878777541905901618411)
  ·
    refine ⟨279517318166312858852427617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186344878777541905901618411 279517318166312858852427617)
    ·
      refine ⟨209637988624734644139320713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279517318166312858852427617 209637988624734644139320713)
      ·
        refine ⟨157228491468550983104490535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209637988624734644139320713 157228491468550983104490535)
        ·
          refine ⟨235842737202826474656735803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157228491468550983104490535 235842737202826474656735803)
          ·
            refine ⟨353764105804239711985103705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235842737202826474656735803 353764105804239711985103705)
            ·
              refine ⟨265323079353179783988827779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353764105804239711985103705 265323079353179783988827779)
              ·
                refine ⟨397984619029769675983241669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265323079353179783988827779 397984619029769675983241669)
                ·
                  refine ⟨74622116068081814246857813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 397984619029769675983241669 74622116068081814246857813)
                  ·
                    refine ⟨874477922672833760705365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74622116068081814246857813 874477922672833760705365)
                    ·
                      rfl

theorem cell23_5109119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_5109119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109119 prefixEnd_5109119 := by exact prefixLift 5109119
  have htrace : WordTrace (prefixWord ++ tailWord_5109119) baseStart_5109119 baseEnd_5109119 := by
    simpa [prefixWord, tailWord_5109119, baseEnd_5109119] using wordTrace_append hprefix tailTrace_5109119
  have hstable : (prefixWord ++ tailWord_5109119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109119).length < 2 ^ (prefixWord ++ tailWord_5109119).sum := by decide
  have hdescent : baseEnd_5109119 < baseStart_5109119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109193 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 5, 1, 3]
def baseStart_5109193 : Nat := 118140960795 + 5109193 * 2 ^ 59
def prefixEnd_5109193 : Nat := 4983230072969 + 3 ^ 40 * 5109193 * 2
def baseEnd_5109193 : Nat := 2623471765586933992590755

theorem tailTrace_5109193 : CollatzResearch.WordTrace tailWord_5109193 prefixEnd_5109193 2623471765586933992590755 := by
  unfold tailWord_5109193
  simp only [CollatzResearch.WordTrace]
  refine ⟨186347577779273816539812233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124231718519515877693208155 186347577779273816539812233)
  ·
    refine ⟨139760683334455362404859175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186347577779273816539812233 139760683334455362404859175)
    ·
      refine ⟨209641025001683043607288763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139760683334455362404859175 209641025001683043607288763)
      ·
        refine ⟨314461537502524565410933145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209641025001683043607288763 314461537502524565410933145)
        ·
          refine ⟨235846153126893424058199859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314461537502524565410933145 235846153126893424058199859)
          ·
            refine ⟨353769229690340136087299789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235846153126893424058199859 353769229690340136087299789)
            ·
              refine ⟨132663461133877551032737421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 353769229690340136087299789 132663461133877551032737421)
              ·
                refine ⟨49748797925204081637276533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132663461133877551032737421 49748797925204081637276533)
                ·
                  refine ⟨4663949805487882653494675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49748797925204081637276533 4663949805487882653494675)
                  ·
                    refine ⟨6995924708231823980242013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4663949805487882653494675 6995924708231823980242013)
                    ·
                      refine ⟨2623471765586933992590755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6995924708231823980242013 2623471765586933992590755)
                      ·
                        rfl

theorem cell23_5109193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 1, 3].length) (baseStart_5109193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109193 prefixEnd_5109193 := by exact prefixLift 5109193
  have htrace : WordTrace (prefixWord ++ tailWord_5109193) baseStart_5109193 baseEnd_5109193 := by
    simpa [prefixWord, tailWord_5109193, baseEnd_5109193] using wordTrace_append hprefix tailTrace_5109193
  have hstable : (prefixWord ++ tailWord_5109193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109193).length < 2 ^ (prefixWord ++ tailWord_5109193).sum := by decide
  have hdescent : baseEnd_5109193 < baseStart_5109193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109233 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_5109233 : Nat := 118140960795 + 5109233 * 2 ^ 59
def prefixEnd_5109233 : Nat := 4983230072969 + 3 ^ 40 * 5109233 * 2
def baseEnd_5109233 : Nat := 2623492304813113836090571

theorem tailTrace_5109233 : CollatzResearch.WordTrace tailWord_5109233 prefixEnd_5109233 2623492304813113836090571 := by
  unfold tailWord_5109233
  simp only [CollatzResearch.WordTrace]
  refine ⟨186349036699128903371268353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124232691132752602247512235 186349036699128903371268353)
  ·
    refine ⟨139761777524346677528451265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186349036699128903371268353 139761777524346677528451265)
    ·
      refine ⟨104821333143260008146338449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139761777524346677528451265 104821333143260008146338449)
      ·
        refine ⟨78615999857445006109753837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104821333143260008146338449 78615999857445006109753837)
        ·
          refine ⟨29480999946541877291157689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78615999857445006109753837 29480999946541877291157689)
          ·
            refine ⟨22110749959906407968368267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29480999946541877291157689 22110749959906407968368267)
            ·
              refine ⟨33166124939859611952552401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22110749959906407968368267 33166124939859611952552401)
              ·
                refine ⟨24874593704894708964414301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33166124939859611952552401 24874593704894708964414301)
                ·
                  refine ⟨9327972639335515861655363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24874593704894708964414301 9327972639335515861655363)
                  ·
                    refine ⟨13991958959003273792483045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9327972639335515861655363 13991958959003273792483045)
                    ·
                      refine ⟨2623492304813113836090571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13991958959003273792483045 2623492304813113836090571)
                      ·
                        rfl

theorem cell23_5109233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_5109233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109233 prefixEnd_5109233 := by exact prefixLift 5109233
  have htrace : WordTrace (prefixWord ++ tailWord_5109233) baseStart_5109233 baseEnd_5109233 := by
    simpa [prefixWord, tailWord_5109233, baseEnd_5109233] using wordTrace_append hprefix tailTrace_5109233
  have hstable : (prefixWord ++ tailWord_5109233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109233).length < 2 ^ (prefixWord ++ tailWord_5109233).sum := by decide
  have hdescent : baseEnd_5109233 < baseStart_5109233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109256 : List Nat := [2, 1, 3, 2, 1, 1, 2, 11]
def baseStart_5109256 : Nat := 118140960795 + 5109256 * 2 ^ 59
def prefixEnd_5109256 : Nat := 4983230072969 + 3 ^ 40 * 5109256 * 2
def baseEnd_5109256 : Nat := 97166819069191379485295

theorem tailTrace_5109256 : CollatzResearch.WordTrace tailWord_5109256 prefixEnd_5109256 97166819069191379485295 := by
  unfold tailWord_5109256
  simp only [CollatzResearch.WordTrace]
  refine ⟨93174937789022789149677811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124233250385363718866237081 93174937789022789149677811)
  ·
    refine ⟨139762406683534183724516717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93174937789022789149677811 139762406683534183724516717)
    ·
      refine ⟨52410902506325318896693769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139762406683534183724516717 52410902506325318896693769)
      ·
        refine ⟨39308176879743989172520327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52410902506325318896693769 39308176879743989172520327)
        ·
          refine ⟨58962265319615983758780491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39308176879743989172520327 58962265319615983758780491)
          ·
            refine ⟨88443397979423975638170737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58962265319615983758780491 88443397979423975638170737)
            ·
              refine ⟨66332548484567981728628053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88443397979423975638170737 66332548484567981728628053)
              ·
                refine ⟨97166819069191379485295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 66332548484567981728628053 97166819069191379485295)
                ·
                  rfl

theorem cell23_5109256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 11].length) (baseStart_5109256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109256 prefixEnd_5109256 := by exact prefixLift 5109256
  have htrace : WordTrace (prefixWord ++ tailWord_5109256) baseStart_5109256 baseEnd_5109256 := by
    simpa [prefixWord, tailWord_5109256, baseEnd_5109256] using wordTrace_append hprefix tailTrace_5109256
  have hstable : (prefixWord ++ tailWord_5109256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109256).length < 2 ^ (prefixWord ++ tailWord_5109256).sum := by decide
  have hdescent : baseEnd_5109256 < baseStart_5109256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109267 : List Nat := [1, 1, 1, 2, 1, 8, 2, 1, 1, 1, 4]
def baseStart_5109267 : Nat := 118140960795 + 5109267 * 2 ^ 59
def prefixEnd_5109267 : Nat := 4983230072969 + 3 ^ 40 * 5109267 * 2
def baseEnd_5109267 : Nat := 2623509763155366703065415

theorem tailTrace_5109267 : CollatzResearch.WordTrace tailWord_5109267 prefixEnd_5109267 2623509763155366703065415 := by
  unfold tailWord_5109267
  simp only [CollatzResearch.WordTrace]
  refine ⟨186350276781005727178006055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124233517854003818118670703 186350276781005727178006055)
  ·
    refine ⟨279525415171508590767009083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186350276781005727178006055 279525415171508590767009083)
    ·
      refine ⟨419288122757262886150513625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279525415171508590767009083 419288122757262886150513625)
      ·
        refine ⟨314466092067947164612885219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419288122757262886150513625 314466092067947164612885219)
        ·
          refine ⟨471699138101920746919327829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314466092067947164612885219 471699138101920746919327829)
          ·
            refine ⟨5527724274631883752960873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 471699138101920746919327829 5527724274631883752960873)
            ·
              refine ⟨4145793205973912814720655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5527724274631883752960873 4145793205973912814720655)
              ·
                refine ⟨6218689808960869222080983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4145793205973912814720655 6218689808960869222080983)
                ·
                  refine ⟨9328034713441303833121475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6218689808960869222080983 9328034713441303833121475)
                  ·
                    refine ⟨13992052070161955749682213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9328034713441303833121475 13992052070161955749682213)
                    ·
                      refine ⟨2623509763155366703065415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13992052070161955749682213 2623509763155366703065415)
                      ·
                        rfl

theorem cell23_5109267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 1, 4].length) (baseStart_5109267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109267 prefixEnd_5109267 := by exact prefixLift 5109267
  have htrace : WordTrace (prefixWord ++ tailWord_5109267) baseStart_5109267 baseEnd_5109267 := by
    simpa [prefixWord, tailWord_5109267, baseEnd_5109267] using wordTrace_append hprefix tailTrace_5109267
  have hstable : (prefixWord ++ tailWord_5109267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109267).length < 2 ^ (prefixWord ++ tailWord_5109267).sum := by decide
  have hdescent : baseEnd_5109267 < baseStart_5109267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109278 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_5109278 : Nat := 118140960795 + 5109278 * 2 ^ 59
def prefixEnd_5109278 : Nat := 4983230072969 + 3 ^ 40 * 5109278 * 2
def baseEnd_5109278 : Nat := 2623515411442566160027865

theorem tailTrace_5109278 : CollatzResearch.WordTrace tailWord_5109278 prefixEnd_5109278 2623515411442566160027865 := by
  unfold tailWord_5109278
  simp only [CollatzResearch.WordTrace]
  refine ⟨23293834747995734507082061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124233785322643917371104325 23293834747995734507082061)
  ·
    refine ⟨8735188030498400440155773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23293834747995734507082061 8735188030498400440155773)
    ·
      refine ⟨3275695511436900165058415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8735188030498400440155773 3275695511436900165058415)
      ·
        refine ⟨4913543267155350247587623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3275695511436900165058415 4913543267155350247587623)
        ·
          refine ⟨7370314900733025371381435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4913543267155350247587623 7370314900733025371381435)
          ·
            refine ⟨11055472351099538057072153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7370314900733025371381435 11055472351099538057072153)
            ·
              refine ⟨8291604263324653542804115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11055472351099538057072153 8291604263324653542804115)
              ·
                refine ⟨12437406394986980314206173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8291604263324653542804115 12437406394986980314206173)
                ·
                  refine ⟨4664027398120117617827315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12437406394986980314206173 4664027398120117617827315)
                  ·
                    refine ⟨6996041097180176426740973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4664027398120117617827315 6996041097180176426740973)
                    ·
                      refine ⟨2623515411442566160027865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6996041097180176426740973 2623515411442566160027865)
                      ·
                        rfl

theorem cell23_5109278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_5109278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109278 prefixEnd_5109278 := by exact prefixLift 5109278
  have htrace : WordTrace (prefixWord ++ tailWord_5109278) baseStart_5109278 baseEnd_5109278 := by
    simpa [prefixWord, tailWord_5109278, baseEnd_5109278] using wordTrace_append hprefix tailTrace_5109278
  have hstable : (prefixWord ++ tailWord_5109278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109278).length < 2 ^ (prefixWord ++ tailWord_5109278).sum := by decide
  have hdescent : baseEnd_5109278 < baseStart_5109278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109294 : List Nat := [4, 1, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_5109294 : Nat := 118140960795 + 5109294 * 2 ^ 59
def prefixEnd_5109294 : Nat := 4983230072969 + 3 ^ 40 * 5109294 * 2
def baseEnd_5109294 : Nat := 874507875711012699142597

theorem tailTrace_5109294 : CollatzResearch.WordTrace tailWord_5109294 prefixEnd_5109294 874507875711012699142597 := by
  unfold tailWord_5109294
  simp only [CollatzResearch.WordTrace]
  refine ⟨23293907693988488848654867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124234174367938607192825957 23293907693988488848654867)
  ·
    refine ⟨34940861540982733272982301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23293907693988488848654867 34940861540982733272982301)
    ·
      refine ⟨13102823077868524977368363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34940861540982733272982301 13102823077868524977368363)
      ·
        refine ⟨19654234616802787466052545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13102823077868524977368363 19654234616802787466052545)
        ·
          refine ⟨14740675962602090599539409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19654234616802787466052545 14740675962602090599539409)
          ·
            refine ⟨11055506971951567949654557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14740675962602090599539409 11055506971951567949654557)
            ·
              refine ⟨4145815114481837981120459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11055506971951567949654557 4145815114481837981120459)
              ·
                refine ⟨6218722671722756971680689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4145815114481837981120459 6218722671722756971680689)
                ·
                  refine ⟨4664042003792067728760517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6218722671722756971680689 4664042003792067728760517)
                  ·
                    refine ⟨874507875711012699142597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4664042003792067728760517 874507875711012699142597)
                    ·
                      rfl

theorem cell23_5109294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_5109294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109294 prefixEnd_5109294 := by exact prefixLift 5109294
  have htrace : WordTrace (prefixWord ++ tailWord_5109294) baseStart_5109294 baseEnd_5109294 := by
    simpa [prefixWord, tailWord_5109294, baseEnd_5109294] using wordTrace_append hprefix tailTrace_5109294
  have hstable : (prefixWord ++ tailWord_5109294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109294).length < 2 ^ (prefixWord ++ tailWord_5109294).sum := by decide
  have hdescent : baseEnd_5109294 < baseStart_5109294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109313 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_5109313 : Nat := 118140960795 + 5109313 * 2 ^ 59
def prefixEnd_5109313 : Nat := 4983230072969 + 3 ^ 40 * 5109313 * 2
def baseEnd_5109313 : Nat := 2623533383265473523090203

theorem tailTrace_5109313 : CollatzResearch.WordTrace tailWord_5109313 prefixEnd_5109313 2623533383265473523090203 := by
  unfold tailWord_5109313
  simp only [CollatzResearch.WordTrace]
  refine ⟨186351954538839077034180593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124234636359226051356120395 186351954538839077034180593)
  ·
    refine ⟨139763965904129307775635445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186351954538839077034180593 139763965904129307775635445)
    ·
      refine ⟨13102871803512122603965823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139763965904129307775635445 13102871803512122603965823)
      ·
        refine ⟨19654307705268183905948735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13102871803512122603965823 19654307705268183905948735)
        ·
          refine ⟨29481461557902275858923103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19654307705268183905948735 29481461557902275858923103)
          ·
            refine ⟨44222192336853413788384655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29481461557902275858923103 44222192336853413788384655)
            ·
              refine ⟨66333288505280120682576983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44222192336853413788384655 66333288505280120682576983)
              ·
                refine ⟨99499932757920181023865475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66333288505280120682576983 99499932757920181023865475)
                ·
                  refine ⟨149249899136880271535798213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99499932757920181023865475 149249899136880271535798213)
                  ·
                    refine ⟨27984356088165050912962165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149249899136880271535798213 27984356088165050912962165)
                    ·
                      refine ⟨2623533383265473523090203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27984356088165050912962165 2623533383265473523090203)
                      ·
                        rfl

theorem cell23_5109313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_5109313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109313 prefixEnd_5109313 := by exact prefixLift 5109313
  have htrace : WordTrace (prefixWord ++ tailWord_5109313) baseStart_5109313 baseEnd_5109313 := by
    simpa [prefixWord, tailWord_5109313, baseEnd_5109313] using wordTrace_append hprefix tailTrace_5109313
  have hstable : (prefixWord ++ tailWord_5109313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109313).length < 2 ^ (prefixWord ++ tailWord_5109313).sum := by decide
  have hdescent : baseEnd_5109313 < baseStart_5109313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109353 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 2, 2, 4]
def baseStart_5109353 : Nat := 118140960795 + 5109353 * 2 ^ 59
def prefixEnd_5109353 : Nat := 4983230072969 + 3 ^ 40 * 5109353 * 2
def baseEnd_5109353 : Nat := 2623553922491653366590019

theorem tailTrace_5109353 : CollatzResearch.WordTrace tailWord_5109353 prefixEnd_5109353 2623553922491653366590019 := by
  unfold tailWord_5109353
  simp only [CollatzResearch.WordTrace]
  refine ⟨186353413458694163865636713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124235608972462775910424475 186353413458694163865636713)
  ·
    refine ⟨139765060094020622899227535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186353413458694163865636713 139765060094020622899227535)
    ·
      refine ⟨209647590141030934348841303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139765060094020622899227535 209647590141030934348841303)
      ·
        refine ⟨314471385211546401523261955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209647590141030934348841303 314471385211546401523261955)
        ·
          refine ⟨471707077817319602284892933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314471385211546401523261955 471707077817319602284892933)
          ·
            refine ⟨88445077090747425428417425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 471707077817319602284892933 88445077090747425428417425)
            ·
              refine ⟨66333807818060569071313069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88445077090747425428417425 66333807818060569071313069)
              ·
                refine ⟨24875177931772713401742401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66333807818060569071313069 24875177931772713401742401)
                ·
                  refine ⟨18656383448829535051306801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24875177931772713401742401 18656383448829535051306801)
                  ·
                    refine ⟨13992287586622151288480101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18656383448829535051306801 13992287586622151288480101)
                    ·
                      refine ⟨2623553922491653366590019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13992287586622151288480101 2623553922491653366590019)
                      ·
                        rfl

theorem cell23_5109353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_5109353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109353 prefixEnd_5109353 := by exact prefixLift 5109353
  have htrace : WordTrace (prefixWord ++ tailWord_5109353) baseStart_5109353 baseEnd_5109353 := by
    simpa [prefixWord, tailWord_5109353, baseEnd_5109353] using wordTrace_append hprefix tailTrace_5109353
  have hstable : (prefixWord ++ tailWord_5109353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109353).length < 2 ^ (prefixWord ++ tailWord_5109353).sum := by decide
  have hdescent : baseEnd_5109353 < baseStart_5109353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109393 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 4, 5]
def baseStart_5109393 : Nat := 118140960795 + 5109393 * 2 ^ 59
def prefixEnd_5109393 : Nat := 4983230072969 + 3 ^ 40 * 5109393 * 2
def baseEnd_5109393 : Nat := 874524820572611070029945

theorem tailTrace_5109393 : CollatzResearch.WordTrace tailWord_5109393 prefixEnd_5109393 874524820572611070029945 := by
  unfold tailWord_5109393
  simp only [CollatzResearch.WordTrace]
  refine ⟨186354872378549250697092833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124236581585699500464728555 186354872378549250697092833)
  ·
    refine ⟨139766154283911938022819625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186354872378549250697092833 139766154283911938022819625)
    ·
      refine ⟨104824615712933953517114719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139766154283911938022819625 104824615712933953517114719)
      ·
        refine ⟨157236923569400930275672079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104824615712933953517114719 157236923569400930275672079)
        ·
          refine ⟨235855385354101395413508119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157236923569400930275672079 235855385354101395413508119)
          ·
            refine ⟨353783078031152093120262179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235855385354101395413508119 353783078031152093120262179)
            ·
              refine ⟨530674617046728139680393269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353783078031152093120262179 530674617046728139680393269)
              ·
                refine ⟨49750745348130763095036869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 530674617046728139680393269 49750745348130763095036869)
                ·
                  refine ⟨9328264752774518080319413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49750745348130763095036869 9328264752774518080319413)
                  ·
                    refine ⟨874524820572611070029945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9328264752774518080319413 874524820572611070029945)
                    ·
                      rfl

theorem cell23_5109393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_5109393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109393 prefixEnd_5109393 := by exact prefixLift 5109393
  have htrace : WordTrace (prefixWord ++ tailWord_5109393) baseStart_5109393 baseEnd_5109393 := by
    simpa [prefixWord, tailWord_5109393, baseEnd_5109393] using wordTrace_append hprefix tailTrace_5109393
  have hstable : (prefixWord ++ tailWord_5109393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109393).length < 2 ^ (prefixWord ++ tailWord_5109393).sum := by decide
  have hdescent : baseEnd_5109393 < baseStart_5109393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109440 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 5, 4]
def baseStart_5109440 : Nat := 118140960795 + 5109440 * 2 ^ 59
def prefixEnd_5109440 : Nat := 4983230072969 + 3 ^ 40 * 5109440 * 2
def baseEnd_5109440 : Nat := 874532865102864842067373

theorem tailTrace_5109440 : CollatzResearch.WordTrace tailWord_5109440 prefixEnd_5109440 874532865102864842067373 := by
  unfold tailWord_5109440
  simp only [CollatzResearch.WordTrace]
  refine ⟨93178293304689488862026887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124237724406252651816035849 93178293304689488862026887)
  ·
    refine ⟨139767439957034233293040331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93178293304689488862026887 139767439957034233293040331)
    ·
      refine ⟨209651159935551349939560497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139767439957034233293040331 209651159935551349939560497)
      ·
        refine ⟨157238369951663512454670373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209651159935551349939560497 157238369951663512454670373)
        ·
          refine ⟨29482194365936908585250695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157238369951663512454670373 29482194365936908585250695)
          ·
            refine ⟨44223291548905362877876043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29482194365936908585250695 44223291548905362877876043)
            ·
              refine ⟨66334937323358044316814065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44223291548905362877876043 66334937323358044316814065)
              ·
                refine ⟨49751202992518533237610549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66334937323358044316814065 49751202992518533237610549)
                ·
                  refine ⟨4664175280548612491025989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49751202992518533237610549 4664175280548612491025989)
                  ·
                    refine ⟨874532865102864842067373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4664175280548612491025989 874532865102864842067373)
                    ·
                      rfl

theorem cell23_5109440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 5, 4].length) (baseStart_5109440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109440 prefixEnd_5109440 := by exact prefixLift 5109440
  have htrace : WordTrace (prefixWord ++ tailWord_5109440) baseStart_5109440 baseEnd_5109440 := by
    simpa [prefixWord, tailWord_5109440, baseEnd_5109440] using wordTrace_append hprefix tailTrace_5109440
  have hstable : (prefixWord ++ tailWord_5109440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109440).length < 2 ^ (prefixWord ++ tailWord_5109440).sum := by decide
  have hdescent : baseEnd_5109440 < baseStart_5109440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109442 : List Nat := [3, 5, 1, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_5109442 : Nat := 118140960795 + 5109442 * 2 ^ 59
def prefixEnd_5109442 : Nat := 4983230072969 + 3 ^ 40 * 5109442 * 2
def baseEnd_5109442 : Nat := 2623599622269903518377111

theorem tailTrace_5109442 : CollatzResearch.WordTrace tailWord_5109442 prefixEnd_5109442 2623599622269903518377111 := by
  unfold tailWord_5109442
  simp only [CollatzResearch.WordTrace]
  refine ⟨46589164888842933016406645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124237773036914488043751053 46589164888842933016406645)
  ·
    refine ⟨4367734208329024970288123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46589164888842933016406645 4367734208329024970288123)
    ·
      refine ⟨6551601312493537455432185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4367734208329024970288123 6551601312493537455432185)
      ·
        refine ⟨4913700984370153091574139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6551601312493537455432185 4913700984370153091574139)
        ·
          refine ⟨7370551476555229637361209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4913700984370153091574139 7370551476555229637361209)
          ·
            refine ⟨5527913607416422228020907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7370551476555229637361209 5527913607416422228020907)
            ·
              refine ⟨8291870411124633342031361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5527913607416422228020907 8291870411124633342031361)
              ·
                refine ⟨6218902808343475006523521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8291870411124633342031361 6218902808343475006523521)
                ·
                  refine ⟨4664177106257606254892641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6218902808343475006523521 4664177106257606254892641)
                  ·
                    refine ⟨3498132829693204691169481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4664177106257606254892641 3498132829693204691169481)
                    ·
                      refine ⟨2623599622269903518377111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3498132829693204691169481 2623599622269903518377111)
                      ·
                        rfl

theorem cell23_5109442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_5109442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109442 prefixEnd_5109442 := by exact prefixLift 5109442
  have htrace : WordTrace (prefixWord ++ tailWord_5109442) baseStart_5109442 baseEnd_5109442 := by
    simpa [prefixWord, tailWord_5109442, baseEnd_5109442] using wordTrace_append hprefix tailTrace_5109442
  have hstable : (prefixWord ++ tailWord_5109442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109442).length < 2 ^ (prefixWord ++ tailWord_5109442).sum := by decide
  have hdescent : baseEnd_5109442 < baseStart_5109442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109443 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 4]
def baseStart_5109443 : Nat := 118140960795 + 5109443 * 2 ^ 59
def prefixEnd_5109443 : Nat := 4983230072969 + 3 ^ 40 * 5109443 * 2
def baseEnd_5109443 : Nat := 2623600135750558014464605

theorem tailTrace_5109443 : CollatzResearch.WordTrace tailWord_5109443 prefixEnd_5109443 2623600135750558014464605 := by
  unfold tailWord_5109443
  simp only [CollatzResearch.WordTrace]
  refine ⟨186356696028368109236412983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124237797352245406157608655 186356696028368109236412983)
  ·
    refine ⟨279535044042552163854619475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186356696028368109236412983 279535044042552163854619475)
    ·
      refine ⟨419302566063828245781929213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279535044042552163854619475 419302566063828245781929213)
      ·
        refine ⟨157238462273935592168223455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 419302566063828245781929213 157238462273935592168223455)
        ·
          refine ⟨235857693410903388252335183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157238462273935592168223455 235857693410903388252335183)
          ·
            refine ⟨353786540116355082378502775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235857693410903388252335183 353786540116355082378502775)
            ·
              refine ⟨530679810174532623567754163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353786540116355082378502775 530679810174532623567754163)
              ·
                refine ⟨796019715261798935351631245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530679810174532623567754163 796019715261798935351631245)
                ·
                  refine ⟨298507393223174600756861717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796019715261798935351631245 298507393223174600756861717)
                  ·
                    refine ⟨13992534057336309410477893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 298507393223174600756861717 13992534057336309410477893)
                    ·
                      refine ⟨2623600135750558014464605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13992534057336309410477893 2623600135750558014464605)
                      ·
                        rfl

theorem cell23_5109443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_5109443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109443 prefixEnd_5109443 := by exact prefixLift 5109443
  have htrace : WordTrace (prefixWord ++ tailWord_5109443) baseStart_5109443 baseEnd_5109443 := by
    simpa [prefixWord, tailWord_5109443, baseEnd_5109443] using wordTrace_append hprefix tailTrace_5109443
  have hstable : (prefixWord ++ tailWord_5109443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109443).length < 2 ^ (prefixWord ++ tailWord_5109443).sum := by decide
  have hdescent : baseEnd_5109443 < baseStart_5109443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109457 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 3, 4]
def baseStart_5109457 : Nat := 118140960795 + 5109457 * 2 ^ 59
def prefixEnd_5109457 : Nat := 4983230072969 + 3 ^ 40 * 5109457 * 2
def baseEnd_5109457 : Nat := 874535774826573653229847

theorem tailTrace_5109457 : CollatzResearch.WordTrace tailWord_5109457 prefixEnd_5109457 874535774826573653229847 := by
  unfold tailWord_5109457
  simp only [CollatzResearch.WordTrace]
  refine ⟨186357206650317389627422625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124238137766878259751615083 186357206650317389627422625)
  ·
    refine ⟨139767904987738042220566969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186357206650317389627422625 139767904987738042220566969)
    ·
      refine ⟨104825928740803531665425227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139767904987738042220566969 104825928740803531665425227)
      ·
        refine ⟨157238893111205297498137841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104825928740803531665425227 157238893111205297498137841)
        ·
          refine ⟨117929169833403973123603381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157238893111205297498137841 117929169833403973123603381)
          ·
            refine ⟨11055859671881622480337817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117929169833403973123603381 11055859671881622480337817)
            ·
              refine ⟨8291894753911216860253363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11055859671881622480337817 8291894753911216860253363)
              ·
                refine ⟨12437842130866825290380045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8291894753911216860253363 12437842130866825290380045)
                ·
                  refine ⟨4664190799075059483892517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12437842130866825290380045 4664190799075059483892517)
                  ·
                    refine ⟨874535774826573653229847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4664190799075059483892517 874535774826573653229847)
                    ·
                      rfl

theorem cell23_5109457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_5109457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109457 prefixEnd_5109457 := by exact prefixLift 5109457
  have htrace : WordTrace (prefixWord ++ tailWord_5109457) baseStart_5109457 baseEnd_5109457 := by
    simpa [prefixWord, tailWord_5109457, baseEnd_5109457] using wordTrace_append hprefix tailTrace_5109457
  have hstable : (prefixWord ++ tailWord_5109457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109457).length < 2 ^ (prefixWord ++ tailWord_5109457).sum := by decide
  have hdescent : baseEnd_5109457 < baseStart_5109457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109507 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 4, 3, 2]
def baseStart_5109507 : Nat := 118140960795 + 5109507 * 2 ^ 59
def prefixEnd_5109507 : Nat := 4983230072969 + 3 ^ 40 * 5109507 * 2
def baseEnd_5109507 : Nat := 2623632998512445764064311

theorem tailTrace_5109507 : CollatzResearch.WordTrace tailWord_5109507 prefixEnd_5109507 2623632998512445764064311 := by
  unfold tailWord_5109507
  simp only [CollatzResearch.WordTrace]
  refine ⟨186359030300136248166742775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124239353533424165444495183 186359030300136248166742775)
  ·
    refine ⟨279538545450204372250114163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186359030300136248166742775 279538545450204372250114163)
    ·
      refine ⟨419307818175306558375171245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279538545450204372250114163 419307818175306558375171245)
      ·
        refine ⟨157240431815739959390689217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 419307818175306558375171245 157240431815739959390689217)
        ·
          refine ⟨117930323861804969543016913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157240431815739959390689217 117930323861804969543016913)
          ·
            refine ⟨88447742896353727157262685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117930323861804969543016913 88447742896353727157262685)
            ·
              refine ⟨33167903586132647683973507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88447742896353727157262685 33167903586132647683973507)
              ·
                refine ⟨49751855379198971525960261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33167903586132647683973507 49751855379198971525960261)
                ·
                  refine ⟨9328472883599807161117549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49751855379198971525960261 9328472883599807161117549)
                  ·
                    refine ⟨3498177331349927685419081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9328472883599807161117549 3498177331349927685419081)
                    ·
                      refine ⟨2623632998512445764064311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3498177331349927685419081 2623632998512445764064311)
                      ·
                        rfl

theorem cell23_5109507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 3, 2].length) (baseStart_5109507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109507 prefixEnd_5109507 := by exact prefixLift 5109507
  have htrace : WordTrace (prefixWord ++ tailWord_5109507) baseStart_5109507 baseEnd_5109507 := by
    simpa [prefixWord, tailWord_5109507, baseEnd_5109507] using wordTrace_append hprefix tailTrace_5109507
  have hstable : (prefixWord ++ tailWord_5109507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109507).length < 2 ^ (prefixWord ++ tailWord_5109507).sum := by decide
  have hdescent : baseEnd_5109507 < baseStart_5109507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109514 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_5109514 : Nat := 118140960795 + 5109514 * 2 ^ 59
def prefixEnd_5109514 : Nat := 4983230072969 + 3 ^ 40 * 5109514 * 2
def baseEnd_5109514 : Nat := 2623636592877027236676779

theorem tailTrace_5109514 : CollatzResearch.WordTrace tailWord_5109514 prefixEnd_5109514 2623636592877027236676779 := by
  unfold tailWord_5109514
  simp only [CollatzResearch.WordTrace]
  refine ⟨46589821402777722090561899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124239523740740592241498397 46589821402777722090561899)
  ·
    refine ⟨69884732104166583135842849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46589821402777722090561899 69884732104166583135842849)
    ·
      refine ⟨52413549078124937351882137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69884732104166583135842849 52413549078124937351882137)
      ·
        refine ⟨39310161808593703013911603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52413549078124937351882137 39310161808593703013911603)
        ·
          refine ⟨58965242712890554520867405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39310161808593703013911603 58965242712890554520867405)
          ·
            refine ⟨22111966017333957945325277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58965242712890554520867405 22111966017333957945325277)
            ·
              refine ⟨8291987256500234229496979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22111966017333957945325277 8291987256500234229496979)
              ·
                refine ⟨12437980884750351344245469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8291987256500234229496979 12437980884750351344245469)
                ·
                  refine ⟨4664242831781381754092051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12437980884750351344245469 4664242831781381754092051)
                  ·
                    refine ⟨6996364247672072631138077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4664242831781381754092051 6996364247672072631138077)
                    ·
                      refine ⟨2623636592877027236676779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6996364247672072631138077 2623636592877027236676779)
                      ·
                        rfl

theorem cell23_5109514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_5109514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109514 prefixEnd_5109514 := by exact prefixLift 5109514
  have htrace : WordTrace (prefixWord ++ tailWord_5109514) baseStart_5109514 baseEnd_5109514 := by
    simpa [prefixWord, tailWord_5109514, baseEnd_5109514] using wordTrace_append hprefix tailTrace_5109514
  have hstable : (prefixWord ++ tailWord_5109514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109514).length < 2 ^ (prefixWord ++ tailWord_5109514).sum := by decide
  have hdescent : baseEnd_5109514 < baseStart_5109514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109537 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_5109537 : Nat := 118140960795 + 5109537 * 2 ^ 59
def prefixEnd_5109537 : Nat := 4983230072969 + 3 ^ 40 * 5109537 * 2
def baseEnd_5109537 : Nat := 2623648402932080646689173

theorem tailTrace_5109537 : CollatzResearch.WordTrace tailWord_5109537 prefixEnd_5109537 2623648402932080646689173 := by
  unfold tailWord_5109537
  simp only [CollatzResearch.WordTrace]
  refine ⟨186360124490027563290334865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124240082993351708860223243 186360124490027563290334865)
  ·
    refine ⟨139770093367520672467751149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186360124490027563290334865 139770093367520672467751149)
    ·
      refine ⟨52413785012820252175406681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139770093367520672467751149 52413785012820252175406681)
      ·
        refine ⟨39310338759615189131555011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52413785012820252175406681 39310338759615189131555011)
        ·
          refine ⟨58965508139422783697332517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39310338759615189131555011 58965508139422783697332517)
          ·
            refine ⟨11056032776141771943249847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58965508139422783697332517 11056032776141771943249847)
            ·
              refine ⟨16584049164212657914874771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11056032776141771943249847 16584049164212657914874771)
              ·
                refine ⟨24876073746318986872312157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16584049164212657914874771 24876073746318986872312157)
                ·
                  refine ⟨9328527654869620077117059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24876073746318986872312157 9328527654869620077117059)
                  ·
                    refine ⟨13992791482304430115675589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9328527654869620077117059 13992791482304430115675589)
                    ·
                      refine ⟨2623648402932080646689173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13992791482304430115675589 2623648402932080646689173)
                      ·
                        rfl

theorem cell23_5109537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_5109537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109537 prefixEnd_5109537 := by exact prefixLift 5109537
  have htrace : WordTrace (prefixWord ++ tailWord_5109537) baseStart_5109537 baseEnd_5109537 := by
    simpa [prefixWord, tailWord_5109537, baseEnd_5109537] using wordTrace_append hprefix tailTrace_5109537
  have hstable : (prefixWord ++ tailWord_5109537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109537).length < 2 ^ (prefixWord ++ tailWord_5109537).sum := by decide
  have hdescent : baseEnd_5109537 < baseStart_5109537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109565 : List Nat := [1, 4, 1, 4, 1, 3, 2, 2, 1, 1, 3]
def baseStart_5109565 : Nat := 118140960795 + 5109565 * 2 ^ 59
def prefixEnd_5109565 : Nat := 4983230072969 + 3 ^ 40 * 5109565 * 2
def baseEnd_5109565 : Nat := 2623662780390406537139045

theorem tailTrace_5109565 : CollatzResearch.WordTrace tailWord_5109565 prefixEnd_5109565 2623662780390406537139045 := by
  unfold tailWord_5109565
  simp only [CollatzResearch.WordTrace]
  refine ⟨186361145733926124072354149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124240763822617416048236099 186361145733926124072354149)
  ·
    refine ⟨34942714825111148263566403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186361145733926124072354149 34942714825111148263566403)
    ·
      refine ⟨52414072237666722395349605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34942714825111148263566403 52414072237666722395349605)
      ·
        refine ⟨9827638544562510449128051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52414072237666722395349605 9827638544562510449128051)
        ·
          refine ⟨14741457816843765673692077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9827638544562510449128051 14741457816843765673692077)
          ·
            refine ⟨5528046681316412127634529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14741457816843765673692077 5528046681316412127634529)
            ·
              refine ⟨4146035010987309095725897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5528046681316412127634529 4146035010987309095725897)
              ·
                refine ⟨3109526258240481821794423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4146035010987309095725897 3109526258240481821794423)
                ·
                  refine ⟨4664289387360722732691635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3109526258240481821794423 4664289387360722732691635)
                  ·
                    refine ⟨6996434081041084099037453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4664289387360722732691635 6996434081041084099037453)
                    ·
                      refine ⟨2623662780390406537139045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6996434081041084099037453 2623662780390406537139045)
                      ·
                        rfl

theorem cell23_5109565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_5109565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109565 prefixEnd_5109565 := by exact prefixLift 5109565
  have htrace : WordTrace (prefixWord ++ tailWord_5109565) baseStart_5109565 baseEnd_5109565 := by
    simpa [prefixWord, tailWord_5109565, baseEnd_5109565] using wordTrace_append hprefix tailTrace_5109565
  have hstable : (prefixWord ++ tailWord_5109565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109565).length < 2 ^ (prefixWord ++ tailWord_5109565).sum := by decide
  have hdescent : baseEnd_5109565 < baseStart_5109565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109581 : List Nat := [1, 6, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_5109581 : Nat := 118140960795 + 5109581 * 2 ^ 59
def prefixEnd_5109581 : Nat := 4983230072969 + 3 ^ 40 * 5109581 * 2
def baseEnd_5109581 : Nat := 874556998693626158179657

theorem tailTrace_5109581 : CollatzResearch.WordTrace tailWord_5109581 prefixEnd_5109581 874556998693626158179657 := by
  unfold tailWord_5109581
  simp only [CollatzResearch.WordTrace]
  refine ⟨186361729301868158804936597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124241152867912105869957731 186361729301868158804936597)
  ·
    refine ⟨8735706061025069943981403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 186361729301868158804936597 8735706061025069943981403)
    ·
      refine ⟨13103559091537604915972105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8735706061025069943981403 13103559091537604915972105)
      ·
        refine ⟨9827669318653203686979079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13103559091537604915972105 9827669318653203686979079)
        ·
          refine ⟨14741503977979805530468619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9827669318653203686979079 14741503977979805530468619)
          ·
            refine ⟨22112255966969708295702929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14741503977979805530468619 22112255966969708295702929)
            ·
              refine ⟨16584191975227281221777197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22112255966969708295702929 16584191975227281221777197)
              ·
                refine ⟨6219071990710230458166449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16584191975227281221777197 6219071990710230458166449)
                ·
                  refine ⟨4664303993032672843624837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6219071990710230458166449 4664303993032672843624837)
                  ·
                    refine ⟨874556998693626158179657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4664303993032672843624837 874556998693626158179657)
                    ·
                      rfl

theorem cell23_5109581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_5109581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109581 prefixEnd_5109581 := by exact prefixLift 5109581
  have htrace : WordTrace (prefixWord ++ tailWord_5109581) baseStart_5109581 baseEnd_5109581 := by
    simpa [prefixWord, tailWord_5109581, baseEnd_5109581] using wordTrace_append hprefix tailTrace_5109581
  have hstable : (prefixWord ++ tailWord_5109581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109581).length < 2 ^ (prefixWord ++ tailWord_5109581).sum := by decide
  have hdescent : baseEnd_5109581 < baseStart_5109581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109587 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 8, 1, 3]
def baseStart_5109587 : Nat := 118140960795 + 5109587 * 2 ^ 59
def prefixEnd_5109587 : Nat := 4983230072969 + 3 ^ 40 * 5109587 * 2
def baseEnd_5109587 : Nat := 2623674076964805451063943

theorem tailTrace_5109587 : CollatzResearch.WordTrace tailWord_5109587 prefixEnd_5109587 2623674076964805451063943 := by
  unfold tailWord_5109587
  simp only [CollatzResearch.WordTrace]
  refine ⟨186361948139846421829655015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124241298759897614553103343 186361948139846421829655015)
  ·
    refine ⟨279542922209769632744482523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186361948139846421829655015 279542922209769632744482523)
    ·
      refine ⟨419314383314654449116723785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279542922209769632744482523 419314383314654449116723785)
      ·
        refine ⟨314485787485990836837542839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419314383314654449116723785 314485787485990836837542839)
        ·
          refine ⟨471728681228986255256314259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314485787485990836837542839 471728681228986255256314259)
          ·
            refine ⟨707593021843479382884471389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471728681228986255256314259 707593021843479382884471389)
            ·
              refine ⟨265347383191304768581676771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 707593021843479382884471389 265347383191304768581676771)
              ·
                refine ⟨398021074786957152872515157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265347383191304768581676771 398021074786957152872515157)
                ·
                  refine ⟨4664309470159654135224787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 398021074786957152872515157 4664309470159654135224787)
                  ·
                    refine ⟨6996464205239481202837181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4664309470159654135224787 6996464205239481202837181)
                    ·
                      refine ⟨2623674076964805451063943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6996464205239481202837181 2623674076964805451063943)
                      ·
                        rfl

theorem cell23_5109587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 1, 3].length) (baseStart_5109587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109587 prefixEnd_5109587 := by exact prefixLift 5109587
  have htrace : WordTrace (prefixWord ++ tailWord_5109587) baseStart_5109587 baseEnd_5109587 := by
    simpa [prefixWord, tailWord_5109587, baseEnd_5109587] using wordTrace_append hprefix tailTrace_5109587
  have hstable : (prefixWord ++ tailWord_5109587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109587).length < 2 ^ (prefixWord ++ tailWord_5109587).sum := by decide
  have hdescent : baseEnd_5109587 < baseStart_5109587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109661 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_5109661 : Nat := 118140960795 + 5109661 * 2 ^ 59
def prefixEnd_5109661 : Nat := 4983230072969 + 3 ^ 40 * 5109661 * 2
def baseEnd_5109661 : Nat := 2623712074533238161538603

theorem tailTrace_5109661 : CollatzResearch.WordTrace tailWord_5109661 prefixEnd_5109661 2623712074533238161538603 := by
  unfold tailWord_5109661
  simp only [CollatzResearch.WordTrace]
  refine ⟨186364647141578332467848837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124243098094385554978565891 186364647141578332467848837)
  ·
    refine ⟨34943371339045937337721657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186364647141578332467848837 34943371339045937337721657)
    ·
      refine ⟨26207528504284453003291243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34943371339045937337721657 26207528504284453003291243)
      ·
        refine ⟨39311292756426679504936865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26207528504284453003291243 39311292756426679504936865)
        ·
          refine ⟨29483469567320009628702649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39311292756426679504936865 29483469567320009628702649)
          ·
            refine ⟨22112602175490007221526987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29483469567320009628702649 22112602175490007221526987)
            ·
              refine ⟨33168903263235010832290481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22112602175490007221526987 33168903263235010832290481)
              ·
                refine ⟨24876677447426258124217861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33168903263235010832290481 24876677447426258124217861)
                ·
                  refine ⟨4664377021392423398290849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24876677447426258124217861 4664377021392423398290849)
                  ·
                    refine ⟨3498282766044317548718137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4664377021392423398290849 3498282766044317548718137)
                    ·
                      refine ⟨2623712074533238161538603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3498282766044317548718137 2623712074533238161538603)
                      ·
                        rfl

theorem cell23_5109661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_5109661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109661 prefixEnd_5109661 := by exact prefixLift 5109661
  have htrace : WordTrace (prefixWord ++ tailWord_5109661) baseStart_5109661 baseEnd_5109661 := by
    simpa [prefixWord, tailWord_5109661, baseEnd_5109661] using wordTrace_append hprefix tailTrace_5109661
  have hstable : (prefixWord ++ tailWord_5109661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109661).length < 2 ^ (prefixWord ++ tailWord_5109661).sum := by decide
  have hdescent : baseEnd_5109661 < baseStart_5109661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109680 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 2, 11]
def baseStart_5109680 : Nat := 118140960795 + 5109680 * 2 ^ 59
def prefixEnd_5109680 : Nat := 4983230072969 + 3 ^ 40 * 5109680 * 2
def baseEnd_5109680 : Nat := 874573943555224529067005

theorem tailTrace_5109680 : CollatzResearch.WordTrace tailWord_5109680 prefixEnd_5109680 874573943555224529067005 := by
  unfold tailWord_5109680
  simp only [CollatzResearch.WordTrace]
  refine ⟨93182670064254749356395247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124243560085672999141860329 93182670064254749356395247)
  ·
    refine ⟨139774005096382124034592871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93182670064254749356395247 139774005096382124034592871)
    ·
      refine ⟨209661007644573186051889307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139774005096382124034592871 209661007644573186051889307)
      ·
        refine ⟨314491511466859779077833961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209661007644573186051889307 314491511466859779077833961)
        ·
          refine ⟨235868633600144834308375471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314491511466859779077833961 235868633600144834308375471)
          ·
            refine ⟨353802950400217251462563207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235868633600144834308375471 353802950400217251462563207)
            ·
              refine ⟨530704425600325877193844811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353802950400217251462563207 530704425600325877193844811)
              ·
                refine ⟨796056638400488815790767217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530704425600325877193844811 796056638400488815790767217)
                ·
                  refine ⟨597042478800366611843075413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 796056638400488815790767217 597042478800366611843075413)
                  ·
                    refine ⟨874573943555224529067005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 597042478800366611843075413 874573943555224529067005)
                    ·
                      rfl

theorem cell23_5109680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_5109680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109680 prefixEnd_5109680 := by exact prefixLift 5109680
  have htrace : WordTrace (prefixWord ++ tailWord_5109680) baseStart_5109680 baseEnd_5109680 := by
    simpa [prefixWord, tailWord_5109680, baseEnd_5109680] using wordTrace_append hprefix tailTrace_5109680
  have hstable : (prefixWord ++ tailWord_5109680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109680).length < 2 ^ (prefixWord ++ tailWord_5109680).sum := by decide
  have hdescent : baseEnd_5109680 < baseStart_5109680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109735 : List Nat := [1, 1, 5, 2, 4, 1, 2, 2, 5]
def baseStart_5109735 : Nat := 118140960795 + 5109735 * 2 ^ 59
def prefixEnd_5109735 : Nat := 4983230072969 + 3 ^ 40 * 5109735 * 2
def baseEnd_5109735 : Nat := 291527785789074541334807

theorem tailTrace_5109735 : CollatzResearch.WordTrace tailWord_5109735 prefixEnd_5109735 291527785789074541334807 := by
  unfold tailWord_5109735
  simp only [CollatzResearch.WordTrace]
  refine ⟨186367346143310243106042659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124244897428873495404028439 186367346143310243106042659)
  ·
    refine ⟨279551019214965364659063989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186367346143310243106042659 279551019214965364659063989)
    ·
      refine ⟨26207908051403002936787249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 279551019214965364659063989 26207908051403002936787249)
      ·
        refine ⟨19655931038552252202590437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26207908051403002936787249 19655931038552252202590437)
        ·
          refine ⟨3685487069728547287985707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19655931038552252202590437 3685487069728547287985707)
          ·
            refine ⟨5528230604592820931978561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3685487069728547287985707 5528230604592820931978561)
            ·
              refine ⟨4146172953444615698983921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5528230604592820931978561 4146172953444615698983921)
              ·
                refine ⟨3109629715083461774237941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4146172953444615698983921 3109629715083461774237941)
                ·
                  refine ⟨291527785789074541334807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3109629715083461774237941 291527785789074541334807)
                  ·
                    rfl

theorem cell23_5109735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 5].length) (baseStart_5109735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109735 prefixEnd_5109735 := by exact prefixLift 5109735
  have htrace : WordTrace (prefixWord ++ tailWord_5109735) baseStart_5109735 baseEnd_5109735 := by
    simpa [prefixWord, tailWord_5109735, baseEnd_5109735] using wordTrace_append hprefix tailTrace_5109735
  have hstable : (prefixWord ++ tailWord_5109735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109735).length < 2 ^ (prefixWord ++ tailWord_5109735).sum := by decide
  have hdescent : baseEnd_5109735 < baseStart_5109735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109787 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 5, 5]
def baseStart_5109787 : Nat := 118140960795 + 5109787 * 2 ^ 59
def prefixEnd_5109787 : Nat := 4983230072969 + 3 ^ 40 * 5109787 * 2
def baseEnd_5109787 : Nat := 874592257698568222854341

theorem tailTrace_5109787 : CollatzResearch.WordTrace tailWord_5109787 prefixEnd_5109787 874592257698568222854341 := by
  unfold tailWord_5109787
  simp only [CollatzResearch.WordTrace]
  refine ⟨186369242739121855986935615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124246161826081237324623743 186369242739121855986935615)
  ·
    refine ⟨279553864108682783980403423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186369242739121855986935615 279553864108682783980403423)
    ·
      refine ⟨419330796163024175970605135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279553864108682783980403423 419330796163024175970605135)
      ·
        refine ⟨628996194244536263955907703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419330796163024175970605135 628996194244536263955907703)
        ·
          refine ⟨943494291366804395933861555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628996194244536263955907703 943494291366804395933861555)
          ·
            refine ⟨1415241437050206593900792333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943494291366804395933861555 1415241437050206593900792333)
            ·
              refine ⟨530715538893827472712797125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1415241437050206593900792333 530715538893827472712797125)
              ·
                refine ⟨99509163542592651133649461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530715538893827472712797125 99509163542592651133649461)
                ·
                  refine ⟨9328984082118061043779637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99509163542592651133649461 9328984082118061043779637)
                  ·
                    refine ⟨874592257698568222854341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9328984082118061043779637 874592257698568222854341)
                    ·
                      rfl

theorem cell23_5109787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 5].length) (baseStart_5109787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109787 prefixEnd_5109787 := by exact prefixLift 5109787
  have htrace : WordTrace (prefixWord ++ tailWord_5109787) baseStart_5109787 baseEnd_5109787 := by
    simpa [prefixWord, tailWord_5109787, baseEnd_5109787] using wordTrace_append hprefix tailTrace_5109787
  have hstable : (prefixWord ++ tailWord_5109787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109787).length < 2 ^ (prefixWord ++ tailWord_5109787).sum := by decide
  have hdescent : baseEnd_5109787 < baseStart_5109787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109807 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 4]
def baseStart_5109807 : Nat := 118140960795 + 5109807 * 2 ^ 59
def prefixEnd_5109807 : Nat := 4983230072969 + 3 ^ 40 * 5109807 * 2
def baseEnd_5109807 : Nat := 2623787042708794590312931

theorem tailTrace_5109807 : CollatzResearch.WordTrace tailWord_5109807 prefixEnd_5109807 2623787042708794590312931 := by
  unfold tailWord_5109807
  simp only [CollatzResearch.WordTrace]
  refine ⟨186369972199049399402663675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124246648132699599601775783 186369972199049399402663675)
  ·
    refine ⟨279554958298574099103995513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186369972199049399402663675 279554958298574099103995513)
    ·
      refine ⟨209666218723930574327996635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279554958298574099103995513 209666218723930574327996635)
      ·
        refine ⟨314499328085895861491994953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209666218723930574327996635 314499328085895861491994953)
        ·
          refine ⟨235874496064421896118996215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314499328085895861491994953 235874496064421896118996215)
          ·
            refine ⟨353811744096632844178494323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235874496064421896118996215 353811744096632844178494323)
            ·
              refine ⟨530717616144949266267741485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353811744096632844178494323 530717616144949266267741485)
              ·
                refine ⟨199019106054355974850403057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 530717616144949266267741485 199019106054355974850403057)
                ·
                  refine ⟨149264329540766981137802293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199019106054355974850403057 149264329540766981137802293)
                  ·
                    refine ⟨13993530894446904481668965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149264329540766981137802293 13993530894446904481668965)
                    ·
                      refine ⟨2623787042708794590312931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13993530894446904481668965 2623787042708794590312931)
                      ·
                        rfl

theorem cell23_5109807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_5109807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109807 prefixEnd_5109807 := by exact prefixLift 5109807
  have htrace : WordTrace (prefixWord ++ tailWord_5109807) baseStart_5109807 baseEnd_5109807 := by
    simpa [prefixWord, tailWord_5109807, baseEnd_5109807] using wordTrace_append hprefix tailTrace_5109807
  have hstable : (prefixWord ++ tailWord_5109807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109807).length < 2 ^ (prefixWord ++ tailWord_5109807).sum := by decide
  have hdescent : baseEnd_5109807 < baseStart_5109807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109821 : List Nat := [1, 4, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_5109821 : Nat := 118140960795 + 5109821 * 2 ^ 59
def prefixEnd_5109821 : Nat := 4983230072969 + 3 ^ 40 * 5109821 * 2
def baseEnd_5109821 : Nat := 874598077145985845179289

theorem tailTrace_5109821 : CollatzResearch.WordTrace tailWord_5109821 prefixEnd_5109821 874598077145985845179289 := by
  unfold tailWord_5109821
  simp only [CollatzResearch.WordTrace]
  refine ⟨186370482820998679793673317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124246988547332453195782211 186370482820998679793673317)
  ·
    refine ⟨34944465528937252461313747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186370482820998679793673317 34944465528937252461313747)
    ·
      refine ⟨52416698293405878691970621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34944465528937252461313747 52416698293405878691970621)
      ·
        refine ⟨19656261860027204509488983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52416698293405878691970621 19656261860027204509488983)
        ·
          refine ⟨29484392790040806764233475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19656261860027204509488983 29484392790040806764233475)
          ·
            refine ⟨44226589185061210146350213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29484392790040806764233475 44226589185061210146350213)
            ·
              refine ⟨8292485472198976902440665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44226589185061210146350213 8292485472198976902440665)
              ·
                refine ⟨6219364104149232676830499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8292485472198976902440665 6219364104149232676830499)
                ·
                  refine ⟨9329046156223849015245749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6219364104149232676830499 9329046156223849015245749)
                  ·
                    refine ⟨874598077145985845179289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9329046156223849015245749 874598077145985845179289)
                    ·
                      rfl

theorem cell23_5109821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_5109821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109821 prefixEnd_5109821 := by exact prefixLift 5109821
  have htrace : WordTrace (prefixWord ++ tailWord_5109821) baseStart_5109821 baseEnd_5109821 := by
    simpa [prefixWord, tailWord_5109821, baseEnd_5109821] using wordTrace_append hprefix tailTrace_5109821
  have hstable : (prefixWord ++ tailWord_5109821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109821).length < 2 ^ (prefixWord ++ tailWord_5109821).sum := by decide
  have hdescent : baseEnd_5109821 < baseStart_5109821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109847 : List Nat := [1, 1, 3, 2, 2, 1, 13]
def baseStart_5109847 : Nat := 118140960795 + 5109847 * 2 ^ 59
def prefixEnd_5109847 : Nat := 4983230072969 + 3 ^ 40 * 5109847 * 2
def baseEnd_5109847 : Nat := 32392686196728079429787

theorem tailTrace_5109847 : CollatzResearch.WordTrace tailWord_5109847 prefixEnd_5109847 32392686196728079429787 := by
  unfold tailWord_5109847
  simp only [CollatzResearch.WordTrace]
  refine ⟨186371431118904486234119795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124247620745936324156079863 186371431118904486234119795)
  ·
    refine ⟨279557146678356729351179693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186371431118904486234119795 279557146678356729351179693)
    ·
      refine ⟨104833930004383773506692385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279557146678356729351179693 104833930004383773506692385)
      ·
        refine ⟨78625447503287830130019289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104833930004383773506692385 78625447503287830130019289)
        ·
          refine ⟨58969085627465872597514467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78625447503287830130019289 58969085627465872597514467)
          ·
            refine ⟨88453628441198808896271701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58969085627465872597514467 88453628441198808896271701)
            ·
              refine ⟨32392686196728079429787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 88453628441198808896271701 32392686196728079429787)
              ·
                rfl

theorem cell23_5109847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 13].length) (baseStart_5109847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109847 prefixEnd_5109847 := by exact prefixLift 5109847
  have htrace : WordTrace (prefixWord ++ tailWord_5109847) baseStart_5109847 baseEnd_5109847 := by
    simpa [prefixWord, tailWord_5109847, baseEnd_5109847] using wordTrace_append hprefix tailTrace_5109847
  have hstable : (prefixWord ++ tailWord_5109847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109847).length < 2 ^ (prefixWord ++ tailWord_5109847).sum := by decide
  have hdescent : baseEnd_5109847 < baseStart_5109847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109852 : List Nat := [2, 2, 4, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_5109852 : Nat := 118140960795 + 5109852 * 2 ^ 59
def prefixEnd_5109852 : Nat := 4983230072969 + 3 ^ 40 * 5109852 * 2
def baseEnd_5109852 : Nat := 2623810149338246914250225

theorem tailTrace_5109852 : CollatzResearch.WordTrace tailWord_5109852 prefixEnd_5109852 2623810149338246914250225 := by
  unfold tailWord_5109852
  simp only [CollatzResearch.WordTrace]
  refine ⟨93185806741943186044025905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124247742322590914725367873 93185806741943186044025905)
  ·
    refine ⟨69889355056457389533019429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93185806741943186044025905 69889355056457389533019429)
    ·
      refine ⟨13104254073085760537441143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69889355056457389533019429 13104254073085760537441143)
      ·
        refine ⟨19656381109628640806161715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13104254073085760537441143 19656381109628640806161715)
        ·
          refine ⟨29484571664442961209242573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19656381109628640806161715 29484571664442961209242573)
          ·
            refine ⟨11056714374166110453465965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29484571664442961209242573 11056714374166110453465965)
            ·
              refine ⟨4146267890312291420049737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11056714374166110453465965 4146267890312291420049737)
              ·
                refine ⟨3109700917734218565037303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4146267890312291420049737 3109700917734218565037303)
                ·
                  refine ⟨4664551376601327847555955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3109700917734218565037303 4664551376601327847555955)
                  ·
                    refine ⟨6996827064901991771333933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4664551376601327847555955 6996827064901991771333933)
                    ·
                      refine ⟨2623810149338246914250225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6996827064901991771333933 2623810149338246914250225)
                      ·
                        rfl

theorem cell23_5109852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_5109852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109852 prefixEnd_5109852 := by exact prefixLift 5109852
  have htrace : WordTrace (prefixWord ++ tailWord_5109852) baseStart_5109852 baseEnd_5109852 := by
    simpa [prefixWord, tailWord_5109852, baseEnd_5109852] using wordTrace_append hprefix tailTrace_5109852
  have hstable : (prefixWord ++ tailWord_5109852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109852).length < 2 ^ (prefixWord ++ tailWord_5109852).sum := by decide
  have hdescent : baseEnd_5109852 < baseStart_5109852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109868 : List Nat := [2, 2, 1, 1, 3, 3, 4, 1, 2, 4]
def baseStart_5109868 : Nat := 118140960795 + 5109868 * 2 ^ 59
def prefixEnd_5109868 : Nat := 4983230072969 + 3 ^ 40 * 5109868 * 2
def baseEnd_5109868 : Nat := 874606121676239617216717

theorem tailTrace_5109868 : CollatzResearch.WordTrace tailWord_5109868 prefixEnd_5109868 874606121676239617216717 := by
  unfold tailWord_5109868
  simp only [CollatzResearch.WordTrace]
  refine ⟨93186098525914203410317129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124248131367885604547089505 93186098525914203410317129)
  ·
    refine ⟨69889573894435652557737847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93186098525914203410317129 69889573894435652557737847)
    ·
      refine ⟨104834360841653478836606771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69889573894435652557737847 104834360841653478836606771)
      ·
        refine ⟨157251541262480218254910157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104834360841653478836606771 157251541262480218254910157)
        ·
          refine ⟨58969327973430081845591309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157251541262480218254910157 58969327973430081845591309)
          ·
            refine ⟨22113497990036280692096741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58969327973430081845591309 22113497990036280692096741)
            ·
              refine ⟨4146280873131802629768139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22113497990036280692096741 4146280873131802629768139)
              ·
                refine ⟨6219421309697703944652209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4146280873131802629768139 6219421309697703944652209)
                ·
                  refine ⟨4664565982273277958489157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6219421309697703944652209 4664565982273277958489157)
                  ·
                    refine ⟨874606121676239617216717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4664565982273277958489157 874606121676239617216717)
                    ·
                      rfl

theorem cell23_5109868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_5109868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109868 prefixEnd_5109868 := by exact prefixLift 5109868
  have htrace : WordTrace (prefixWord ++ tailWord_5109868) baseStart_5109868 baseEnd_5109868 := by
    simpa [prefixWord, tailWord_5109868, baseEnd_5109868] using wordTrace_append hprefix tailTrace_5109868
  have hstable : (prefixWord ++ tailWord_5109868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109868).length < 2 ^ (prefixWord ++ tailWord_5109868).sum := by decide
  have hdescent : baseEnd_5109868 < baseStart_5109868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109878 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_5109878 : Nat := 118140960795 + 5109878 * 2 ^ 59
def prefixEnd_5109878 : Nat := 4983230072969 + 3 ^ 40 * 5109878 * 2
def baseEnd_5109878 : Nat := 2623823499835263812525105

theorem tailTrace_5109878 : CollatzResearch.WordTrace tailWord_5109878 prefixEnd_5109878 2623823499835263812525105 := by
  unfold tailWord_5109878
  simp only [CollatzResearch.WordTrace]
  refine ⟨11648285111362011158031143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124248374521194785685665525 11648285111362011158031143)
  ·
    refine ⟨17472427667043016737046715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11648285111362011158031143 17472427667043016737046715)
    ·
      refine ⟨26208641500564525105570073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17472427667043016737046715 26208641500564525105570073)
      ·
        refine ⟨19656481125423393829177555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26208641500564525105570073 19656481125423393829177555)
        ·
          refine ⟨29484721688135090743766333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19656481125423393829177555 29484721688135090743766333)
          ·
            refine ⟨11056770633050659028912375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29484721688135090743766333 11056770633050659028912375)
            ·
              refine ⟨16585155949575988543368563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11056770633050659028912375 16585155949575988543368563)
              ·
                refine ⟨24877733924363982815052845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16585155949575988543368563 24877733924363982815052845)
                ·
                  refine ⟨9329150221636493555644817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24877733924363982815052845 9329150221636493555644817)
                  ·
                    refine ⟨6996862666227370166733613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9329150221636493555644817 6996862666227370166733613)
                    ·
                      refine ⟨2623823499835263812525105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6996862666227370166733613 2623823499835263812525105)
                      ·
                        rfl

theorem cell23_5109878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_5109878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109878 prefixEnd_5109878 := by exact prefixLift 5109878
  have htrace : WordTrace (prefixWord ++ tailWord_5109878) baseStart_5109878 baseEnd_5109878 := by
    simpa [prefixWord, tailWord_5109878, baseEnd_5109878] using wordTrace_append hprefix tailTrace_5109878
  have hstable : (prefixWord ++ tailWord_5109878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109878).length < 2 ^ (prefixWord ++ tailWord_5109878).sum := by decide
  have hdescent : baseEnd_5109878 < baseStart_5109878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109891 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 3]
def baseStart_5109891 : Nat := 118140960795 + 5109891 * 2 ^ 59
def prefixEnd_5109891 : Nat := 4983230072969 + 3 ^ 40 * 5109891 * 2
def baseEnd_5109891 : Nat := 2623830175083772261662545

theorem tailTrace_5109891 : CollatzResearch.WordTrace tailWord_5109891 prefixEnd_5109891 2623830175083772261662545 := by
  unfold tailWord_5109891
  simp only [CollatzResearch.WordTrace]
  refine ⟨186373035930745081748721527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124248690620496721165814351 186373035930745081748721527)
  ·
    refine ⟨279559553896117622623082291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186373035930745081748721527 279559553896117622623082291)
    ·
      refine ⟨419339330844176433934623437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279559553896117622623082291 419339330844176433934623437)
      ·
        refine ⟨157252249066566162725483789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 419339330844176433934623437 157252249066566162725483789)
        ·
          refine ⟨58969593399962311022056421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157252249066566162725483789 58969593399962311022056421)
          ·
            refine ⟨11056798762492933316635579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58969593399962311022056421 11056798762492933316635579)
            ·
              refine ⟨16585198143739399974953369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11056798762492933316635579 16585198143739399974953369)
              ·
                refine ⟨12438898607804549981215027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16585198143739399974953369 12438898607804549981215027)
                ·
                  refine ⟨18658347911706824971822541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12438898607804549981215027 18658347911706824971822541)
                  ·
                    refine ⟨6996880466890059364433453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18658347911706824971822541 6996880466890059364433453)
                    ·
                      refine ⟨2623830175083772261662545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6996880466890059364433453 2623830175083772261662545)
                      ·
                        rfl

theorem cell23_5109891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_5109891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109891 prefixEnd_5109891 := by exact prefixLift 5109891
  have htrace : WordTrace (prefixWord ++ tailWord_5109891) baseStart_5109891 baseEnd_5109891 := by
    simpa [prefixWord, tailWord_5109891, baseEnd_5109891] using wordTrace_append hprefix tailTrace_5109891
  have hstable : (prefixWord ++ tailWord_5109891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109891).length < 2 ^ (prefixWord ++ tailWord_5109891).sum := by decide
  have hdescent : baseEnd_5109891 < baseStart_5109891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109944 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_5109944 : Nat := 118140960795 + 5109944 * 2 ^ 59
def prefixEnd_5109944 : Nat := 4983230072969 + 3 ^ 40 * 5109944 * 2
def baseEnd_5109944 : Nat := 2623857389558460554299801

theorem tailTrace_5109944 : CollatzResearch.WordTrace tailWord_5109944 prefixEnd_5109944 2623857389558460554299801 := by
  unfold tailWord_5109944
  simp only [CollatzResearch.WordTrace]
  refine ⟨93187484499776535900200443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124249979333035381200267257 93187484499776535900200443)
  ·
    refine ⟨139781226749664803850300665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93187484499776535900200443 139781226749664803850300665)
    ·
      refine ⟨104835920062248602887725499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139781226749664803850300665 104835920062248602887725499)
      ·
        refine ⟨157253880093372904331588249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104835920062248602887725499 157253880093372904331588249)
        ·
          refine ⟨117940410070029678248691187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157253880093372904331588249 117940410070029678248691187)
          ·
            refine ⟨176910615105044517373036781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117940410070029678248691187 176910615105044517373036781)
            ·
              refine ⟨66341480664391694014888793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176910615105044517373036781 66341480664391694014888793)
              ·
                refine ⟨49756110498293770511166595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66341480664391694014888793 49756110498293770511166595)
                ·
                  refine ⟨74634165747440655766749893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49756110498293770511166595 74634165747440655766749893)
                  ·
                    refine ⟨13993906077645122956265605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74634165747440655766749893 13993906077645122956265605)
                    ·
                      refine ⟨2623857389558460554299801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13993906077645122956265605 2623857389558460554299801)
                      ·
                        rfl

theorem cell23_5109944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_5109944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109944 prefixEnd_5109944 := by exact prefixLift 5109944
  have htrace : WordTrace (prefixWord ++ tailWord_5109944) baseStart_5109944 baseEnd_5109944 := by
    simpa [prefixWord, tailWord_5109944, baseEnd_5109944] using wordTrace_append hprefix tailTrace_5109944
  have hstable : (prefixWord ++ tailWord_5109944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109944).length < 2 ^ (prefixWord ++ tailWord_5109944).sum := by decide
  have hdescent : baseEnd_5109944 < baseStart_5109944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109952 : List Nat := [2, 1, 1, 2, 5, 3, 2, 1, 1, 3, 2]
def baseStart_5109952 : Nat := 118140960795 + 5109952 * 2 ^ 59
def prefixEnd_5109952 : Nat := 4983230072969 + 3 ^ 40 * 5109952 * 2
def baseEnd_5109952 : Nat := 2623861497403696522999765

theorem tailTrace_5109952 : CollatzResearch.WordTrace tailWord_5109952 prefixEnd_5109952 2623861497403696522999765 := by
  unfold tailWord_5109952
  simp only [CollatzResearch.WordTrace]
  refine ⟨93187630391762044583346055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124250173855682726111128073 93187630391762044583346055)
  ·
    refine ⟨139781445587643066875019083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93187630391762044583346055 139781445587643066875019083)
    ·
      refine ⟨209672168381464600312528625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139781445587643066875019083 209672168381464600312528625)
      ·
        refine ⟨157254126286098450234396469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209672168381464600312528625 157254126286098450234396469)
        ·
          refine ⟨14742574339321729709474669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157254126286098450234396469 14742574339321729709474669)
          ·
            refine ⟨5528465377245648641053001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14742574339321729709474669 5528465377245648641053001)
            ·
              refine ⟨4146349032934236480789751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5528465377245648641053001 4146349032934236480789751)
              ·
                refine ⟨6219523549401354721184627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4146349032934236480789751 6219523549401354721184627)
                ·
                  refine ⟨9329285324102032081776941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6219523549401354721184627 9329285324102032081776941)
                  ·
                    refine ⟨3498481996538262030666353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9329285324102032081776941 3498481996538262030666353)
                    ·
                      refine ⟨2623861497403696522999765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3498481996538262030666353 2623861497403696522999765)
                      ·
                        rfl

theorem cell23_5109952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 1, 3, 2].length) (baseStart_5109952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109952 prefixEnd_5109952 := by exact prefixLift 5109952
  have htrace : WordTrace (prefixWord ++ tailWord_5109952) baseStart_5109952 baseEnd_5109952 := by
    simpa [prefixWord, tailWord_5109952, baseEnd_5109952] using wordTrace_append hprefix tailTrace_5109952
  have hstable : (prefixWord ++ tailWord_5109952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109952).length < 2 ^ (prefixWord ++ tailWord_5109952).sum := by decide
  have hdescent : baseEnd_5109952 < baseStart_5109952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109984 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 3, 7]
def baseStart_5109984 : Nat := 118140960795 + 5109984 * 2 ^ 59
def prefixEnd_5109984 : Nat := 4983230072969 + 3 ^ 40 * 5109984 * 2
def baseEnd_5109984 : Nat := 874625976261546799266539

theorem tailTrace_5109984 : CollatzResearch.WordTrace tailWord_5109984 prefixEnd_5109984 874625976261546799266539 := by
  unfold tailWord_5109984
  simp only [CollatzResearch.WordTrace]
  refine ⟨93188213959704079315928503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124250951946272105754571337 93188213959704079315928503)
  ·
    refine ⟨139782320939556118973892755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93188213959704079315928503 139782320939556118973892755)
    ·
      refine ⟨209673481409334178460839133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139782320939556118973892755 209673481409334178460839133)
      ·
        refine ⟨78627555528500316922814675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209673481409334178460839133 78627555528500316922814675)
        ·
          refine ⟨117941333292750475384222013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78627555528500316922814675 117941333292750475384222013)
          ·
            refine ⟨44227999984781428269083255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117941333292750475384222013 44227999984781428269083255)
            ·
              refine ⟨66341999977172142403624883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44227999984781428269083255 66341999977172142403624883)
              ·
                refine ⟨99512999965758213605437325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66341999977172142403624883 99512999965758213605437325)
                ·
                  refine ⟨37317374987159330102038997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99512999965758213605437325 37317374987159330102038997)
                  ·
                    refine ⟨874625976261546799266539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37317374987159330102038997 874625976261546799266539)
                    ·
                      rfl

theorem cell23_5109984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_5109984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109984 prefixEnd_5109984 := by exact prefixLift 5109984
  have htrace : WordTrace (prefixWord ++ tailWord_5109984) baseStart_5109984 baseEnd_5109984 := by
    simpa [prefixWord, tailWord_5109984, baseEnd_5109984] using wordTrace_append hprefix tailTrace_5109984
  have hstable : (prefixWord ++ tailWord_5109984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109984).length < 2 ^ (prefixWord ++ tailWord_5109984).sum := by decide
  have hdescent : baseEnd_5109984 < baseStart_5109984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5109986 : List Nat := [3, 3, 4, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5109986 : Nat := 118140960795 + 5109986 * 2 ^ 59
def prefixEnd_5109986 : Nat := 4983230072969 + 3 ^ 40 * 5109986 * 2
def baseEnd_5109986 : Nat := 2623878955745949389974609

theorem tailTrace_5109986 : CollatzResearch.WordTrace tailWord_5109986 prefixEnd_5109986 2623878955745949389974609 := by
  unfold tailWord_5109986
  simp only [CollatzResearch.WordTrace]
  refine ⟨46594125216350228243357453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124251000576933941982286541 46594125216350228243357453)
  ·
    refine ⟨17472796956131335591259045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46594125216350228243357453 17472796956131335591259045)
    ·
      refine ⟨3276149429274625423361071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17472796956131335591259045 3276149429274625423361071)
      ·
        refine ⟨4914224143911938135041607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3276149429274625423361071 4914224143911938135041607)
        ·
          refine ⟨7371336215867907202562411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4914224143911938135041607 7371336215867907202562411)
          ·
            refine ⟨11057004323801860803843617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7371336215867907202562411 11057004323801860803843617)
            ·
              refine ⟨8292753242851395602882713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11057004323801860803843617 8292753242851395602882713)
              ·
                refine ⟨6219564932138546702162035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8292753242851395602882713 6219564932138546702162035)
                ·
                  refine ⟨9329347398207820053243053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6219564932138546702162035 9329347398207820053243053)
                  ·
                    refine ⟨3498505274327932519966145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9329347398207820053243053 3498505274327932519966145)
                    ·
                      refine ⟨2623878955745949389974609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3498505274327932519966145 2623878955745949389974609)
                      ·
                        rfl

theorem cell23_5109986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5109986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5109986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5109986 prefixEnd_5109986 := by exact prefixLift 5109986
  have htrace : WordTrace (prefixWord ++ tailWord_5109986) baseStart_5109986 baseEnd_5109986 := by
    simpa [prefixWord, tailWord_5109986, baseEnd_5109986] using wordTrace_append hprefix tailTrace_5109986
  have hstable : (prefixWord ++ tailWord_5109986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5109986).length < 2 ^ (prefixWord ++ tailWord_5109986).sum := by decide
  have hdescent : baseEnd_5109986 < baseStart_5109986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5109986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110018 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_5110018 : Nat := 118140960795 + 5110018 * 2 ^ 59
def prefixEnd_5110018 : Nat := 4983230072969 + 3 ^ 40 * 5110018 * 2
def baseEnd_5110018 : Nat := 874631795708964421591487

theorem tailTrace_5110018 : CollatzResearch.WordTrace tailWord_5110018 prefixEnd_5110018 874631795708964421591487 := by
  unfold tailWord_5110018
  simp only [CollatzResearch.WordTrace]
  refine ⟨46594417000321245609648677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124251778667523321625729805 46594417000321245609648677)
  ·
    refine ⟨8736453187560233551809127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46594417000321245609648677 8736453187560233551809127)
    ·
      refine ⟨13104679781340350327713691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8736453187560233551809127 13104679781340350327713691)
      ·
        refine ⟨19657019672010525491570537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13104679781340350327713691 19657019672010525491570537)
        ·
          refine ⟨14742764754007894118677903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19657019672010525491570537 14742764754007894118677903)
          ·
            refine ⟨22114147131011841178016855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14742764754007894118677903 22114147131011841178016855)
            ·
              refine ⟨33171220696517761767025283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22114147131011841178016855 33171220696517761767025283)
              ·
                refine ⟨49756831044776642650537925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33171220696517761767025283 49756831044776642650537925)
                ·
                  refine ⟨9329405820895620496975861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49756831044776642650537925 9329405820895620496975861)
                  ·
                    refine ⟨874631795708964421591487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9329405820895620496975861 874631795708964421591487)
                    ·
                      rfl

theorem cell23_5110018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_5110018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110018 prefixEnd_5110018 := by exact prefixLift 5110018
  have htrace : WordTrace (prefixWord ++ tailWord_5110018) baseStart_5110018 baseEnd_5110018 := by
    simpa [prefixWord, tailWord_5110018, baseEnd_5110018] using wordTrace_append hprefix tailTrace_5110018
  have hstable : (prefixWord ++ tailWord_5110018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110018).length < 2 ^ (prefixWord ++ tailWord_5110018).sum := by decide
  have hdescent : baseEnd_5110018 < baseStart_5110018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110078 : List Nat := [4, 2, 1, 2, 1, 2, 1, 4, 6]
def baseStart_5110078 : Nat := 118140960795 + 5110078 * 2 ^ 59
def prefixEnd_5110078 : Nat := 4983230072969 + 3 ^ 40 * 5110078 * 2
def baseEnd_5110078 : Nat := 291547355107351447780465

theorem tailTrace_5110078 : CollatzResearch.WordTrace tailWord_5110078 prefixEnd_5110078 291547355107351447780465 := by
  unfold tailWord_5110078
  simp only [CollatzResearch.WordTrace]
  refine ⟨23297482047633451585722361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124253237587378408457185925 23297482047633451585722361)
  ·
    refine ⟨17473111535725088689291771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23297482047633451585722361 17473111535725088689291771)
    ·
      refine ⟨26209667303587633033937657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17473111535725088689291771 26209667303587633033937657)
      ·
        refine ⟨19657250477690724775453243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26209667303587633033937657 19657250477690724775453243)
        ·
          refine ⟨29485875716536087163179865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19657250477690724775453243 29485875716536087163179865)
          ·
            refine ⟨22114406787402065372384899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29485875716536087163179865 22114406787402065372384899)
            ·
              refine ⟨33171610181103098058577349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22114406787402065372384899 33171610181103098058577349)
              ·
                refine ⟨6219676908956830885983253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33171610181103098058577349 6219676908956830885983253)
                ·
                  refine ⟨291547355107351447780465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6219676908956830885983253 291547355107351447780465)
                  ·
                    rfl

theorem cell23_5110078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_5110078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110078 prefixEnd_5110078 := by exact prefixLift 5110078
  have htrace : WordTrace (prefixWord ++ tailWord_5110078) baseStart_5110078 baseEnd_5110078 := by
    simpa [prefixWord, tailWord_5110078, baseEnd_5110078] using wordTrace_append hprefix tailTrace_5110078
  have hstable : (prefixWord ++ tailWord_5110078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110078).length < 2 ^ (prefixWord ++ tailWord_5110078).sum := by decide
  have hdescent : baseEnd_5110078 < baseStart_5110078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110121 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 1, 6]
def baseStart_5110121 : Nat := 118140960795 + 5110121 * 2 ^ 59
def prefixEnd_5110121 : Nat := 4983230072969 + 3 ^ 40 * 5110121 * 2
def baseEnd_5110121 : Nat := 874649425211435453928829

theorem tailTrace_5110121 : CollatzResearch.WordTrace tailWord_5110121 prefixEnd_5110121 874649425211435453928829 := by
  unfold tailWord_5110121
  simp only [CollatzResearch.WordTrace]
  refine ⟨186381424719911831029594217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124254283146607887353062811 186381424719911831029594217)
  ·
    refine ⟨139786068539933873272195663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186381424719911831029594217 139786068539933873272195663)
    ·
      refine ⟨209679102809900809908293495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139786068539933873272195663 209679102809900809908293495)
      ·
        refine ⟨314518654214851214862440243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209679102809900809908293495 314518654214851214862440243)
        ·
          refine ⟨471777981322276822293660365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314518654214851214862440243 471777981322276822293660365)
          ·
            refine ⟨176916742995853808360122637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 471777981322276822293660365 176916742995853808360122637)
            ·
              refine ⟨66343778623445178135045989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176916742995853808360122637 66343778623445178135045989)
              ·
                refine ⟨12439458491895970900321123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66343778623445178135045989 12439458491895970900321123)
                ·
                  refine ⟨18659187737843956350481685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12439458491895970900321123 18659187737843956350481685)
                  ·
                    refine ⟨874649425211435453928829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18659187737843956350481685 874649425211435453928829)
                    ·
                      rfl

theorem cell23_5110121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_5110121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110121 prefixEnd_5110121 := by exact prefixLift 5110121
  have htrace : WordTrace (prefixWord ++ tailWord_5110121) baseStart_5110121 baseEnd_5110121 := by
    simpa [prefixWord, tailWord_5110121, baseEnd_5110121] using wordTrace_append hprefix tailTrace_5110121
  have hstable : (prefixWord ++ tailWord_5110121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110121).length < 2 ^ (prefixWord ++ tailWord_5110121).sum := by decide
  have hdescent : baseEnd_5110121 < baseStart_5110121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110148 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_5110148 : Nat := 118140960795 + 5110148 * 2 ^ 59
def prefixEnd_5110148 : Nat := 4983230072969 + 3 ^ 40 * 5110148 * 2
def baseEnd_5110148 : Nat := 2623962139611977756148863

theorem tailTrace_5110148 : CollatzResearch.WordTrace tailWord_5110148 prefixEnd_5110148 2623962139611977756148863 := by
  unfold tailWord_5110148
  simp only [CollatzResearch.WordTrace]
  refine ⟨93191204745407007320413549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124254939660542676427218065 93191204745407007320413549)
  ·
    refine ⟨34946701779527627745155081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93191204745407007320413549 34946701779527627745155081)
    ·
      refine ⟨26210026334645720808866311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34946701779527627745155081 26210026334645720808866311)
      ·
        refine ⟨39315039501968581213299467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26210026334645720808866311 39315039501968581213299467)
        ·
          refine ⟨58972559252952871819949201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39315039501968581213299467 58972559252952871819949201)
          ·
            refine ⟨44229419439714653864961901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58972559252952871819949201 44229419439714653864961901)
            ·
              refine ⟨16586032289892995199360713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44229419439714653864961901 16586032289892995199360713)
              ·
                refine ⟨12439524217419746399520535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16586032289892995199360713 12439524217419746399520535)
                ·
                  refine ⟨18659286326129619599280803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12439524217419746399520535 18659286326129619599280803)
                  ·
                    refine ⟨27988929489194429398921205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18659286326129619599280803 27988929489194429398921205)
                    ·
                      refine ⟨2623962139611977756148863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27988929489194429398921205 2623962139611977756148863)
                      ·
                        rfl

theorem cell23_5110148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_5110148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110148 prefixEnd_5110148 := by exact prefixLift 5110148
  have htrace : WordTrace (prefixWord ++ tailWord_5110148) baseStart_5110148 baseEnd_5110148 := by
    simpa [prefixWord, tailWord_5110148, baseEnd_5110148] using wordTrace_append hprefix tailTrace_5110148
  have hstable : (prefixWord ++ tailWord_5110148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110148).length < 2 ^ (prefixWord ++ tailWord_5110148).sum := by decide
  have hdescent : baseEnd_5110148 < baseStart_5110148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110151 : List Nat := [1, 1, 4, 2, 2, 1, 2, 10]
def baseStart_5110151 : Nat := 118140960795 + 5110151 * 2 ^ 59
def prefixEnd_5110151 : Nat := 4983230072969 + 3 ^ 40 * 5110151 * 2
def baseEnd_5110151 : Nat := 97183840001997823867087

theorem tailTrace_5110151 : CollatzResearch.WordTrace tailWord_5110151 prefixEnd_5110151 97183840001997823867087 := by
  unfold tailWord_5110151
  simp only [CollatzResearch.WordTrace]
  refine ⟨186382518909803146153186307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124255012606535430768790871 186382518909803146153186307)
  ·
    refine ⟨279573778364704719229779461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186382518909803146153186307 279573778364704719229779461)
    ·
      refine ⟨52420083443382134855583649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279573778364704719229779461 52420083443382134855583649)
      ·
        refine ⟨39315062582536601141687737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52420083443382134855583649 39315062582536601141687737)
        ·
          refine ⟨29486296936902450856265803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39315062582536601141687737 29486296936902450856265803)
          ·
            refine ⟨44229445405353676284398705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29486296936902450856265803 44229445405353676284398705)
            ·
              refine ⟨33172084054015257213299029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44229445405353676284398705 33172084054015257213299029)
              ·
                refine ⟨97183840001997823867087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33172084054015257213299029 97183840001997823867087)
                ·
                  rfl

theorem cell23_5110151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 10].length) (baseStart_5110151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110151 prefixEnd_5110151 := by exact prefixLift 5110151
  have htrace : WordTrace (prefixWord ++ tailWord_5110151) baseStart_5110151 baseEnd_5110151 := by
    simpa [prefixWord, tailWord_5110151, baseEnd_5110151] using wordTrace_append hprefix tailTrace_5110151
  have hstable : (prefixWord ++ tailWord_5110151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110151).length < 2 ^ (prefixWord ++ tailWord_5110151).sum := by decide
  have hdescent : baseEnd_5110151 < baseStart_5110151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110168 : List Nat := [2, 1, 2, 5, 1, 2, 1, 9]
def baseStart_5110168 : Nat := 118140960795 + 5110168 * 2 ^ 59
def prefixEnd_5110168 : Nat := 4983230072969 + 3 ^ 40 * 5110168 * 2
def baseEnd_5110168 : Nat := 97184163304632136218473

theorem tailTrace_5110168 : CollatzResearch.WordTrace tailWord_5110168 prefixEnd_5110168 97184163304632136218473 := by
  unfold tailWord_5110168
  simp only [CollatzResearch.WordTrace]
  refine ⟨93191569475370779028277579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124255425967161038704370105 93191569475370779028277579)
  ·
    refine ⟨139787354213056168542416369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93191569475370779028277579 139787354213056168542416369)
    ·
      refine ⟨104840515659792126406812277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139787354213056168542416369 104840515659792126406812277)
      ·
        refine ⟨9828798343105511850638651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104840515659792126406812277 9828798343105511850638651)
        ·
          refine ⟨14743197514658267775957977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9828798343105511850638651 14743197514658267775957977)
          ·
            refine ⟨11057398135993700831968483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14743197514658267775957977 11057398135993700831968483)
            ·
              refine ⟨16586097203990551247952725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11057398135993700831968483 16586097203990551247952725)
              ·
                refine ⟨97184163304632136218473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16586097203990551247952725 97184163304632136218473)
                ·
                  rfl

theorem cell23_5110168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 9].length) (baseStart_5110168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110168 prefixEnd_5110168 := by exact prefixLift 5110168
  have htrace : WordTrace (prefixWord ++ tailWord_5110168) baseStart_5110168 baseEnd_5110168 := by
    simpa [prefixWord, tailWord_5110168, baseEnd_5110168] using wordTrace_append hprefix tailTrace_5110168
  have hstable : (prefixWord ++ tailWord_5110168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110168).length < 2 ^ (prefixWord ++ tailWord_5110168).sum := by decide
  have hdescent : baseEnd_5110168 < baseStart_5110168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110179 : List Nat := [1, 1, 1, 4, 1, 4, 3, 3, 1, 2, 2]
def baseStart_5110179 : Nat := 118140960795 + 5110179 * 2 ^ 59
def prefixEnd_5110179 : Nat := 4983230072969 + 3 ^ 40 * 5110179 * 2
def baseEnd_5110179 : Nat := 2623978057512267134861221

theorem tailTrace_5110179 : CollatzResearch.WordTrace tailWord_5110179 prefixEnd_5110179 2623978057512267134861221 := by
  unfold tailWord_5110179
  simp only [CollatzResearch.WordTrace]
  refine ⟨186383540153701706935205591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124255693435801137956803727 186383540153701706935205591)
  ·
    refine ⟨279575310230552560402808387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186383540153701706935205591 279575310230552560402808387)
    ·
      refine ⟨419362965345828840604212581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279575310230552560402808387 419362965345828840604212581)
      ·
        refine ⟨78630556002342907613289859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 419362965345828840604212581 78630556002342907613289859)
        ·
          refine ⟨117945834003514361419934789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78630556002342907613289859 117945834003514361419934789)
          ·
            refine ⟨22114843875658942766237773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117945834003514361419934789 22114843875658942766237773)
            ·
              refine ⟨8293066453372103537339165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22114843875658942766237773 8293066453372103537339165)
              ·
                refine ⟨3109899920014538826502187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8293066453372103537339165 3109899920014538826502187)
                ·
                  refine ⟨4664849880021808239753281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3109899920014538826502187 4664849880021808239753281)
                  ·
                    refine ⟨3498637410016356179814961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4664849880021808239753281 3498637410016356179814961)
                    ·
                      refine ⟨2623978057512267134861221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3498637410016356179814961 2623978057512267134861221)
                      ·
                        rfl

theorem cell23_5110179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_5110179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110179 prefixEnd_5110179 := by exact prefixLift 5110179
  have htrace : WordTrace (prefixWord ++ tailWord_5110179) baseStart_5110179 baseEnd_5110179 := by
    simpa [prefixWord, tailWord_5110179, baseEnd_5110179] using wordTrace_append hprefix tailTrace_5110179
  have hstable : (prefixWord ++ tailWord_5110179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110179).length < 2 ^ (prefixWord ++ tailWord_5110179).sum := by decide
  have hdescent : baseEnd_5110179 < baseStart_5110179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110211 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 1, 8]
def baseStart_5110211 : Nat := 118140960795 + 5110211 * 2 ^ 59
def prefixEnd_5110211 : Nat := 4983230072969 + 3 ^ 40 * 5110211 * 2
def baseEnd_5110211 : Nat := 874664829631070336553691

theorem tailTrace_5110211 : CollatzResearch.WordTrace tailWord_5110211 prefixEnd_5110211 874664829631070336553691 := by
  unfold tailWord_5110211
  simp only [CollatzResearch.WordTrace]
  refine ⟨186384707289585776400370487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124256471526390517600246991 186384707289585776400370487)
  ·
    refine ⟨279577060934378664600555731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186384707289585776400370487 279577060934378664600555731)
    ·
      refine ⟨419365591401567996900833597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279577060934378664600555731 419365591401567996900833597)
      ·
        refine ⟨157262096775587998837812599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 419365591401567996900833597 157262096775587998837812599)
        ·
          refine ⟨235893145163381998256718899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157262096775587998837812599 235893145163381998256718899)
          ·
            refine ⟨353839717745072997385078349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235893145163381998256718899 353839717745072997385078349)
            ·
              refine ⟨132689894154402374019404381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 353839717745072997385078349 132689894154402374019404381)
              ·
                refine ⟨49758710307900890257276643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132689894154402374019404381 49758710307900890257276643)
                ·
                  refine ⟨74638065461851335385914965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49758710307900890257276643 74638065461851335385914965)
                  ·
                    refine ⟨874664829631070336553691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74638065461851335385914965 874664829631070336553691)
                    ·
                      rfl

theorem cell23_5110211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 8].length) (baseStart_5110211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110211 prefixEnd_5110211 := by exact prefixLift 5110211
  have htrace : WordTrace (prefixWord ++ tailWord_5110211) baseStart_5110211 baseEnd_5110211 := by
    simpa [prefixWord, tailWord_5110211, baseEnd_5110211] using wordTrace_append hprefix tailTrace_5110211
  have hstable : (prefixWord ++ tailWord_5110211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110211).length < 2 ^ (prefixWord ++ tailWord_5110211).sum := by decide
  have hdescent : baseEnd_5110211 < baseStart_5110211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110239 : List Nat := [1, 1, 2, 3, 3, 3, 3, 1, 1, 3, 2]
def baseStart_5110239 : Nat := 118140960795 + 5110239 * 2 ^ 59
def prefixEnd_5110239 : Nat := 4983230072969 + 3 ^ 40 * 5110239 * 2
def baseEnd_5110239 : Nat := 2624008866351536900110945

theorem tailTrace_5110239 : CollatzResearch.WordTrace tailWord_5110239 prefixEnd_5110239 2624008866351536900110945 := by
  unfold tailWord_5110239
  simp only [CollatzResearch.WordTrace]
  refine ⟨186385728533484337182389771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124257152355656224788259847 186385728533484337182389771)
  ·
    refine ⟨279578592800226505773584657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186385728533484337182389771 279578592800226505773584657)
    ·
      refine ⟨209683944600169879330188493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279578592800226505773584657 209683944600169879330188493)
      ·
        refine ⟨78631479225063704748820685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209683944600169879330188493 78631479225063704748820685)
        ·
          refine ⟨29486804709398889280807757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78631479225063704748820685 29486804709398889280807757)
          ·
            refine ⟨11057551766024583480302909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29486804709398889280807757 11057551766024583480302909)
            ·
              refine ⟨4146581912259218805113591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11057551766024583480302909 4146581912259218805113591)
              ·
                refine ⟨6219872868388828207670387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4146581912259218805113591 6219872868388828207670387)
                ·
                  refine ⟨9329809302583242311505581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6219872868388828207670387 9329809302583242311505581)
                  ·
                    refine ⟨3498678488468715866814593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9329809302583242311505581 3498678488468715866814593)
                    ·
                      refine ⟨2624008866351536900110945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3498678488468715866814593 2624008866351536900110945)
                      ·
                        rfl

theorem cell23_5110239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_5110239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110239 prefixEnd_5110239 := by exact prefixLift 5110239
  have htrace : WordTrace (prefixWord ++ tailWord_5110239) baseStart_5110239 baseEnd_5110239 := by
    simpa [prefixWord, tailWord_5110239, baseEnd_5110239] using wordTrace_append hprefix tailTrace_5110239
  have hstable : (prefixWord ++ tailWord_5110239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110239).length < 2 ^ (prefixWord ++ tailWord_5110239).sum := by decide
  have hdescent : baseEnd_5110239 < baseStart_5110239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110298 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_5110298 : Nat := 118140960795 + 5110298 * 2 ^ 59
def prefixEnd_5110298 : Nat := 4983230072969 + 3 ^ 40 * 5110298 * 2
def baseEnd_5110298 : Nat := 2624039161710152169273173

theorem tailTrace_5110298 : CollatzResearch.WordTrace tailWord_5110298 prefixEnd_5110298 2624039161710152169273173 := by
  unfold tailWord_5110298
  simp only [CollatzResearch.WordTrace]
  refine ⟨46596970110067647564696887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124258586960180393505858365 46596970110067647564696887)
  ·
    refine ⟨69895455165101471347045331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46596970110067647564696887 69895455165101471347045331)
    ·
      refine ⟨104843182747652207020567997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69895455165101471347045331 104843182747652207020567997)
      ·
        refine ⟨39316193530369577632712999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104843182747652207020567997 39316193530369577632712999)
        ·
          refine ⟨58974290295554366449069499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39316193530369577632712999 58974290295554366449069499)
          ·
            refine ⟨88461435443331549673604249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58974290295554366449069499 88461435443331549673604249)
            ·
              refine ⟨66346076582498662255203187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88461435443331549673604249 66346076582498662255203187)
              ·
                refine ⟨99519114873747993382804781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66346076582498662255203187 99519114873747993382804781)
                ·
                  refine ⟨37319668077655497518551793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99519114873747993382804781 37319668077655497518551793)
                  ·
                    refine ⟨27989751058241623138913845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37319668077655497518551793 27989751058241623138913845)
                    ·
                      refine ⟨2624039161710152169273173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27989751058241623138913845 2624039161710152169273173)
                      ·
                        rfl

theorem cell23_5110298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_5110298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110298 prefixEnd_5110298 := by exact prefixLift 5110298
  have htrace : WordTrace (prefixWord ++ tailWord_5110298) baseStart_5110298 baseEnd_5110298 := by
    simpa [prefixWord, tailWord_5110298, baseEnd_5110298] using wordTrace_append hprefix tailTrace_5110298
  have hstable : (prefixWord ++ tailWord_5110298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110298).length < 2 ^ (prefixWord ++ tailWord_5110298).sum := by decide
  have hdescent : baseEnd_5110298 < baseStart_5110298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110335 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 3, 4]
def baseStart_5110335 : Nat := 118140960795 + 5110335 * 2 ^ 59
def prefixEnd_5110335 : Nat := 4983230072969 + 3 ^ 40 * 5110335 * 2
def baseEnd_5110335 : Nat := 874686053498122841503501

theorem tailTrace_5110335 : CollatzResearch.WordTrace tailWord_5110335 prefixEnd_5110335 874686053498122841503501 := by
  unfold tailWord_5110335
  simp only [CollatzResearch.WordTrace]
  refine ⟨186389229941136545577884459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124259486627424363718589639 186389229941136545577884459)
  ·
    refine ⟨279583844911704818366826689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186389229941136545577884459 279583844911704818366826689)
    ·
      refine ⟨209687883683778613775120017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279583844911704818366826689 209687883683778613775120017)
      ·
        refine ⟨157265912762833960331340013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209687883683778613775120017 157265912762833960331340013)
        ·
          refine ⟨58974717286062735124252505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157265912762833960331340013 58974717286062735124252505)
          ·
            refine ⟨44231037964547051343189379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58974717286062735124252505 44231037964547051343189379)
            ·
              refine ⟨66346556946820577014784069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44231037964547051343189379 66346556946820577014784069)
              ·
                refine ⟨12439979427528858190272013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66346556946820577014784069 12439979427528858190272013)
                ·
                  refine ⟨4664992285323321821352005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12439979427528858190272013 4664992285323321821352005)
                  ·
                    refine ⟨874686053498122841503501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4664992285323321821352005 874686053498122841503501)
                    ·
                      rfl

theorem cell23_5110335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 4].length) (baseStart_5110335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110335 prefixEnd_5110335 := by exact prefixLift 5110335
  have htrace : WordTrace (prefixWord ++ tailWord_5110335) baseStart_5110335 baseEnd_5110335 := by
    simpa [prefixWord, tailWord_5110335, baseEnd_5110335] using wordTrace_append hprefix tailTrace_5110335
  have hstable : (prefixWord ++ tailWord_5110335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110335).length < 2 ^ (prefixWord ++ tailWord_5110335).sum := by decide
  have hdescent : baseEnd_5110335 < baseStart_5110335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110348 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 10]
def baseStart_5110348 : Nat := 118140960795 + 5110348 * 2 ^ 59
def prefixEnd_5110348 : Nat := 4983230072969 + 3 ^ 40 * 5110348 * 2
def baseEnd_5110348 : Nat := 291562759526986330405327

theorem tailTrace_5110348 : CollatzResearch.WordTrace tailWord_5110348 prefixEnd_5110348 291562759526986330405327 := by
  unfold tailWord_5110348
  simp only [CollatzResearch.WordTrace]
  refine ⟨93194852045044724399053849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124259802726726299198738465 93194852045044724399053849)
  ·
    refine ⟨69896139033783543299290387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93194852045044724399053849 69896139033783543299290387)
    ·
      refine ⟨104844208550675314948935581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69896139033783543299290387 104844208550675314948935581)
      ·
        refine ⟨39316578206503243105850843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104844208550675314948935581 39316578206503243105850843)
        ·
          refine ⟨58974867309754864658776265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39316578206503243105850843 58974867309754864658776265)
          ·
            refine ⟨44231150482316148494082199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58974867309754864658776265 44231150482316148494082199)
            ·
              refine ⟨66346725723474222741123299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44231150482316148494082199 66346725723474222741123299)
              ·
                refine ⟨99520088585211334111684949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66346725723474222741123299 99520088585211334111684949)
                ·
                  refine ⟨291562759526986330405327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 99520088585211334111684949 291562759526986330405327)
                  ·
                    rfl

theorem cell23_5110348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_5110348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110348 prefixEnd_5110348 := by exact prefixLift 5110348
  have htrace : WordTrace (prefixWord ++ tailWord_5110348) baseStart_5110348 baseEnd_5110348 := by
    simpa [prefixWord, tailWord_5110348, baseEnd_5110348] using wordTrace_append hprefix tailTrace_5110348
  have hstable : (prefixWord ++ tailWord_5110348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110348).length < 2 ^ (prefixWord ++ tailWord_5110348).sum := by decide
  have hdescent : baseEnd_5110348 < baseStart_5110348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110352 : List Nat := [2, 1, 1, 1, 1, 3, 2, 7, 1, 4]
def baseStart_5110352 : Nat := 118140960795 + 5110352 * 2 ^ 59
def prefixEnd_5110352 : Nat := 4983230072969 + 3 ^ 40 * 5110352 * 2
def baseEnd_5110352 : Nat := 874688963221831652665975

theorem tailTrace_5110352 : CollatzResearch.WordTrace tailWord_5110352 prefixEnd_5110352 874688963221831652665975 := by
  unfold tailWord_5110352
  simp only [CollatzResearch.WordTrace]
  refine ⟨93194924991037478740626655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124259899988049971654168873 93194924991037478740626655)
  ·
    refine ⟨139792387486556218110939983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93194924991037478740626655 139792387486556218110939983)
    ·
      refine ⟨209688581229834327166409975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139792387486556218110939983 209688581229834327166409975)
      ·
        refine ⟨314532871844751490749614963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209688581229834327166409975 314532871844751490749614963)
        ·
          refine ⟨471799307767127236124422445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314532871844751490749614963 471799307767127236124422445)
          ·
            refine ⟨176924740412672713546658417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 471799307767127236124422445 176924740412672713546658417)
            ·
              refine ⟨132693555309504535159993813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176924740412672713546658417 132693555309504535159993813)
              ·
                refine ⟨3110005202566512542812355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 132693555309504535159993813 3110005202566512542812355)
                ·
                  refine ⟨4665007803849768814218533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110005202566512542812355 4665007803849768814218533)
                  ·
                    refine ⟨874688963221831652665975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4665007803849768814218533 874688963221831652665975)
                    ·
                      rfl

theorem cell23_5110352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 1, 4].length) (baseStart_5110352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110352 prefixEnd_5110352 := by exact prefixLift 5110352
  have htrace : WordTrace (prefixWord ++ tailWord_5110352) baseStart_5110352 baseEnd_5110352 := by
    simpa [prefixWord, tailWord_5110352, baseEnd_5110352] using wordTrace_append hprefix tailTrace_5110352
  have hstable : (prefixWord ++ tailWord_5110352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110352).length < 2 ^ (prefixWord ++ tailWord_5110352).sum := by decide
  have hdescent : baseEnd_5110352 < baseStart_5110352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110366 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_5110366 : Nat := 118140960795 + 5110366 * 2 ^ 59
def prefixEnd_5110366 : Nat := 4983230072969 + 3 ^ 40 * 5110366 * 2
def baseEnd_5110366 : Nat := 2624074078394657903222861

theorem tailTrace_5110366 : CollatzResearch.WordTrace tailWord_5110366 prefixEnd_5110366 2624074078394657903222861 := by
  unfold tailWord_5110366
  simp only [CollatzResearch.WordTrace]
  refine ⟨23298795075503029734032869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124260240402682825248175301 23298795075503029734032869)
  ·
    refine ⟨4368524076656818075131163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23298795075503029734032869 4368524076656818075131163)
    ·
      refine ⟨6552786114985227112696745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4368524076656818075131163 6552786114985227112696745)
      ·
        refine ⟨4914589586238920334522559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6552786114985227112696745 4914589586238920334522559)
        ·
          refine ⟨7371884379358380501783839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4914589586238920334522559 7371884379358380501783839)
          ·
            refine ⟨11057826569037570752675759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7371884379358380501783839 11057826569037570752675759)
            ·
              refine ⟨16586739853556356129013639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11057826569037570752675759 16586739853556356129013639)
              ·
                refine ⟨24880109780334534193520459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16586739853556356129013639 24880109780334534193520459)
                ·
                  refine ⟨37320164670501801290280689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24880109780334534193520459 37320164670501801290280689)
                  ·
                    refine ⟨27990123502876350967710517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37320164670501801290280689 27990123502876350967710517)
                    ·
                      refine ⟨2624074078394657903222861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27990123502876350967710517 2624074078394657903222861)
                      ·
                        rfl

theorem cell23_5110366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_5110366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110366 prefixEnd_5110366 := by exact prefixLift 5110366
  have htrace : WordTrace (prefixWord ++ tailWord_5110366) baseStart_5110366 baseEnd_5110366 := by
    simpa [prefixWord, tailWord_5110366, baseEnd_5110366] using wordTrace_append hprefix tailTrace_5110366
  have hstable : (prefixWord ++ tailWord_5110366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110366).length < 2 ^ (prefixWord ++ tailWord_5110366).sum := by decide
  have hdescent : baseEnd_5110366 < baseStart_5110366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110368 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 8]
def baseStart_5110368 : Nat := 118140960795 + 5110368 * 2 ^ 59
def prefixEnd_5110368 : Nat := 4983230072969 + 3 ^ 40 * 5110368 * 2
def baseEnd_5110368 : Nat := 2624075105355966895397851

theorem tailTrace_5110368 : CollatzResearch.WordTrace tailWord_5110368 prefixEnd_5110368 2624075105355966895397851 := by
  unfold tailWord_5110368
  simp only [CollatzResearch.WordTrace]
  refine ⟨93195216775008496106917879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124260289033344661475890505 93195216775008496106917879)
  ·
    refine ⟨139792825162512744160376819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93195216775008496106917879 139792825162512744160376819)
    ·
      refine ⟨209689237743769116240565229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139792825162512744160376819 209689237743769116240565229)
      ·
        refine ⟨78633464153913418590211961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209689237743769116240565229 78633464153913418590211961)
        ·
          refine ⟨58975098115435063942658971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78633464153913418590211961 58975098115435063942658971)
          ·
            refine ⟨88462647173152595913988457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58975098115435063942658971 88462647173152595913988457)
            ·
              refine ⟨66346985379864446935491343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88462647173152595913988457 66346985379864446935491343)
              ·
                refine ⟨99520478069796670403237015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66346985379864446935491343 99520478069796670403237015)
                ·
                  refine ⟨149280717104695005604855523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99520478069796670403237015 149280717104695005604855523)
                  ·
                    refine ⟨223921075657042508407283285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 149280717104695005604855523 223921075657042508407283285)
                    ·
                      refine ⟨2624075105355966895397851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 223921075657042508407283285 2624075105355966895397851)
                      ·
                        rfl

theorem cell23_5110368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_5110368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110368 prefixEnd_5110368 := by exact prefixLift 5110368
  have htrace : WordTrace (prefixWord ++ tailWord_5110368) baseStart_5110368 baseEnd_5110368 := by
    simpa [prefixWord, tailWord_5110368, baseEnd_5110368] using wordTrace_append hprefix tailTrace_5110368
  have hstable : (prefixWord ++ tailWord_5110368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110368).length < 2 ^ (prefixWord ++ tailWord_5110368).sum := by decide
  have hdescent : baseEnd_5110368 < baseStart_5110368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110382 : List Nat := [4, 1, 2, 2, 2, 2, 1, 3, 6]
def baseStart_5110382 : Nat := 118140960795 + 5110382 * 2 ^ 59
def prefixEnd_5110382 : Nat := 4983230072969 + 3 ^ 40 * 5110382 * 2
def baseEnd_5110382 : Nat := 291564699342792204513643

theorem tailTrace_5110382 : CollatzResearch.WordTrace tailWord_5110382 prefixEnd_5110382 291564699342792204513643 := by
  unfold tailWord_5110382
  simp only [CollatzResearch.WordTrace]
  refine ⟨23298868021495784075605675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124260629447977515069896933 23298868021495784075605675)
  ·
    refine ⟨34948302032243676113408513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23298868021495784075605675 34948302032243676113408513)
    ·
      refine ⟨26211226524182757085056385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34948302032243676113408513 26211226524182757085056385)
      ·
        refine ⟨19658419893137067813792289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26211226524182757085056385 19658419893137067813792289)
        ·
          refine ⟨14743814919852800860344217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19658419893137067813792289 14743814919852800860344217)
          ·
            refine ⟨11057861189889600645258163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14743814919852800860344217 11057861189889600645258163)
            ·
              refine ⟨16586791784834400967887245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11057861189889600645258163 16586791784834400967887245)
              ·
                refine ⟨6220046919312900362957717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16586791784834400967887245 6220046919312900362957717)
                ·
                  refine ⟨291564699342792204513643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6220046919312900362957717 291564699342792204513643)
                  ·
                    rfl

theorem cell23_5110382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_5110382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110382 prefixEnd_5110382 := by exact prefixLift 5110382
  have htrace : WordTrace (prefixWord ++ tailWord_5110382) baseStart_5110382 baseEnd_5110382 := by
    simpa [prefixWord, tailWord_5110382, baseEnd_5110382] using wordTrace_append hprefix tailTrace_5110382
  have hstable : (prefixWord ++ tailWord_5110382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110382).length < 2 ^ (prefixWord ++ tailWord_5110382).sum := by decide
  have hdescent : baseEnd_5110382 < baseStart_5110382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110395 : List Nat := [1, 1, 1, 1, 1, 4, 2, 6, 1, 5]
def baseStart_5110395 : Nat := 118140960795 + 5110395 * 2 ^ 59
def prefixEnd_5110395 : Nat := 4983230072969 + 3 ^ 40 * 5110395 * 2
def baseEnd_5110395 : Nat := 874696323111212763253409

theorem tailTrace_5110395 : CollatzResearch.WordTrace tailWord_5110395 prefixEnd_5110395 874696323111212763253409 := by
  unfold tailWord_5110395
  simp only [CollatzResearch.WordTrace]
  refine ⟨186391418320919175825068639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124260945547279450550045759 186391418320919175825068639)
  ·
    refine ⟨279587127481378763737602959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186391418320919175825068639 279587127481378763737602959)
    ·
      refine ⟨419380691222068145606404439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279587127481378763737602959 419380691222068145606404439)
      ·
        refine ⟨629071036833102218409606659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419380691222068145606404439 629071036833102218409606659)
        ·
          refine ⟨943606555249653327614409989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629071036833102218409606659 943606555249653327614409989)
          ·
            refine ⟨176926229109309998927701873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 943606555249653327614409989 176926229109309998927701873)
            ·
              refine ⟨132694671831982499195776405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176926229109309998927701873 132694671831982499195776405)
              ·
                refine ⟨6220062742124179649802019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132694671831982499195776405 6220062742124179649802019)
                ·
                  refine ⟨9330094113186269474703029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6220062742124179649802019 9330094113186269474703029)
                  ·
                    refine ⟨874696323111212763253409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9330094113186269474703029 874696323111212763253409)
                    ·
                      rfl

theorem cell23_5110395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 5].length) (baseStart_5110395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110395 prefixEnd_5110395 := by exact prefixLift 5110395
  have htrace : WordTrace (prefixWord ++ tailWord_5110395) baseStart_5110395 baseEnd_5110395 := by
    simpa [prefixWord, tailWord_5110395, baseEnd_5110395] using wordTrace_append hprefix tailTrace_5110395
  have hstable : (prefixWord ++ tailWord_5110395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110395).length < 2 ^ (prefixWord ++ tailWord_5110395).sum := by decide
  have hdescent : baseEnd_5110395 < baseStart_5110395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110409 : List Nat := [1, 2, 1, 1, 4, 1, 1, 7, 1, 1, 3]
def baseStart_5110409 : Nat := 118140960795 + 5110409 * 2 ^ 59
def prefixEnd_5110409 : Nat := 4983230072969 + 3 ^ 40 * 5110409 * 2
def baseEnd_5110409 : Nat := 2624096158062801234985163

theorem tailTrace_5110409 : CollatzResearch.WordTrace tailWord_5110409 prefixEnd_5110409 2624096158062801234985163 := by
  unfold tailWord_5110409
  simp only [CollatzResearch.WordTrace]
  refine ⟨186391928942868456216078281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124261285961912304144052187 186391928942868456216078281)
  ·
    refine ⟨139793946707151342162058711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186391928942868456216078281 139793946707151342162058711)
    ·
      refine ⟨209690920060727013243088067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139793946707151342162058711 209690920060727013243088067)
      ·
        refine ⟨314536380091090519864632101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209690920060727013243088067 314536380091090519864632101)
        ·
          refine ⟨58975571267079472474618519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 314536380091090519864632101 58975571267079472474618519)
          ·
            refine ⟨88463356900619208711927779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58975571267079472474618519 88463356900619208711927779)
            ·
              refine ⟨132695035350928813067891669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88463356900619208711927779 132695035350928813067891669)
              ·
                refine ⟨3110039891037394056278711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 132695035350928813067891669 3110039891037394056278711)
                ·
                  refine ⟨4665059836556091084418067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110039891037394056278711 4665059836556091084418067)
                  ·
                    refine ⟨6997589754834136626627101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4665059836556091084418067 6997589754834136626627101)
                    ·
                      refine ⟨2624096158062801234985163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6997589754834136626627101 2624096158062801234985163)
                      ·
                        rfl

theorem cell23_5110409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 1, 1, 3].length) (baseStart_5110409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110409 prefixEnd_5110409 := by exact prefixLift 5110409
  have htrace : WordTrace (prefixWord ++ tailWord_5110409) baseStart_5110409 baseEnd_5110409 := by
    simpa [prefixWord, tailWord_5110409, baseEnd_5110409] using wordTrace_append hprefix tailTrace_5110409
  have hstable : (prefixWord ++ tailWord_5110409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110409).length < 2 ^ (prefixWord ++ tailWord_5110409).sum := by decide
  have hdescent : baseEnd_5110409 < baseStart_5110409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110462 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_5110462 : Nat := 118140960795 + 5110462 * 2 ^ 59
def prefixEnd_5110462 : Nat := 4983230072969 + 3 ^ 40 * 5110462 * 2
def baseEnd_5110462 : Nat := 2624123372537489527622419

theorem tailTrace_5110462 : CollatzResearch.WordTrace tailWord_5110462 prefixEnd_5110462 2624123372537489527622419 := by
  unfold tailWord_5110462
  simp only [CollatzResearch.WordTrace]
  refine ⟨23299232751459555783469705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124262574674450964178505093 23299232751459555783469705)
  ·
    refine ⟨17474424563594666837602279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23299232751459555783469705 17474424563594666837602279)
    ·
      refine ⟨26211636845392000256403419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17474424563594666837602279 26211636845392000256403419)
      ·
        refine ⟨39317455268088000384605129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26211636845392000256403419 39317455268088000384605129)
        ·
          refine ⟨29488091451066000288453847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39317455268088000384605129 29488091451066000288453847)
          ·
            refine ⟨44232137176599000432680771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29488091451066000288453847 44232137176599000432680771)
            ·
              refine ⟨66348205764898500649021157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44232137176599000432680771 66348205764898500649021157)
              ·
                refine ⟨12440288580918468871691467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66348205764898500649021157 12440288580918468871691467)
                ·
                  refine ⟨18660432871377703307537201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12440288580918468871691467 18660432871377703307537201)
                  ·
                    refine ⟨13995324653533277480652901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18660432871377703307537201 13995324653533277480652901)
                    ·
                      refine ⟨2624123372537489527622419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13995324653533277480652901 2624123372537489527622419)
                      ·
                        rfl

theorem cell23_5110462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_5110462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110462 prefixEnd_5110462 := by exact prefixLift 5110462
  have htrace : WordTrace (prefixWord ++ tailWord_5110462) baseStart_5110462 baseEnd_5110462 := by
    simpa [prefixWord, tailWord_5110462, baseEnd_5110462] using wordTrace_append hprefix tailTrace_5110462
  have hstable : (prefixWord ++ tailWord_5110462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110462).length < 2 ^ (prefixWord ++ tailWord_5110462).sum := by decide
  have hdescent : baseEnd_5110462 < baseStart_5110462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110476 : List Nat := [2, 2, 1, 5, 1, 3, 1, 2, 2, 4]
def baseStart_5110476 : Nat := 118140960795 + 5110476 * 2 ^ 59
def prefixEnd_5110476 : Nat := 4983230072969 + 3 ^ 40 * 5110476 * 2
def baseEnd_5110476 : Nat := 874710187088884157615785

theorem tailTrace_5110476 : CollatzResearch.WordTrace tailWord_5110476 prefixEnd_5110476 874710187088884157615785 := by
  unfold tailWord_5110476
  simp only [CollatzResearch.WordTrace]
  refine ⟨93197186316812863329383641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124262915089083817772511521 93197186316812863329383641)
  ·
    refine ⟨69897889737609647497037731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93197186316812863329383641 69897889737609647497037731)
    ·
      refine ⟨104846834606414471245556597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69897889737609647497037731 104846834606414471245556597)
      ·
        refine ⟨9829390744351356679270931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104846834606414471245556597 9829390744351356679270931)
        ·
          refine ⟨14744086116527035018906397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9829390744351356679270931 14744086116527035018906397)
          ·
            refine ⟨5529032293697638132089899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14744086116527035018906397 5529032293697638132089899)
            ·
              refine ⟨8293548440546457198134849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5529032293697638132089899 8293548440546457198134849)
              ·
                refine ⟨6220161330409842898601137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8293548440546457198134849 6220161330409842898601137)
                ·
                  refine ⟨4665120997807382173950853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6220161330409842898601137 4665120997807382173950853)
                  ·
                    refine ⟨874710187088884157615785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4665120997807382173950853 874710187088884157615785)
                    ·
                      rfl

theorem cell23_5110476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_5110476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110476 prefixEnd_5110476 := by exact prefixLift 5110476
  have htrace : WordTrace (prefixWord ++ tailWord_5110476) baseStart_5110476 baseEnd_5110476 := by
    simpa [prefixWord, tailWord_5110476, baseEnd_5110476] using wordTrace_append hprefix tailTrace_5110476
  have hstable : (prefixWord ++ tailWord_5110476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110476).length < 2 ^ (prefixWord ++ tailWord_5110476).sum := by decide
  have hdescent : baseEnd_5110476 < baseStart_5110476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110499 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 3]
def baseStart_5110499 : Nat := 118140960795 + 5110499 * 2 ^ 59
def prefixEnd_5110499 : Nat := 4983230072969 + 3 ^ 40 * 5110499 * 2
def baseEnd_5110499 : Nat := 2624142371321705882859749

theorem tailTrace_5110499 : CollatzResearch.WordTrace tailWord_5110499 prefixEnd_5110499 2624142371321705882859749 := by
  unfold tailWord_5110499
  simp only [CollatzResearch.WordTrace]
  refine ⟨186395211512542401586854551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124263474341694934391236367 186395211512542401586854551)
  ·
    refine ⟨279592817268813602380281827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186395211512542401586854551 279592817268813602380281827)
    ·
      refine ⟨419389225903220403570422741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279592817268813602380281827 419389225903220403570422741)
      ·
        refine ⟨9829434982106728208681783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 419389225903220403570422741 9829434982106728208681783)
        ·
          refine ⟨14744152473160092313022675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9829434982106728208681783 14744152473160092313022675)
          ·
            refine ⟨22116228709740138469534013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14744152473160092313022675 22116228709740138469534013)
            ·
              refine ⟨8293585766152551926075255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22116228709740138469534013 8293585766152551926075255)
              ·
                refine ⟨12440378649228827889112883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8293585766152551926075255 12440378649228827889112883)
                ·
                  refine ⟨18660567973843241833669325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12440378649228827889112883 18660567973843241833669325)
                  ·
                    refine ⟨6997712990191215687625997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18660567973843241833669325 6997712990191215687625997)
                    ·
                      refine ⟨2624142371321705882859749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6997712990191215687625997 2624142371321705882859749)
                      ·
                        rfl

theorem cell23_5110499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_5110499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110499 prefixEnd_5110499 := by exact prefixLift 5110499
  have htrace : WordTrace (prefixWord ++ tailWord_5110499) baseStart_5110499 baseEnd_5110499 := by
    simpa [prefixWord, tailWord_5110499, baseEnd_5110499] using wordTrace_append hprefix tailTrace_5110499
  have hstable : (prefixWord ++ tailWord_5110499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110499).length < 2 ^ (prefixWord ++ tailWord_5110499).sum := by decide
  have hdescent : baseEnd_5110499 < baseStart_5110499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110505 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 2, 3, 4]
def baseStart_5110505 : Nat := 118140960795 + 5110505 * 2 ^ 59
def prefixEnd_5110505 : Nat := 4983230072969 + 3 ^ 40 * 5110505 * 2
def baseEnd_5110505 : Nat := 2624145452205632859384721

theorem tailTrace_5110505 : CollatzResearch.WordTrace tailWord_5110505 prefixEnd_5110505 2624145452205632859384721 := by
  unfold tailWord_5110505
  simp only [CollatzResearch.WordTrace]
  refine ⟨186395430350520664611572969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124263620233680443074381979 186395430350520664611572969)
  ·
    refine ⟨139796572762890498458679727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186395430350520664611572969 139796572762890498458679727)
    ·
      refine ⟨209694859144335747688019591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139796572762890498458679727 209694859144335747688019591)
      ·
        refine ⟨314542288716503621532029387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209694859144335747688019591 314542288716503621532029387)
        ·
          refine ⟨471813433074755432298044081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314542288716503621532029387 471813433074755432298044081)
          ·
            refine ⟨353860074806066574223533061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471813433074755432298044081 353860074806066574223533061)
            ·
              refine ⟨66348764026137482666912449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 353860074806066574223533061 66348764026137482666912449)
              ·
                refine ⟨49761573019603112000184337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66348764026137482666912449 49761573019603112000184337)
                ·
                  refine ⟨37321179764702334000138253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49761573019603112000184337 37321179764702334000138253)
                  ·
                    refine ⟨13995442411763375250051845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37321179764702334000138253 13995442411763375250051845)
                    ·
                      refine ⟨2624145452205632859384721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13995442411763375250051845 2624145452205632859384721)
                      ·
                        rfl

theorem cell23_5110505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_5110505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110505 prefixEnd_5110505 := by exact prefixLift 5110505
  have htrace : WordTrace (prefixWord ++ tailWord_5110505) baseStart_5110505 baseEnd_5110505 := by
    simpa [prefixWord, tailWord_5110505, baseEnd_5110505] using wordTrace_append hprefix tailTrace_5110505
  have hstable : (prefixWord ++ tailWord_5110505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110505).length < 2 ^ (prefixWord ++ tailWord_5110505).sum := by decide
  have hdescent : baseEnd_5110505 < baseStart_5110505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110542 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_5110542 : Nat := 118140960795 + 5110542 * 2 ^ 59
def prefixEnd_5110542 : Nat := 4983230072969 + 3 ^ 40 * 5110542 * 2
def baseEnd_5110542 : Nat := 2624164450989849214622051

theorem tailTrace_5110542 : CollatzResearch.WordTrace tailWord_5110542 prefixEnd_5110542 2624164450989849214622051 := by
  unfold tailWord_5110542
  simp only [CollatzResearch.WordTrace]
  refine ⟨23299597481423327491333735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124264519900924413287113253 23299597481423327491333735)
  ·
    refine ⟨34949396222134991237000603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23299597481423327491333735 34949396222134991237000603)
    ·
      refine ⟨52424094333202486855500905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34949396222134991237000603 52424094333202486855500905)
      ·
        refine ⟨39318070749901865141625679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52424094333202486855500905 39318070749901865141625679)
        ·
          refine ⟨58977106124852797712438519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39318070749901865141625679 58977106124852797712438519)
          ·
            refine ⟨88465659187279196568657779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58977106124852797712438519 88465659187279196568657779)
            ·
              refine ⟨132698488780918794852986669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88465659187279196568657779 132698488780918794852986669)
              ·
                refine ⟨49761933292844548069870001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132698488780918794852986669 49761933292844548069870001)
                ·
                  refine ⟨37321449969633411052402501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49761933292844548069870001 37321449969633411052402501)
                  ·
                    refine ⟨6997771869306264572325469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37321449969633411052402501 6997771869306264572325469)
                    ·
                      refine ⟨2624164450989849214622051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6997771869306264572325469 2624164450989849214622051)
                      ·
                        rfl

theorem cell23_5110542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_5110542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110542 prefixEnd_5110542 := by exact prefixLift 5110542
  have htrace : WordTrace (prefixWord ++ tailWord_5110542) baseStart_5110542 baseEnd_5110542 := by
    simpa [prefixWord, tailWord_5110542, baseEnd_5110542] using wordTrace_append hprefix tailTrace_5110542
  have hstable : (prefixWord ++ tailWord_5110542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110542).length < 2 ^ (prefixWord ++ tailWord_5110542).sum := by decide
  have hdescent : baseEnd_5110542 < baseStart_5110542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110590 : List Nat := [4, 2, 1, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_5110590 : Nat := 118140960795 + 5110590 * 2 ^ 59
def prefixEnd_5110590 : Nat := 4983230072969 + 3 ^ 40 * 5110590 * 2
def baseEnd_5110590 : Nat := 2624189098061265026821831

theorem tailTrace_5110590 : CollatzResearch.WordTrace tailWord_5110590 prefixEnd_5110590 2624189098061265026821831 := by
  unfold tailWord_5110590
  simp only [CollatzResearch.WordTrace]
  refine ⟨23299816319401590516052153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124265687036808482752278149 23299816319401590516052153)
  ·
    refine ⟨17474862239551192887039115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23299816319401590516052153 17474862239551192887039115)
    ·
      refine ⟨26212293359326789330558673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17474862239551192887039115 26212293359326789330558673)
      ·
        refine ⟨19659220019495091997919005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26212293359326789330558673 19659220019495091997919005)
        ·
          refine ⟨7372207507310659499219627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19659220019495091997919005 7372207507310659499219627)
          ·
            refine ⟨11058311260965989248829441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7372207507310659499219627 11058311260965989248829441)
            ·
              refine ⟨8293733445724491936622081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11058311260965989248829441 8293733445724491936622081)
              ·
                refine ⟨6220300084293368952466561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8293733445724491936622081 6220300084293368952466561)
                ·
                  refine ⟨4665225063220026714349921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6220300084293368952466561 4665225063220026714349921)
                  ·
                    refine ⟨3498918797415020035762441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4665225063220026714349921 3498918797415020035762441)
                    ·
                      refine ⟨2624189098061265026821831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3498918797415020035762441 2624189098061265026821831)
                      ·
                        rfl

theorem cell23_5110590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_5110590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110590 prefixEnd_5110590 := by exact prefixLift 5110590
  have htrace : WordTrace (prefixWord ++ tailWord_5110590) baseStart_5110590 baseEnd_5110590 := by
    simpa [prefixWord, tailWord_5110590, baseEnd_5110590] using wordTrace_append hprefix tailTrace_5110590
  have hstable : (prefixWord ++ tailWord_5110590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110590).length < 2 ^ (prefixWord ++ tailWord_5110590).sum := by decide
  have hdescent : baseEnd_5110590 < baseStart_5110590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110629 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 2, 1, 4]
def baseStart_5110629 : Nat := 118140960795 + 5110629 * 2 ^ 59
def prefixEnd_5110629 : Nat := 4983230072969 + 3 ^ 40 * 5110629 * 2
def baseEnd_5110629 : Nat := 2624209123806790374234151

theorem tailTrace_5110629 : CollatzResearch.WordTrace tailWord_5110629 prefixEnd_5110629 2624209123806790374234151 := by
  unfold tailWord_5110629
  simp only [CollatzResearch.WordTrace]
  refine ⟨186399953002071433789086941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124266635334714289192724627 186399953002071433789086941)
  ·
    refine ⟨69899982375776787670907603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186399953002071433789086941 69899982375776787670907603)
    ·
      refine ⟨104849973563665181506361405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69899982375776787670907603 104849973563665181506361405)
      ·
        refine ⟨39318740086374443064885527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104849973563665181506361405 39318740086374443064885527)
        ·
          refine ⟨58978110129561664597328291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39318740086374443064885527 58978110129561664597328291)
          ·
            refine ⟨88467165194342496895992437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58978110129561664597328291 88467165194342496895992437)
            ·
              refine ⟨8293796736969609083999291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88467165194342496895992437 8293796736969609083999291)
              ·
                refine ⟨12440695105454413625998937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8293796736969609083999291 12440695105454413625998937)
                ·
                  refine ⟨9330521329090810219499203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12440695105454413625998937 9330521329090810219499203)
                  ·
                    refine ⟨13995781993636215329248805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9330521329090810219499203 13995781993636215329248805)
                    ·
                      refine ⟨2624209123806790374234151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13995781993636215329248805 2624209123806790374234151)
                      ·
                        rfl

theorem cell23_5110629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_5110629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110629 prefixEnd_5110629 := by exact prefixLift 5110629
  have htrace : WordTrace (prefixWord ++ tailWord_5110629) baseStart_5110629 baseEnd_5110629 := by
    simpa [prefixWord, tailWord_5110629, baseEnd_5110629] using wordTrace_append hprefix tailTrace_5110629
  have hstable : (prefixWord ++ tailWord_5110629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110629).length < 2 ^ (prefixWord ++ tailWord_5110629).sum := by decide
  have hdescent : baseEnd_5110629 < baseStart_5110629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110642 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_5110642 : Nat := 118140960795 + 5110642 * 2 ^ 59
def prefixEnd_5110642 : Nat := 4983230072969 + 3 ^ 40 * 5110642 * 2
def baseEnd_5110642 : Nat := 2624215799055298823371591

theorem tailTrace_5110642 : CollatzResearch.WordTrace tailWord_5110642 prefixEnd_5110642 2624215799055298823371591 := by
  unfold tailWord_5110642
  simp only [CollatzResearch.WordTrace]
  refine ⟨46600106787756084252327545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124266951434016224672873453 46600106787756084252327545)
  ·
    refine ⟨34950080090817063189245659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46600106787756084252327545 34950080090817063189245659)
    ·
      refine ⟨52425120136225594783868489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34950080090817063189245659 52425120136225594783868489)
      ·
        refine ⟨39318840102169196087901367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52425120136225594783868489 39318840102169196087901367)
        ·
          refine ⟨58978260153253794131852051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39318840102169196087901367 58978260153253794131852051)
          ·
            refine ⟨88467390229880691197778077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58978260153253794131852051 88467390229880691197778077)
            ·
              refine ⟨33175271336205259199166779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88467390229880691197778077 33175271336205259199166779)
              ·
                refine ⟨49762907004307888798750169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33175271336205259199166779 49762907004307888798750169)
                ·
                  refine ⟨37322180253230916599062627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49762907004307888798750169 37322180253230916599062627)
                  ·
                    refine ⟨55983270379846374898593941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37322180253230916599062627 55983270379846374898593941)
                    ·
                      refine ⟨2624215799055298823371591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55983270379846374898593941 2624215799055298823371591)
                      ·
                        rfl

theorem cell23_5110642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_5110642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110642 prefixEnd_5110642 := by exact prefixLift 5110642
  have htrace : WordTrace (prefixWord ++ tailWord_5110642) baseStart_5110642 baseEnd_5110642 := by
    simpa [prefixWord, tailWord_5110642, baseEnd_5110642] using wordTrace_append hprefix tailTrace_5110642
  have hstable : (prefixWord ++ tailWord_5110642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110642).length < 2 ^ (prefixWord ++ tailWord_5110642).sum := by decide
  have hdescent : baseEnd_5110642 < baseStart_5110642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110690 : List Nat := [3, 3, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_5110690 : Nat := 118140960795 + 5110690 * 2 ^ 59
def prefixEnd_5110690 : Nat := 4983230072969 + 3 ^ 40 * 5110690 * 2
def baseEnd_5110690 : Nat := 874746815375571545190457

theorem tailTrace_5110690 : CollatzResearch.WordTrace tailWord_5110690 prefixEnd_5110690 874746815375571545190457 := by
  unfold tailWord_5110690
  simp only [CollatzResearch.WordTrace]
  refine ⟨46600544463712610301764381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124268118569900294138038349 46600544463712610301764381)
  ·
    refine ⟨17475204173892228863161643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46600544463712610301764381 17475204173892228863161643)
    ·
      refine ⟨26212806260838343294742465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17475204173892228863161643 26212806260838343294742465)
      ·
        refine ⟨19659604695628757471056849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26212806260838343294742465 19659604695628757471056849)
        ·
          refine ⟨14744703521721568103292637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19659604695628757471056849 14744703521721568103292637)
          ·
            refine ⟨5529263820645588038734739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14744703521721568103292637 5529263820645588038734739)
            ·
              refine ⟨8293895730968382058102109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5529263820645588038734739 8293895730968382058102109)
              ·
                refine ⟨3110210899113143271788291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8293895730968382058102109 3110210899113143271788291)
                ·
                  refine ⟨4665316348669714907682437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110210899113143271788291 4665316348669714907682437)
                  ·
                    refine ⟨874746815375571545190457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4665316348669714907682437 874746815375571545190457)
                    ·
                      rfl

theorem cell23_5110690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_5110690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110690 prefixEnd_5110690 := by exact prefixLift 5110690
  have htrace : WordTrace (prefixWord ++ tailWord_5110690) baseStart_5110690 baseEnd_5110690 := by
    simpa [prefixWord, tailWord_5110690, baseEnd_5110690] using wordTrace_append hprefix tailTrace_5110690
  have hstable : (prefixWord ++ tailWord_5110690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110690).length < 2 ^ (prefixWord ++ tailWord_5110690).sum := by decide
  have hdescent : baseEnd_5110690 < baseStart_5110690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110713 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 3, 1, 3]
def baseStart_5110713 : Nat := 118140960795 + 5110713 * 2 ^ 59
def prefixEnd_5110713 : Nat := 4983230072969 + 3 ^ 40 * 5110713 * 2
def baseEnd_5110713 : Nat := 2624252256181768045583765

theorem tailTrace_5110713 : CollatzResearch.WordTrace tailWord_5110713 prefixEnd_5110713 2624252256181768045583765 := by
  unfold tailWord_5110713
  simp only [CollatzResearch.WordTrace]
  refine ⟨186403016733767116135144793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124268677822511410756763195 186403016733767116135144793)
  ·
    refine ⟨139802262550325337101358595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186403016733767116135144793 139802262550325337101358595)
    ·
      refine ⟨209703393825488005652037893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139802262550325337101358595 209703393825488005652037893)
      ·
        refine ⟨39319386342279001059757105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209703393825488005652037893 39319386342279001059757105)
        ·
          refine ⟨29489539756709250794817829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39319386342279001059757105 29489539756709250794817829)
          ·
            refine ⟨5529288704382984524028343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29489539756709250794817829 5529288704382984524028343)
            ·
              refine ⟨8293933056574476786042515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5529288704382984524028343 8293933056574476786042515)
              ·
                refine ⟨12440899584861715179063773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8293933056574476786042515 12440899584861715179063773)
                ·
                  refine ⟨4665337344323143192148915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12440899584861715179063773 4665337344323143192148915)
                  ·
                    refine ⟨6998006016484714788223373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4665337344323143192148915 6998006016484714788223373)
                    ·
                      refine ⟨2624252256181768045583765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6998006016484714788223373 2624252256181768045583765)
                      ·
                        rfl

theorem cell23_5110713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_5110713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110713 prefixEnd_5110713 := by exact prefixLift 5110713
  have htrace : WordTrace (prefixWord ++ tailWord_5110713) baseStart_5110713 baseEnd_5110713 := by
    simpa [prefixWord, tailWord_5110713, baseEnd_5110713] using wordTrace_append hprefix tailTrace_5110713
  have hstable : (prefixWord ++ tailWord_5110713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110713).length < 2 ^ (prefixWord ++ tailWord_5110713).sum := by decide
  have hdescent : baseEnd_5110713 < baseStart_5110713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110719 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 2, 6, 2]
def baseStart_5110719 : Nat := 118140960795 + 5110719 * 2 ^ 59
def prefixEnd_5110719 : Nat := 4983230072969 + 3 ^ 40 * 5110719 * 2
def baseEnd_5110719 : Nat := 2624255337065695022108737

theorem tailTrace_5110719 : CollatzResearch.WordTrace tailWord_5110719 prefixEnd_5110719 2624255337065695022108737 := by
  unfold tailWord_5110719
  simp only [CollatzResearch.WordTrace]
  refine ⟨186403235571745379159863211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124268823714496919439908807 186403235571745379159863211)
  ·
    refine ⟨279604853357618068739794817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186403235571745379159863211 279604853357618068739794817)
    ·
      refine ⟨209703640018213551554846113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279604853357618068739794817 209703640018213551554846113)
      ·
        refine ⟨157277730013660163666134585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209703640018213551554846113 157277730013660163666134585)
        ·
          refine ⟨117958297510245122749600939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157277730013660163666134585 117958297510245122749600939)
          ·
            refine ⟨176937446265367684124401409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117958297510245122749600939 176937446265367684124401409)
            ·
              refine ⟨132703084699025763093301057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176937446265367684124401409 132703084699025763093301057)
              ·
                refine ⟨99527313524269322319975793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132703084699025763093301057 99527313524269322319975793)
                ·
                  refine ⟨74645485143201991739981845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99527313524269322319975793 74645485143201991739981845)
                  ·
                    refine ⟨3499007116087593362811649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74645485143201991739981845 3499007116087593362811649)
                    ·
                      refine ⟨2624255337065695022108737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499007116087593362811649 2624255337065695022108737)
                      ·
                        rfl

theorem cell23_5110719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 6, 2].length) (baseStart_5110719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110719 prefixEnd_5110719 := by exact prefixLift 5110719
  have htrace : WordTrace (prefixWord ++ tailWord_5110719) baseStart_5110719 baseEnd_5110719 := by
    simpa [prefixWord, tailWord_5110719, baseEnd_5110719] using wordTrace_append hprefix tailTrace_5110719
  have hstable : (prefixWord ++ tailWord_5110719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110719).length < 2 ^ (prefixWord ++ tailWord_5110719).sum := by decide
  have hdescent : baseEnd_5110719 < baseStart_5110719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110736 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 5, 2, 2]
def baseStart_5110736 : Nat := 118140960795 + 5110736 * 2 ^ 59
def prefixEnd_5110736 : Nat := 4983230072969 + 3 ^ 40 * 5110736 * 2
def baseEnd_5110736 : Nat := 2624264066236821455596159

theorem tailTrace_5110736 : CollatzResearch.WordTrace tailWord_5110736 prefixEnd_5110736 2624264066236821455596159 := by
  unfold tailWord_5110736
  simp only [CollatzResearch.WordTrace]
  refine ⟨93201927806341895531616031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124269237075122527375488041 93201927806341895531616031)
  ·
    refine ⟨139802891709512843297424047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93201927806341895531616031 139802891709512843297424047)
    ·
      refine ⟨209704337564269264946136071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139802891709512843297424047 209704337564269264946136071)
      ·
        refine ⟨314556506346403897419204107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209704337564269264946136071 314556506346403897419204107)
        ·
          refine ⟨471834759519605846128806161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314556506346403897419204107 471834759519605846128806161)
          ·
            refine ⟨353876069639704384596604621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471834759519605846128806161 353876069639704384596604621)
            ·
              refine ⟨132703526114889144223726733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 353876069639704384596604621 132703526114889144223726733)
              ·
                refine ⟨49763822293083429083897525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132703526114889144223726733 49763822293083429083897525)
                ·
                  refine ⟨4665358339976571476615393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49763822293083429083897525 4665358339976571476615393)
                  ·
                    refine ⟨3499018754982428607461545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4665358339976571476615393 3499018754982428607461545)
                    ·
                      refine ⟨2624264066236821455596159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499018754982428607461545 2624264066236821455596159)
                      ·
                        rfl

theorem cell23_5110736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 5, 2, 2].length) (baseStart_5110736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110736 prefixEnd_5110736 := by exact prefixLift 5110736
  have htrace : WordTrace (prefixWord ++ tailWord_5110736) baseStart_5110736 baseEnd_5110736 := by
    simpa [prefixWord, tailWord_5110736, baseEnd_5110736] using wordTrace_append hprefix tailTrace_5110736
  have hstable : (prefixWord ++ tailWord_5110736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110736).length < 2 ^ (prefixWord ++ tailWord_5110736).sum := by decide
  have hdescent : baseEnd_5110736 < baseStart_5110736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110819 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 2, 6]
def baseStart_5110819 : Nat := 118140960795 + 5110819 * 2 ^ 59
def prefixEnd_5110819 : Nat := 4983230072969 + 3 ^ 40 * 5110819 * 2
def baseEnd_5110819 : Nat := 874768895043714876952759

theorem tailTrace_5110819 : CollatzResearch.WordTrace tailWord_5110819 prefixEnd_5110819 874768895043714876952759 := by
  unfold tailWord_5110819
  simp only [CollatzResearch.WordTrace]
  refine ⟨186406882871383096238503511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124271255247588730825669007 186406882871383096238503511)
  ·
    refine ⟨279610324307074644357755267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186406882871383096238503511 279610324307074644357755267)
    ·
      refine ⟨419415486460611966536632901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279610324307074644357755267 419415486460611966536632901)
      ·
        refine ⟨78640403711364743725618669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 419415486460611966536632901 78640403711364743725618669)
        ·
          refine ⟨29490151391761778897107001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78640403711364743725618669 29490151391761778897107001)
          ·
            refine ⟨22117613543821334172830251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29490151391761778897107001 22117613543821334172830251)
            ·
              refine ⟨33176420315732001259245377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22117613543821334172830251 33176420315732001259245377)
              ·
                refine ⟨24882315236799000944434033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33176420315732001259245377 24882315236799000944434033)
                ·
                  refine ⟨18661736427599250708325525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24882315236799000944434033 18661736427599250708325525)
                  ·
                    refine ⟨874768895043714876952759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18661736427599250708325525 874768895043714876952759)
                    ·
                      rfl

theorem cell23_5110819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 6].length) (baseStart_5110819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110819 prefixEnd_5110819 := by exact prefixLift 5110819
  have htrace : WordTrace (prefixWord ++ tailWord_5110819) baseStart_5110819 baseEnd_5110819 := by
    simpa [prefixWord, tailWord_5110819, baseEnd_5110819] using wordTrace_append hprefix tailTrace_5110819
  have hstable : (prefixWord ++ tailWord_5110819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110819).length < 2 ^ (prefixWord ++ tailWord_5110819).sum := by decide
  have hdescent : baseEnd_5110819 < baseStart_5110819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110820 : List Nat := [2, 3, 1, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_5110820 : Nat := 118140960795 + 5110820 * 2 ^ 59
def prefixEnd_5110820 : Nat := 4983230072969 + 3 ^ 40 * 5110820 * 2
def baseEnd_5110820 : Nat := 2624307198611799126945773

theorem tailTrace_5110820 : CollatzResearch.WordTrace tailWord_5110820 prefixEnd_5110820 2624307198611799126945773 := by
  unfold tailWord_5110820
  simp only [CollatzResearch.WordTrace]
  refine ⟨93203459672189736704644957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124271279562919648939526609 93203459672189736704644957)
  ·
    refine ⟨34951297377071151264241859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93203459672189736704644957 34951297377071151264241859)
    ·
      refine ⟨52426946065606726896362789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34951297377071151264241859 52426946065606726896362789)
      ·
        refine ⟨9830052387301261293068023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52426946065606726896362789 9830052387301261293068023)
        ·
          refine ⟨14745078580951891939602035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9830052387301261293068023 14745078580951891939602035)
          ·
            refine ⟨22117617871427837909403053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14745078580951891939602035 22117617871427837909403053)
            ·
              refine ⟨8294106701785439216026145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22117617871427837909403053 8294106701785439216026145)
              ·
                refine ⟨6220580026339079412019609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8294106701785439216026145 6220580026339079412019609)
                ·
                  refine ⟨4665435019754309559014707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6220580026339079412019609 4665435019754309559014707)
                  ·
                    refine ⟨6998152529631464338522061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4665435019754309559014707 6998152529631464338522061)
                    ·
                      refine ⟨2624307198611799126945773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6998152529631464338522061 2624307198611799126945773)
                      ·
                        rfl

theorem cell23_5110820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_5110820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110820 prefixEnd_5110820 := by exact prefixLift 5110820
  have htrace : WordTrace (prefixWord ++ tailWord_5110820) baseStart_5110820 baseEnd_5110820 := by
    simpa [prefixWord, tailWord_5110820, baseEnd_5110820] using wordTrace_append hprefix tailTrace_5110820
  have hstable : (prefixWord ++ tailWord_5110820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110820).length < 2 ^ (prefixWord ++ tailWord_5110820).sum := by decide
  have hdescent : baseEnd_5110820 < baseStart_5110820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110889 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 7]
def baseStart_5110889 : Nat := 118140960795 + 5110889 * 2 ^ 59
def prefixEnd_5110889 : Nat := 4983230072969 + 3 ^ 40 * 5110889 * 2
def baseEnd_5110889 : Nat := 2624342628776959356982955

theorem tailTrace_5110889 : CollatzResearch.WordTrace tailWord_5110889 prefixEnd_5110889 2624342628776959356982955 := by
  unfold tailWord_5110889
  simp only [CollatzResearch.WordTrace]
  refine ⟨186409435981129498193551721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124272957320752998795701147 186409435981129498193551721)
  ·
    refine ⟨139807076985847123645163791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186409435981129498193551721 139807076985847123645163791)
    ·
      refine ⟨209710615478770685467745687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139807076985847123645163791 209710615478770685467745687)
      ·
        refine ⟨314565923218156028201618531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209710615478770685467745687 314565923218156028201618531)
        ·
          refine ⟨471848884827234042302427797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314565923218156028201618531 471848884827234042302427797)
          ·
            refine ⟨22117916476276595732926303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 471848884827234042302427797 22117916476276595732926303)
            ·
              refine ⟨33176874714414893599389455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22117916476276595732926303 33176874714414893599389455)
              ·
                refine ⟨49765312071622340399084183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33176874714414893599389455 49765312071622340399084183)
                ·
                  refine ⟨74647968107433510598626275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49765312071622340399084183 74647968107433510598626275)
                  ·
                    refine ⟨111971952161150265897939413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74647968107433510598626275 111971952161150265897939413)
                    ·
                      refine ⟨2624342628776959356982955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111971952161150265897939413 2624342628776959356982955)
                      ·
                        rfl

theorem cell23_5110889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_5110889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110889 prefixEnd_5110889 := by exact prefixLift 5110889
  have htrace : WordTrace (prefixWord ++ tailWord_5110889) baseStart_5110889 baseEnd_5110889 := by
    simpa [prefixWord, tailWord_5110889, baseEnd_5110889] using wordTrace_append hprefix tailTrace_5110889
  have hstable : (prefixWord ++ tailWord_5110889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110889).length < 2 ^ (prefixWord ++ tailWord_5110889).sum := by decide
  have hdescent : baseEnd_5110889 < baseStart_5110889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110894 : List Nat := [4, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_5110894 : Nat := 118140960795 + 5110894 * 2 ^ 59
def prefixEnd_5110894 : Nat := 4983230072969 + 3 ^ 40 * 5110894 * 2
def baseEnd_5110894 : Nat := 2624345196180231837420433

theorem tailTrace_5110894 : CollatzResearch.WordTrace tailWord_5110894 prefixEnd_5110894 2624345196180231837420433 := by
  unfold tailWord_5110894
  simp only [CollatzResearch.WordTrace]
  refine ⟨23301202293263923005935467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124273078897407589364989157 23301202293263923005935467)
  ·
    refine ⟨34951803439895884508903201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23301202293263923005935467 34951803439895884508903201)
    ·
      refine ⟨26213852579921913381677401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34951803439895884508903201 26213852579921913381677401)
      ·
        refine ⟨19660389434941435036258051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26213852579921913381677401 19660389434941435036258051)
        ·
          refine ⟨29490584152412152554387077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19660389434941435036258051 29490584152412152554387077)
          ·
            refine ⟨5529484528577278603947577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29490584152412152554387077 5529484528577278603947577)
            ·
              refine ⟨4147113396432958952960683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5529484528577278603947577 4147113396432958952960683)
              ·
                refine ⟨6220670094649438429441025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4147113396432958952960683 6220670094649438429441025)
                ·
                  refine ⟨4665502570987078822080769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6220670094649438429441025 4665502570987078822080769)
                  ·
                    refine ⟨3499126928240309116560577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4665502570987078822080769 3499126928240309116560577)
                    ·
                      refine ⟨2624345196180231837420433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499126928240309116560577 2624345196180231837420433)
                      ·
                        rfl

theorem cell23_5110894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_5110894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110894 prefixEnd_5110894 := by exact prefixLift 5110894
  have htrace : WordTrace (prefixWord ++ tailWord_5110894) baseStart_5110894 baseEnd_5110894 := by
    simpa [prefixWord, tailWord_5110894, baseEnd_5110894] using wordTrace_append hprefix tailTrace_5110894
  have hstable : (prefixWord ++ tailWord_5110894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110894).length < 2 ^ (prefixWord ++ tailWord_5110894).sum := by decide
  have hdescent : baseEnd_5110894 < baseStart_5110894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110913 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 2, 5]
def baseStart_5110913 : Nat := 118140960795 + 5110913 * 2 ^ 59
def prefixEnd_5110913 : Nat := 4983230072969 + 3 ^ 40 * 5110913 * 2
def baseEnd_5110913 : Nat := 874784984104222421027615

theorem tailTrace_5110913 : CollatzResearch.WordTrace tailWord_5110913 prefixEnd_5110913 874784984104222421027615 := by
  unfold tailWord_5110913
  simp only [CollatzResearch.WordTrace]
  refine ⟨186410311333042550292425393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124273540888695033528283595 186410311333042550292425393)
  ·
    refine ⟨139807733499781912719319045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186410311333042550292425393 139807733499781912719319045)
    ·
      refine ⟨26213950031209108634872321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139807733499781912719319045 26213950031209108634872321)
      ·
        refine ⟨19660462523406831476154241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26213950031209108634872321 19660462523406831476154241)
        ·
          refine ⟨14745346892555123607115681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19660462523406831476154241 14745346892555123607115681)
          ·
            refine ⟨11059010169416342705336761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14745346892555123607115681 11059010169416342705336761)
            ·
              refine ⟨8294257627062257029002571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11059010169416342705336761 8294257627062257029002571)
              ·
                refine ⟨12441386440593385543503857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8294257627062257029002571 12441386440593385543503857)
                ·
                  refine ⟨9331039830445039157627893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12441386440593385543503857 9331039830445039157627893)
                  ·
                    refine ⟨874784984104222421027615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9331039830445039157627893 874784984104222421027615)
                    ·
                      rfl

theorem cell23_5110913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_5110913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110913 prefixEnd_5110913 := by exact prefixLift 5110913
  have htrace : WordTrace (prefixWord ++ tailWord_5110913) baseStart_5110913 baseEnd_5110913 := by
    simpa [prefixWord, tailWord_5110913, baseEnd_5110913] using wordTrace_append hprefix tailTrace_5110913
  have hstable : (prefixWord ++ tailWord_5110913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110913).length < 2 ^ (prefixWord ++ tailWord_5110913).sum := by decide
  have hdescent : baseEnd_5110913 < baseStart_5110913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110977 : List Nat := [1, 2, 6, 1, 1, 1, 1, 5, 1, 4]
def baseStart_5110977 : Nat := 118140960795 + 5110977 * 2 ^ 59
def prefixEnd_5110977 : Nat := 4983230072969 + 3 ^ 40 * 5110977 * 2
def baseEnd_5110977 : Nat := 874795938358185004227517

theorem tailTrace_5110977 : CollatzResearch.WordTrace tailWord_5110977 prefixEnd_5110977 874795938358185004227517 := by
  unfold tailWord_5110977
  simp only [CollatzResearch.WordTrace]
  refine ⟨186412645604810689222755185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124275097069873792815170123 186412645604810689222755185)
  ·
    refine ⟨139809484203608016917066389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186412645604810689222755185 139809484203608016917066389)
    ·
      refine ⟨6553569572044125792987487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139809484203608016917066389 6553569572044125792987487)
      ·
        refine ⟨9830354358066188689481231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6553569572044125792987487 9830354358066188689481231)
        ·
          refine ⟨14745531537099283034221847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9830354358066188689481231 14745531537099283034221847)
          ·
            refine ⟨22118297305648924551332771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14745531537099283034221847 22118297305648924551332771)
            ·
              refine ⟨33177445958473386826999157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22118297305648924551332771 33177445958473386826999157)
              ·
                refine ⟨3110385558606880015031171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33177445958473386826999157 3110385558606880015031171)
                ·
                  refine ⟨4665578337910320022546757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110385558606880015031171 4665578337910320022546757)
                  ·
                    refine ⟨874795938358185004227517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4665578337910320022546757 874795938358185004227517)
                    ·
                      rfl

theorem cell23_5110977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_5110977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110977 prefixEnd_5110977 := by exact prefixLift 5110977
  have htrace : WordTrace (prefixWord ++ tailWord_5110977) baseStart_5110977 baseEnd_5110977 := by
    simpa [prefixWord, tailWord_5110977, baseEnd_5110977] using wordTrace_append hprefix tailTrace_5110977
  have hstable : (prefixWord ++ tailWord_5110977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110977).length < 2 ^ (prefixWord ++ tailWord_5110977).sum := by decide
  have hdescent : baseEnd_5110977 < baseStart_5110977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110990 : List Nat := [4, 1, 1, 1, 5, 2, 1, 2, 6]
def baseStart_5110990 : Nat := 118140960795 + 5110990 * 2 ^ 59
def prefixEnd_5110990 : Nat := 4983230072969 + 3 ^ 40 * 5110990 * 2
def baseEnd_5110990 : Nat := 291599387813673717979999

theorem tailTrace_5110990 : CollatzResearch.WordTrace tailWord_5110990 prefixEnd_5110990 291599387813673717979999 := by
  unfold tailWord_5110990
  simp only [CollatzResearch.WordTrace]
  refine ⟨23301639969220449055372303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124275413169175728295318949 23301639969220449055372303)
  ·
    refine ⟨34952459953830673583058455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23301639969220449055372303 34952459953830673583058455)
    ·
      refine ⟨52428689930746010374587683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34952459953830673583058455 52428689930746010374587683)
      ·
        refine ⟨78643034896119015561881525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52428689930746010374587683 78643034896119015561881525)
        ·
          refine ⟨7372784521511157708926393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78643034896119015561881525 7372784521511157708926393)
          ·
            refine ⟨5529588391133368281694795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7372784521511157708926393 5529588391133368281694795)
            ·
              refine ⟨8294382586700052422542193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5529588391133368281694795 8294382586700052422542193)
              ·
                refine ⟨6220786940025039316906645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8294382586700052422542193 6220786940025039316906645)
                ·
                  refine ⟨291599387813673717979999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6220786940025039316906645 291599387813673717979999)
                  ·
                    rfl

theorem cell23_5110990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_5110990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110990 prefixEnd_5110990 := by exact prefixLift 5110990
  have htrace : WordTrace (prefixWord ++ tailWord_5110990) baseStart_5110990 baseEnd_5110990 := by
    simpa [prefixWord, tailWord_5110990, baseEnd_5110990] using wordTrace_append hprefix tailTrace_5110990
  have hstable : (prefixWord ++ tailWord_5110990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110990).length < 2 ^ (prefixWord ++ tailWord_5110990).sum := by decide
  have hdescent : baseEnd_5110990 < baseStart_5110990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5110993 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 4, 3, 2]
def baseStart_5110993 : Nat := 118140960795 + 5110993 * 2 ^ 59
def prefixEnd_5110993 : Nat := 4983230072969 + 3 ^ 40 * 5110993 * 2
def baseEnd_5110993 : Nat := 2624396030765026950082477

theorem tailTrace_5110993 : CollatzResearch.WordTrace tailWord_5110993 prefixEnd_5110993 2624396030765026950082477 := by
  unfold tailWord_5110993
  simp only [CollatzResearch.WordTrace]
  refine ⟨186413229172752723955337633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124275486115168482636891755 186413229172752723955337633)
  ·
    refine ⟨139809921879564542966503225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186413229172752723955337633 139809921879564542966503225)
    ·
      refine ⟨104857441409673407224877419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139809921879564542966503225 104857441409673407224877419)
      ·
        refine ⟨157286162114510110837316129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104857441409673407224877419 157286162114510110837316129)
        ·
          refine ⟨117964621585882583127987097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157286162114510110837316129 117964621585882583127987097)
          ·
            refine ⟨88473466189411937345990323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117964621585882583127987097 88473466189411937345990323)
            ·
              refine ⟨132710199284117906018985485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88473466189411937345990323 132710199284117906018985485)
              ·
                refine ⟨49766324731544214757119557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132710199284117906018985485 49766324731544214757119557)
                ·
                  refine ⟨9331185887164540266959917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49766324731544214757119557 9331185887164540266959917)
                  ·
                    refine ⟨3499194707686702600109969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9331185887164540266959917 3499194707686702600109969)
                    ·
                      refine ⟨2624396030765026950082477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499194707686702600109969 2624396030765026950082477)
                      ·
                        rfl

theorem cell23_5110993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 3, 2].length) (baseStart_5110993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5110993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5110993 prefixEnd_5110993 := by exact prefixLift 5110993
  have htrace : WordTrace (prefixWord ++ tailWord_5110993) baseStart_5110993 baseEnd_5110993 := by
    simpa [prefixWord, tailWord_5110993, baseEnd_5110993] using wordTrace_append hprefix tailTrace_5110993
  have hstable : (prefixWord ++ tailWord_5110993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5110993).length < 2 ^ (prefixWord ++ tailWord_5110993).sum := by decide
  have hdescent : baseEnd_5110993 < baseStart_5110993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5110993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111028 : List Nat := [2, 6, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_5111028 : Nat := 118140960795 + 5111028 * 2 ^ 59
def prefixEnd_5111028 : Nat := 4983230072969 + 3 ^ 40 * 5111028 * 2
def baseEnd_5111028 : Nat := 874804667529311437714939

theorem tailTrace_5111028 : CollatzResearch.WordTrace tailWord_5111028 prefixEnd_5111028 874804667529311437714939 := by
  unfold tailWord_5111028
  simp only [CollatzResearch.WordTrace]
  refine ⟨93207252863812962466430869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124276337151750616621907825 93207252863812962466430869)
  ·
    refine ⟨4369089977991232615613947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93207252863812962466430869 4369089977991232615613947)
    ·
      refine ⟨6553634966986848923420921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4369089977991232615613947 6553634966986848923420921)
      ·
        refine ⟨4915226225240136692565691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6553634966986848923420921 4915226225240136692565691)
        ·
          refine ⟨7372839337860205038848537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4915226225240136692565691 7372839337860205038848537)
          ·
            refine ⟨5529629503395153779136403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7372839337860205038848537 5529629503395153779136403)
            ·
              refine ⟨8294444255092730668704605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5529629503395153779136403 8294444255092730668704605)
              ·
                refine ⟨3110416595659774000764227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8294444255092730668704605 3110416595659774000764227)
                ·
                  refine ⟨4665624893489661001146341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110416595659774000764227 4665624893489661001146341)
                  ·
                    refine ⟨874804667529311437714939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4665624893489661001146341 874804667529311437714939)
                    ·
                      rfl

theorem cell23_5111028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_5111028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111028 prefixEnd_5111028 := by exact prefixLift 5111028
  have htrace : WordTrace (prefixWord ++ tailWord_5111028) baseStart_5111028 baseEnd_5111028 := by
    simpa [prefixWord, tailWord_5111028, baseEnd_5111028] using wordTrace_append hprefix tailTrace_5111028
  have hstable : (prefixWord ++ tailWord_5111028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111028).length < 2 ^ (prefixWord ++ tailWord_5111028).sum := by decide
  have hdescent : baseEnd_5111028 < baseStart_5111028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111043 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 5]
def baseStart_5111043 : Nat := 118140960795 + 5111043 * 2 ^ 59
def prefixEnd_5111043 : Nat := 4983230072969 + 3 ^ 40 * 5111043 * 2
def baseEnd_5111043 : Nat := 2624421704797751754457247

theorem tailTrace_5111043 : CollatzResearch.WordTrace tailWord_5111043 prefixEnd_5111043 2624421704797751754457247 := by
  unfold tailWord_5111043
  simp only [CollatzResearch.WordTrace]
  refine ⟨186415052822571582494657783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124276701881714388329771855 186415052822571582494657783)
  ·
    refine ⟨279622579233857373741986675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186415052822571582494657783 279622579233857373741986675)
    ·
      refine ⟨419433868850786060612980013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279622579233857373741986675 419433868850786060612980013)
      ·
        refine ⟨157287700819044772729867505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 419433868850786060612980013 157287700819044772729867505)
        ·
          refine ⟨117965775614283579547400629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157287700819044772729867505 117965775614283579547400629)
          ·
            refine ⟨11059291463839085582568809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117965775614283579547400629 11059291463839085582568809)
            ·
              refine ⟨8294468597879314186926607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11059291463839085582568809 8294468597879314186926607)
              ·
                refine ⟨12441702896818971280389911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8294468597879314186926607 12441702896818971280389911)
                ·
                  refine ⟨18662554345228456920584867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12441702896818971280389911 18662554345228456920584867)
                  ·
                    refine ⟨27993831517842685380877301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18662554345228456920584867 27993831517842685380877301)
                    ·
                      refine ⟨2624421704797751754457247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27993831517842685380877301 2624421704797751754457247)
                      ·
                        rfl

theorem cell23_5111043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_5111043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111043 prefixEnd_5111043 := by exact prefixLift 5111043
  have htrace : WordTrace (prefixWord ++ tailWord_5111043) baseStart_5111043 baseEnd_5111043 := by
    simpa [prefixWord, tailWord_5111043, baseEnd_5111043] using wordTrace_append hprefix tailTrace_5111043
  have hstable : (prefixWord ++ tailWord_5111043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111043).length < 2 ^ (prefixWord ++ tailWord_5111043).sum := by decide
  have hdescent : baseEnd_5111043 < baseStart_5111043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111073 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_5111073 : Nat := 118140960795 + 5111073 * 2 ^ 59
def prefixEnd_5111073 : Nat := 4983230072969 + 3 ^ 40 * 5111073 * 2
def baseEnd_5111073 : Nat := 2624437109217386637082109

theorem tailTrace_5111073 : CollatzResearch.WordTrace tailWord_5111073 prefixEnd_5111073 2624437109217386637082109 := by
  unfold tailWord_5111073
  simp only [CollatzResearch.WordTrace]
  refine ⟨186416147012462897618249873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124277431341641931745499915 186416147012462897618249873)
  ·
    refine ⟨139812110259347173213687405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186416147012462897618249873 139812110259347173213687405)
    ·
      refine ⟨52429541347255189955132777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139812110259347173213687405 52429541347255189955132777)
      ·
        refine ⟨39322156010441392466349583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52429541347255189955132777 39322156010441392466349583)
        ·
          refine ⟨58983234015662088699524375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39322156010441392466349583 58983234015662088699524375)
          ·
            refine ⟨88474851023493133049286563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58983234015662088699524375 88474851023493133049286563)
            ·
              refine ⟨132712276535239699573929845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88474851023493133049286563 132712276535239699573929845)
              ·
                refine ⟨12441775925178721835055923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132712276535239699573929845 12441775925178721835055923)
                ·
                  refine ⟨18662663887768082752583885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12441775925178721835055923 18662663887768082752583885)
                  ·
                    refine ⟨6998498957913031032218957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18662663887768082752583885 6998498957913031032218957)
                    ·
                      refine ⟨2624437109217386637082109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6998498957913031032218957 2624437109217386637082109)
                      ·
                        rfl

theorem cell23_5111073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_5111073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111073 prefixEnd_5111073 := by exact prefixLift 5111073
  have htrace : WordTrace (prefixWord ++ tailWord_5111073) baseStart_5111073 baseEnd_5111073 := by
    simpa [prefixWord, tailWord_5111073, baseEnd_5111073] using wordTrace_append hprefix tailTrace_5111073
  have hstable : (prefixWord ++ tailWord_5111073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111073).length < 2 ^ (prefixWord ++ tailWord_5111073).sum := by decide
  have hdescent : baseEnd_5111073 < baseStart_5111073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111074 : List Nat := [3, 3, 1, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_5111074 : Nat := 118140960795 + 5111074 * 2 ^ 59
def prefixEnd_5111074 : Nat := 4983230072969 + 3 ^ 40 * 5111074 * 2
def baseEnd_5111074 : Nat := 2624437622698041133169605

theorem tailTrace_5111074 : CollatzResearch.WordTrace tailWord_5111074 prefixEnd_5111074 2624437622698041133169605 := by
  unfold tailWord_5111074
  simp only [CollatzResearch.WordTrace]
  refine ⟨46604045871364818697259069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124277455656972849859357517 46604045871364818697259069)
  ·
    refine ⟨17476517201761807011472151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46604045871364818697259069 17476517201761807011472151)
    ·
      refine ⟨26214775802642710517208227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17476517201761807011472151 26214775802642710517208227)
      ·
        refine ⟨39322163703964065775812341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26214775802642710517208227 39322163703964065775812341)
        ·
          refine ⟨3686452847246631166482407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39322163703964065775812341 3686452847246631166482407)
          ·
            refine ⟨5529679270869946749723611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3686452847246631166482407 5529679270869946749723611)
            ·
              refine ⟨8294518906304920124585417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5529679270869946749723611 8294518906304920124585417)
              ·
                refine ⟨6220889179728690093439063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8294518906304920124585417 6220889179728690093439063)
                ·
                  refine ⟨9331333769593035140158595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6220889179728690093439063 9331333769593035140158595)
                  ·
                    refine ⟨13997000654389552710237893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9331333769593035140158595 13997000654389552710237893)
                    ·
                      refine ⟨2624437622698041133169605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13997000654389552710237893 2624437622698041133169605)
                      ·
                        rfl

theorem cell23_5111074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_5111074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111074 prefixEnd_5111074 := by exact prefixLift 5111074
  have htrace : WordTrace (prefixWord ++ tailWord_5111074) baseStart_5111074 baseEnd_5111074 := by
    simpa [prefixWord, tailWord_5111074, baseEnd_5111074] using wordTrace_append hprefix tailTrace_5111074
  have hstable : (prefixWord ++ tailWord_5111074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111074).length < 2 ^ (prefixWord ++ tailWord_5111074).sum := by decide
  have hdescent : baseEnd_5111074 < baseStart_5111074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111077 : List Nat := [1, 3, 1, 2, 4, 3, 1, 2, 1, 2, 3]
def baseStart_5111077 : Nat := 118140960795 + 5111077 * 2 ^ 59
def prefixEnd_5111077 : Nat := 4983230072969 + 3 ^ 40 * 5111077 * 2
def baseEnd_5111077 : Nat := 2624439163140004621432091

theorem tailTrace_5111077 : CollatzResearch.WordTrace tailWord_5111077 prefixEnd_5111077 2624439163140004621432091 := by
  unfold tailWord_5111077
  simp only [CollatzResearch.WordTrace]
  refine ⟨186416292904448406301395485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124277528602965604200930323 186416292904448406301395485)
  ·
    refine ⟨69906109839168152363023307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186416292904448406301395485 69906109839168152363023307)
    ·
      refine ⟨104859164758752228544534961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69906109839168152363023307 104859164758752228544534961)
      ·
        refine ⟨78644373569064171408401221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104859164758752228544534961 78644373569064171408401221)
        ·
          refine ⟨14745820044199532139075229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78644373569064171408401221 14745820044199532139075229)
          ·
            refine ⟨5529682516574824552153211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14745820044199532139075229 5529682516574824552153211)
            ·
              refine ⟨8294523774862236828229817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5529682516574824552153211 8294523774862236828229817)
              ·
                refine ⟨6220892831146677621172363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8294523774862236828229817 6220892831146677621172363)
                ·
                  refine ⟨9331339246720016431758545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6220892831146677621172363 9331339246720016431758545)
                  ·
                    refine ⟨6998504435040012323818909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9331339246720016431758545 6998504435040012323818909)
                    ·
                      refine ⟨2624439163140004621432091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6998504435040012323818909 2624439163140004621432091)
                      ·
                        rfl

theorem cell23_5111077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_5111077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111077 prefixEnd_5111077 := by exact prefixLift 5111077
  have htrace : WordTrace (prefixWord ++ tailWord_5111077) baseStart_5111077 baseEnd_5111077 := by
    simpa [prefixWord, tailWord_5111077, baseEnd_5111077] using wordTrace_append hprefix tailTrace_5111077
  have hstable : (prefixWord ++ tailWord_5111077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111077).length < 2 ^ (prefixWord ++ tailWord_5111077).sum := by decide
  have hdescent : baseEnd_5111077 < baseStart_5111077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111090 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_5111090 : Nat := 118140960795 + 5111090 * 2 ^ 59
def prefixEnd_5111090 : Nat := 4983230072969 + 3 ^ 40 * 5111090 * 2
def baseEnd_5111090 : Nat := 2624445838388513070569531

theorem tailTrace_5111090 : CollatzResearch.WordTrace tailWord_5111090 prefixEnd_5111090 2624445838388513070569531 := by
  unfold tailWord_5111090
  simp only [CollatzResearch.WordTrace]
  refine ⟨46604191763350327380404681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124277844702267539681079149 46604191763350327380404681)
  ·
    refine ⟨34953143822512745535303511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46604191763350327380404681 34953143822512745535303511)
    ·
      refine ⟨52429715733769118302955267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34953143822512745535303511 52429715733769118302955267)
      ·
        refine ⟨78644573600653677454432901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52429715733769118302955267 78644573600653677454432901)
        ·
          refine ⟨14745857550122564522706169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78644573600653677454432901 14745857550122564522706169)
          ·
            refine ⟨11059393162591923392029627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14745857550122564522706169 11059393162591923392029627)
            ·
              refine ⟨16589089743887885088044441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11059393162591923392029627 16589089743887885088044441)
              ·
                refine ⟨12441817307915913816033331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16589089743887885088044441 12441817307915913816033331)
                ·
                  refine ⟨18662725961873870724049997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12441817307915913816033331 18662725961873870724049997)
                  ·
                    refine ⟨6998522235702701521518749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18662725961873870724049997 6998522235702701521518749)
                    ·
                      refine ⟨2624445838388513070569531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6998522235702701521518749 2624445838388513070569531)
                      ·
                        rfl

theorem cell23_5111090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_5111090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111090 prefixEnd_5111090 := by exact prefixLift 5111090
  have htrace : WordTrace (prefixWord ++ tailWord_5111090) baseStart_5111090 baseEnd_5111090 := by
    simpa [prefixWord, tailWord_5111090, baseEnd_5111090] using wordTrace_append hprefix tailTrace_5111090
  have hstable : (prefixWord ++ tailWord_5111090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111090).length < 2 ^ (prefixWord ++ tailWord_5111090).sum := by decide
  have hdescent : baseEnd_5111090 < baseStart_5111090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111094 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5111094 : Nat := 118140960795 + 5111094 * 2 ^ 59
def prefixEnd_5111094 : Nat := 4983230072969 + 3 ^ 40 * 5111094 * 2
def baseEnd_5111094 : Nat := 2624447892311131054919513

theorem tailTrace_5111094 : CollatzResearch.WordTrace tailWord_5111094 prefixEnd_5111094 2624447892311131054919513 := by
  unfold tailWord_5111094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11651057059086676137797771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124277941963591212136509557 11651057059086676137797771)
  ·
    refine ⟨17476585588630014206696657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11651057059086676137797771 17476585588630014206696657)
    ·
      refine ⟨13107439191472510655022493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17476585588630014206696657 13107439191472510655022493)
      ·
        refine ⟨4915289696802191495633435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13107439191472510655022493 4915289696802191495633435)
        ·
          refine ⟨7372934545203287243450153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4915289696802191495633435 7372934545203287243450153)
          ·
            refine ⟨5529700908902465432587615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7372934545203287243450153 5529700908902465432587615)
            ·
              refine ⟨8294551363353698148881423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5529700908902465432587615 8294551363353698148881423)
              ·
                refine ⟨12441827045030547223322135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8294551363353698148881423 12441827045030547223322135)
                ·
                  refine ⟨18662740567545820834983203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12441827045030547223322135 18662740567545820834983203)
                  ·
                    refine ⟨27994110851318731252474805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18662740567545820834983203 27994110851318731252474805)
                    ·
                      refine ⟨2624447892311131054919513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27994110851318731252474805 2624447892311131054919513)
                      ·
                        rfl

theorem cell23_5111094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5111094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111094 prefixEnd_5111094 := by exact prefixLift 5111094
  have htrace : WordTrace (prefixWord ++ tailWord_5111094) baseStart_5111094 baseEnd_5111094 := by
    simpa [prefixWord, tailWord_5111094, baseEnd_5111094] using wordTrace_append hprefix tailTrace_5111094
  have hstable : (prefixWord ++ tailWord_5111094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111094).length < 2 ^ (prefixWord ++ tailWord_5111094).sum := by decide
  have hdescent : baseEnd_5111094 < baseStart_5111094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111108 : List Nat := [2, 3, 4, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_5111108 : Nat := 118140960795 + 5111108 * 2 ^ 59
def prefixEnd_5111108 : Nat := 4983230072969 + 3 ^ 40 * 5111108 * 2
def baseEnd_5111108 : Nat := 2624455081040294000144449

theorem tailTrace_5111108 : CollatzResearch.WordTrace tailWord_5111108 prefixEnd_5111108 2624455081040294000144449 := by
  unfold tailWord_5111108
  simp only [CollatzResearch.WordTrace]
  refine ⟨93208711783668049297886989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124278282378224065730515985 93208711783668049297886989)
  ·
    refine ⟨34953266918875518486707621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93208711783668049297886989 34953266918875518486707621)
    ·
      refine ⟨6553737547289159716257679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34953266918875518486707621 6553737547289159716257679)
      ·
        refine ⟨9830606320933739574386519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6553737547289159716257679 9830606320933739574386519)
        ·
          refine ⟨14745909481400609361579779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9830606320933739574386519 14745909481400609361579779)
          ·
            refine ⟨22118864222100914042369669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14745909481400609361579779 22118864222100914042369669)
            ·
              refine ⟨4147287041643921382944313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22118864222100914042369669 4147287041643921382944313)
              ·
                refine ⟨3110465281232941037208235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4147287041643921382944313 3110465281232941037208235)
                ·
                  refine ⟨4665697921849411555812353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110465281232941037208235 4665697921849411555812353)
                  ·
                    refine ⟨3499273441387058666859265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4665697921849411555812353 3499273441387058666859265)
                    ·
                      refine ⟨2624455081040294000144449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499273441387058666859265 2624455081040294000144449)
                      ·
                        rfl

theorem cell23_5111108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_5111108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111108 prefixEnd_5111108 := by exact prefixLift 5111108
  have htrace : WordTrace (prefixWord ++ tailWord_5111108) baseStart_5111108 baseEnd_5111108 := by
    simpa [prefixWord, tailWord_5111108, baseEnd_5111108] using wordTrace_append hprefix tailTrace_5111108
  have hstable : (prefixWord ++ tailWord_5111108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111108).length < 2 ^ (prefixWord ++ tailWord_5111108).sum := by decide
  have hdescent : baseEnd_5111108 < baseStart_5111108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111130 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2]
def baseStart_5111130 : Nat := 118140960795 + 5111130 * 2 ^ 59
def prefixEnd_5111130 : Nat := 4983230072969 + 3 ^ 40 * 5111130 * 2
def baseEnd_5111130 : Nat := 2624466377614692914069347

theorem tailTrace_5111130 : CollatzResearch.WordTrace tailWord_5111130 prefixEnd_5111130 2624466377614692914069347 := by
  unfold tailWord_5111130
  simp only [CollatzResearch.WordTrace]
  refine ⟨46604556493314099088268711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124278817315504264235383229 46604556493314099088268711)
  ·
    refine ⟨69906834739971148632403067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46604556493314099088268711 69906834739971148632403067)
    ·
      refine ⟨104860252109956722948604601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69906834739971148632403067 104860252109956722948604601)
      ·
        refine ⟨78645189082467542211453451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104860252109956722948604601 78645189082467542211453451)
        ·
          refine ⟨117967783623701313317180177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78645189082467542211453451 117967783623701313317180177)
          ·
            refine ⟨88475837717775984987885133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117967783623701313317180177 88475837717775984987885133)
            ·
              refine ⟨33178439144165994370456925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88475837717775984987885133 33178439144165994370456925)
              ·
                refine ⟨12441914679062247888921347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33178439144165994370456925 12441914679062247888921347)
                ·
                  refine ⟨18662872018593371833382021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12441914679062247888921347 18662872018593371833382021)
                  ·
                    refine ⟨3499288503486257218759129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18662872018593371833382021 3499288503486257218759129)
                    ·
                      refine ⟨2624466377614692914069347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499288503486257218759129 2624466377614692914069347)
                      ·
                        rfl

theorem cell23_5111130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_5111130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111130 prefixEnd_5111130 := by exact prefixLift 5111130
  have htrace : WordTrace (prefixWord ++ tailWord_5111130) baseStart_5111130 baseEnd_5111130 := by
    simpa [prefixWord, tailWord_5111130, baseEnd_5111130] using wordTrace_append hprefix tailTrace_5111130
  have hstable : (prefixWord ++ tailWord_5111130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111130).length < 2 ^ (prefixWord ++ tailWord_5111130).sum := by decide
  have hdescent : baseEnd_5111130 < baseStart_5111130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111163 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 3]
def baseStart_5111163 : Nat := 118140960795 + 5111163 * 2 ^ 59
def prefixEnd_5111163 : Nat := 4983230072969 + 3 ^ 40 * 5111163 * 2
def baseEnd_5111163 : Nat := 2624483322476291284956695

theorem tailTrace_5111163 : CollatzResearch.WordTrace tailWord_5111163 prefixEnd_5111163 2624483322476291284956695 := by
  unfold tailWord_5111163
  simp only [CollatzResearch.WordTrace]
  refine ⟨186419429582136842989026143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124279619721424561992684095 186419429582136842989026143)
  ·
    refine ⟨279629144373205264483539215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186419429582136842989026143 279629144373205264483539215)
    ·
      refine ⟨419443716559807896725308823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279629144373205264483539215 419443716559807896725308823)
      ·
        refine ⟨629165574839711845087963235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419443716559807896725308823 629165574839711845087963235)
        ·
          refine ⟨943748362259567767631944853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629165574839711845087963235 943748362259567767631944853)
          ·
            refine ⟨44238204480917239107747415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 943748362259567767631944853 44238204480917239107747415)
            ·
              refine ⟨66357306721375858661621123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44238204480917239107747415 66357306721375858661621123)
              ·
                refine ⟨99535960082063787992431685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66357306721375858661621123 99535960082063787992431685)
                ·
                  refine ⟨18662992515386960248580941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99535960082063787992431685 18662992515386960248580941)
                  ·
                    refine ⟨6998622193270110093217853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18662992515386960248580941 6998622193270110093217853)
                    ·
                      refine ⟨2624483322476291284956695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6998622193270110093217853 2624483322476291284956695)
                      ·
                        rfl

theorem cell23_5111163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 3].length) (baseStart_5111163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111163 prefixEnd_5111163 := by exact prefixLift 5111163
  have htrace : WordTrace (prefixWord ++ tailWord_5111163) baseStart_5111163 baseEnd_5111163 := by
    simpa [prefixWord, tailWord_5111163, baseEnd_5111163] using wordTrace_append hprefix tailTrace_5111163
  have hstable : (prefixWord ++ tailWord_5111163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111163).length < 2 ^ (prefixWord ++ tailWord_5111163).sum := by decide
  have hdescent : baseEnd_5111163 < baseStart_5111163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111203 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 4]
def baseStart_5111203 : Nat := 118140960795 + 5111203 * 2 ^ 59
def prefixEnd_5111203 : Nat := 4983230072969 + 3 ^ 40 * 5111203 * 2
def baseEnd_5111203 : Nat := 2624503861702471128456511

theorem tailTrace_5111203 : CollatzResearch.WordTrace tailWord_5111203 prefixEnd_5111203 2624503861702471128456511 := by
  unfold tailWord_5111203
  simp only [CollatzResearch.WordTrace]
  refine ⟨186420888501991929820482263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124280592334661286546988175 186420888501991929820482263)
  ·
    refine ⟨279631332752987894730723395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186420888501991929820482263 279631332752987894730723395)
    ·
      refine ⟨419446999129481842096085093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279631332752987894730723395 419446999129481842096085093)
      ·
        refine ⟨78646312336777845393015955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 419446999129481842096085093 78646312336777845393015955)
        ·
          refine ⟨117969468505166768089523933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78646312336777845393015955 117969468505166768089523933)
          ·
            refine ⟨44238550689437538033571475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117969468505166768089523933 44238550689437538033571475)
            ·
              refine ⟨66357826034156307050357213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44238550689437538033571475 66357826034156307050357213)
              ·
                refine ⟨24884184762808615143883955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66357826034156307050357213 24884184762808615143883955)
                ·
                  refine ⟨37326277144212922715825933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24884184762808615143883955 37326277144212922715825933)
                  ·
                    refine ⟨13997353929079846018434725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37326277144212922715825933 13997353929079846018434725)
                    ·
                      refine ⟨2624503861702471128456511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13997353929079846018434725 2624503861702471128456511)
                      ·
                        rfl

theorem cell23_5111203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_5111203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111203 prefixEnd_5111203 := by exact prefixLift 5111203
  have htrace : WordTrace (prefixWord ++ tailWord_5111203) baseStart_5111203 baseEnd_5111203 := by
    simpa [prefixWord, tailWord_5111203, baseEnd_5111203] using wordTrace_append hprefix tailTrace_5111203
  have hstable : (prefixWord ++ tailWord_5111203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111203).length < 2 ^ (prefixWord ++ tailWord_5111203).sum := by decide
  have hdescent : baseEnd_5111203 < baseStart_5111203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111240 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_5111240 : Nat := 118140960795 + 5111240 * 2 ^ 59
def prefixEnd_5111240 : Nat := 4983230072969 + 3 ^ 40 * 5111240 * 2
def baseEnd_5111240 : Nat := 2624522860486687483693841

theorem tailTrace_5111240 : CollatzResearch.WordTrace tailWord_5111240 prefixEnd_5111240 2624522860486687483693841 := by
  unfold tailWord_5111240
  simp only [CollatzResearch.WordTrace]
  refine ⟨93211119001428942569789587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124281492001905256759719449 93211119001428942569789587)
  ·
    refine ⟨139816678502143413854684381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93211119001428942569789587 139816678502143413854684381)
    ·
      refine ⟨52431254438303780195506643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139816678502143413854684381 52431254438303780195506643)
      ·
        refine ⟨78646881657455670293259965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52431254438303780195506643 78646881657455670293259965)
        ·
          refine ⟨29492580621545876359972487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78646881657455670293259965 29492580621545876359972487)
          ·
            refine ⟨44238870932318814539958731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29492580621545876359972487 44238870932318814539958731)
            ·
              refine ⟨66358306398478221809938097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44238870932318814539958731 66358306398478221809938097)
              ·
                refine ⟨49768729798858666357453573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66358306398478221809938097 49768729798858666357453573)
                ·
                  refine ⟨9331636837285999942022545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49768729798858666357453573 9331636837285999942022545)
                  ·
                    refine ⟨6998727627964499956516909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9331636837285999942022545 6998727627964499956516909)
                    ·
                      refine ⟨2624522860486687483693841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6998727627964499956516909 2624522860486687483693841)
                      ·
                        rfl

theorem cell23_5111240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_5111240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111240 prefixEnd_5111240 := by exact prefixLift 5111240
  have htrace : WordTrace (prefixWord ++ tailWord_5111240) baseStart_5111240 baseEnd_5111240 := by
    simpa [prefixWord, tailWord_5111240, baseEnd_5111240] using wordTrace_append hprefix tailTrace_5111240
  have hstable : (prefixWord ++ tailWord_5111240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111240).length < 2 ^ (prefixWord ++ tailWord_5111240).sum := by decide
  have hdescent : baseEnd_5111240 < baseStart_5111240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111254 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_5111254 : Nat := 118140960795 + 5111254 * 2 ^ 59
def prefixEnd_5111254 : Nat := 4983230072969 + 3 ^ 40 * 5111254 * 2
def baseEnd_5111254 : Nat := 2624530049215850428918777

theorem tailTrace_5111254 : CollatzResearch.WordTrace tailWord_5111254 prefixEnd_5111254 2624530049215850428918777 := by
  unfold tailWord_5111254
  simp only [CollatzResearch.WordTrace]
  refine ⟨11651421789050447845661801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124281832416538110353725877 11651421789050447845661801)
  ·
    refine ⟨8738566341787835884246351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11651421789050447845661801 8738566341787835884246351)
    ·
      refine ⟨13107849512681753826369527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8738566341787835884246351 13107849512681753826369527)
      ·
        refine ⟨19661774269022630739554291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13107849512681753826369527 19661774269022630739554291)
        ·
          refine ⟨29492661403533946109331437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19661774269022630739554291 29492661403533946109331437)
          ·
            refine ⟨11059748026325229790999289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29492661403533946109331437 11059748026325229790999289)
            ·
              refine ⟨8294811019743922343249467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11059748026325229790999289 8294811019743922343249467)
              ·
                refine ⟨12442216529615883514874201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8294811019743922343249467 12442216529615883514874201)
                ·
                  refine ⟨9331662397211912636155651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12442216529615883514874201 9331662397211912636155651)
                  ·
                    refine ⟨13997493595817868954233477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9331662397211912636155651 13997493595817868954233477)
                    ·
                      refine ⟨2624530049215850428918777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13997493595817868954233477 2624530049215850428918777)
                      ·
                        rfl

theorem cell23_5111254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_5111254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111254 prefixEnd_5111254 := by exact prefixLift 5111254
  have htrace : WordTrace (prefixWord ++ tailWord_5111254) baseStart_5111254 baseEnd_5111254 := by
    simpa [prefixWord, tailWord_5111254, baseEnd_5111254] using wordTrace_append hprefix tailTrace_5111254
  have hstable : (prefixWord ++ tailWord_5111254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111254).length < 2 ^ (prefixWord ++ tailWord_5111254).sum := by decide
  have hdescent : baseEnd_5111254 < baseStart_5111254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111257 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 2, 2, 3]
def baseStart_5111257 : Nat := 118140960795 + 5111257 * 2 ^ 59
def prefixEnd_5111257 : Nat := 4983230072969 + 3 ^ 40 * 5111257 * 2
def baseEnd_5111257 : Nat := 2624531589657813917181263

theorem tailTrace_5111257 : CollatzResearch.WordTrace tailWord_5111257 prefixEnd_5111257 2624531589657813917181263 := by
  unfold tailWord_5111257
  simp only [CollatzResearch.WordTrace]
  refine ⟨186422858043796297042948025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124281905362530864695298683 186422858043796297042948025)
  ·
    refine ⟨139817143532847222782211019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186422858043796297042948025 139817143532847222782211019)
    ·
      refine ⟨209725715299270834173316529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139817143532847222782211019 209725715299270834173316529)
      ·
        refine ⟨157294286474453125629987397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209725715299270834173316529 157294286474453125629987397)
        ·
          refine ⟨29492678713959961055622637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157294286474453125629987397 29492678713959961055622637)
          ·
            refine ⟨11059754517734985395858489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29492678713959961055622637 11059754517734985395858489)
            ·
              refine ⟨8294815888301239046893867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11059754517734985395858489 8294815888301239046893867)
              ·
                refine ⟨12442223832451858570340801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8294815888301239046893867 12442223832451858570340801)
                ·
                  refine ⟨9331667874338893927755601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12442223832451858570340801 9331667874338893927755601)
                  ·
                    refine ⟨6998750905754170445816701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9331667874338893927755601 6998750905754170445816701)
                    ·
                      refine ⟨2624531589657813917181263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6998750905754170445816701 2624531589657813917181263)
                      ·
                        rfl

theorem cell23_5111257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_5111257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111257 prefixEnd_5111257 := by exact prefixLift 5111257
  have htrace : WordTrace (prefixWord ++ tailWord_5111257) baseStart_5111257 baseEnd_5111257 := by
    simpa [prefixWord, tailWord_5111257, baseEnd_5111257] using wordTrace_append hprefix tailTrace_5111257
  have hstable : (prefixWord ++ tailWord_5111257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111257).length < 2 ^ (prefixWord ++ tailWord_5111257).sum := by decide
  have hdescent : baseEnd_5111257 < baseStart_5111257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111281 : List Nat := [1, 2, 2, 2, 3, 4, 2, 2, 1, 4]
def baseStart_5111281 : Nat := 118140960795 + 5111281 * 2 ^ 59
def prefixEnd_5111281 : Nat := 4983230072969 + 3 ^ 40 * 5111281 * 2
def baseEnd_5111281 : Nat := 874847971064507274427051

theorem tailTrace_5111281 : CollatzResearch.WordTrace tailWord_5111281 prefixEnd_5111281 874847971064507274427051 := by
  unfold tailWord_5111281
  simp only [CollatzResearch.WordTrace]
  refine ⟨186423733395709349141821697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124282488930472899427881131 186423733395709349141821697)
  ·
    refine ⟨139817800046782011856366273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186423733395709349141821697 139817800046782011856366273)
    ·
      refine ⟨104863350035086508892274705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139817800046782011856366273 104863350035086508892274705)
      ·
        refine ⟨78647512526314881669206029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104863350035086508892274705 78647512526314881669206029)
        ·
          refine ⟨29492817197368080625952261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78647512526314881669206029 29492817197368080625952261)
          ·
            refine ⟨5529903224506515117366049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29492817197368080625952261 5529903224506515117366049)
            ·
              refine ⟨4147427418379886338024537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5529903224506515117366049 4147427418379886338024537)
              ·
                refine ⟨3110570563784914753518403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4147427418379886338024537 3110570563784914753518403)
                ·
                  refine ⟨4665855845677372130277605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110570563784914753518403 4665855845677372130277605)
                  ·
                    refine ⟨874847971064507274427051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4665855845677372130277605 874847971064507274427051)
                    ·
                      rfl

theorem cell23_5111281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_5111281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111281 prefixEnd_5111281 := by exact prefixLift 5111281
  have htrace : WordTrace (prefixWord ++ tailWord_5111281) baseStart_5111281 baseEnd_5111281 := by
    simpa [prefixWord, tailWord_5111281, baseEnd_5111281] using wordTrace_append hprefix tailTrace_5111281
  have hstable : (prefixWord ++ tailWord_5111281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111281).length < 2 ^ (prefixWord ++ tailWord_5111281).sum := by decide
  have hdescent : baseEnd_5111281 < baseStart_5111281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111354 : List Nat := [3, 1, 1, 1, 3, 2, 5, 1, 2, 4]
def baseStart_5111354 : Nat := 118140960795 + 5111354 * 2 ^ 59
def prefixEnd_5111354 : Nat := 4983230072969 + 3 ^ 40 * 5111354 * 2
def baseEnd_5111354 : Nat := 874860465760433345889439

theorem tailTrace_5111354 : CollatzResearch.WordTrace tailWord_5111354 prefixEnd_5111354 874860465760433345889439 := by
  unfold tailWord_5111354
  simp only [CollatzResearch.WordTrace]
  refine ⟨46606598981111220652307279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124284263949629921739486077 46606598981111220652307279)
  ·
    refine ⟨69909898471666830978460919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46606598981111220652307279 69909898471666830978460919)
    ·
      refine ⟨104864847707500246467691379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69909898471666830978460919 104864847707500246467691379)
      ·
        refine ⟨157297271561250369701537069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104864847707500246467691379 157297271561250369701537069)
        ·
          refine ⟨58986476835468888638076401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157297271561250369701537069 58986476835468888638076401)
          ·
            refine ⟨44239857626601666478557301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58986476835468888638076401 44239857626601666478557301)
            ·
              refine ⟨4147486652493906232364747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44239857626601666478557301 4147486652493906232364747)
              ·
                refine ⟨6221229978740859348547121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4147486652493906232364747 6221229978740859348547121)
                ·
                  refine ⟨4665922484055644511410341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6221229978740859348547121 4665922484055644511410341)
                  ·
                    refine ⟨874860465760433345889439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4665922484055644511410341 874860465760433345889439)
                    ·
                      rfl

theorem cell23_5111354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_5111354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111354 prefixEnd_5111354 := by exact prefixLift 5111354
  have htrace : WordTrace (prefixWord ++ tailWord_5111354) baseStart_5111354 baseEnd_5111354 := by
    simpa [prefixWord, tailWord_5111354, baseEnd_5111354] using wordTrace_append hprefix tailTrace_5111354
  have hstable : (prefixWord ++ tailWord_5111354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111354).length < 2 ^ (prefixWord ++ tailWord_5111354).sum := by decide
  have hdescent : baseEnd_5111354 < baseStart_5111354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111357 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_5111357 : Nat := 118140960795 + 5111357 * 2 ^ 59
def prefixEnd_5111357 : Nat := 4983230072969 + 3 ^ 40 * 5111357 * 2
def baseEnd_5111357 : Nat := 2624582937723263525930803

theorem tailTrace_5111357 : CollatzResearch.WordTrace tailWord_5111357 prefixEnd_5111357 2624582937723263525930803 := by
  unfold tailWord_5111357
  simp only [CollatzResearch.WordTrace]
  refine ⟨186426505343434014121588325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124284336895622676081058883 186426505343434014121588325)
  ·
    refine ⟨34954969751893877647797811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186426505343434014121588325 34954969751893877647797811)
    ·
      refine ⟨52432454627840816471696717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34954969751893877647797811 52432454627840816471696717)
      ·
        refine ⟨19662170485440306176886269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52432454627840816471696717 19662170485440306176886269)
        ·
          refine ⟨7373313932040114816332351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19662170485440306176886269 7373313932040114816332351)
          ·
            refine ⟨11059970898060172224498527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7373313932040114816332351 11059970898060172224498527)
            ·
              refine ⟨16589956347090258336747791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11059970898060172224498527 16589956347090258336747791)
              ·
                refine ⟨24884934520635387505121687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16589956347090258336747791 24884934520635387505121687)
                ·
                  refine ⟨37327401780953081257682531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24884934520635387505121687 37327401780953081257682531)
                  ·
                    refine ⟨55991102671429621886523797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37327401780953081257682531 55991102671429621886523797)
                    ·
                      refine ⟨2624582937723263525930803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55991102671429621886523797 2624582937723263525930803)
                      ·
                        rfl

theorem cell23_5111357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_5111357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111357 prefixEnd_5111357 := by exact prefixLift 5111357
  have htrace : WordTrace (prefixWord ++ tailWord_5111357) baseStart_5111357 baseEnd_5111357 := by
    simpa [prefixWord, tailWord_5111357, baseEnd_5111357] using wordTrace_append hprefix tailTrace_5111357
  have hstable : (prefixWord ++ tailWord_5111357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111357).length < 2 ^ (prefixWord ++ tailWord_5111357).sum := by decide
  have hdescent : baseEnd_5111357 < baseStart_5111357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111377 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 6, 1, 3]
def baseStart_5111377 : Nat := 118140960795 + 5111377 * 2 ^ 59
def prefixEnd_5111377 : Nat := 4983230072969 + 3 ^ 40 * 5111377 * 2
def baseEnd_5111377 : Nat := 2624593207336353447680711

theorem tailTrace_5111377 : CollatzResearch.WordTrace tailWord_5111377 prefixEnd_5111377 2624593207336353447680711 := by
  unfold tailWord_5111377
  simp only [CollatzResearch.WordTrace]
  refine ⟨186427234803361557537316385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124284823202241038358210923 186427234803361557537316385)
  ·
    refine ⟨139820426102521168152987289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186427234803361557537316385 139820426102521168152987289)
    ·
      refine ⟨104865319576890876114740467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139820426102521168152987289 104865319576890876114740467)
      ·
        refine ⟨157297979365336314172110701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104865319576890876114740467 157297979365336314172110701)
        ·
          refine ⟨58986742262001117814541513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157297979365336314172110701 58986742262001117814541513)
          ·
            refine ⟨44240056696500838360906135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58986742262001117814541513 44240056696500838360906135)
            ·
              refine ⟨66360085044751257541359203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44240056696500838360906135 66360085044751257541359203)
              ·
                refine ⟨99540127567126886312038805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66360085044751257541359203 99540127567126886312038805)
                ·
                  refine ⟨4665943479709072795876819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99540127567126886312038805 4665943479709072795876819)
                  ·
                    refine ⟨6998915219563609193815229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4665943479709072795876819 6998915219563609193815229)
                    ·
                      refine ⟨2624593207336353447680711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6998915219563609193815229 2624593207336353447680711)
                      ·
                        rfl

theorem cell23_5111377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_5111377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111377 prefixEnd_5111377 := by exact prefixLift 5111377
  have htrace : WordTrace (prefixWord ++ tailWord_5111377) baseStart_5111377 baseEnd_5111377 := by
    simpa [prefixWord, tailWord_5111377, baseEnd_5111377] using wordTrace_append hprefix tailTrace_5111377
  have hstable : (prefixWord ++ tailWord_5111377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111377).length < 2 ^ (prefixWord ++ tailWord_5111377).sum := by decide
  have hdescent : baseEnd_5111377 < baseStart_5111377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111378 : List Nat := [3, 2, 2, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_5111378 : Nat := 118140960795 + 5111378 * 2 ^ 59
def prefixEnd_5111378 : Nat := 4983230072969 + 3 ^ 40 * 5111378 * 2
def baseEnd_5111378 : Nat := 2624593720817007943768207

theorem tailTrace_5111378 : CollatzResearch.WordTrace tailWord_5111378 prefixEnd_5111378 2624593720817007943768207 := by
  unfold tailWord_5111378
  simp only [CollatzResearch.WordTrace]
  refine ⟨46606817819089483677025697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124284847517571956472068525 46606817819089483677025697)
  ·
    refine ⟨34955113364317112757769273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46606817819089483677025697 34955113364317112757769273)
    ·
      refine ⟨26216335023237834568326955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34955113364317112757769273 26216335023237834568326955)
      ·
        refine ⟨39324502534856751852490433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26216335023237834568326955 39324502534856751852490433)
        ·
          refine ⟨29493376901142563889367825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39324502534856751852490433 29493376901142563889367825)
          ·
            refine ⟨22120032675856922917025869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29493376901142563889367825 22120032675856922917025869)
            ·
              refine ⟨8295012253446346093884701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22120032675856922917025869 8295012253446346093884701)
              ·
                refine ⟨3110629595042379785206763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8295012253446346093884701 3110629595042379785206763)
                ·
                  refine ⟨4665944392563569677810145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110629595042379785206763 4665944392563569677810145)
                  ·
                    refine ⟨3499458294422677258357609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4665944392563569677810145 3499458294422677258357609)
                    ·
                      refine ⟨2624593720817007943768207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499458294422677258357609 2624593720817007943768207)
                      ·
                        rfl

theorem cell23_5111378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_5111378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111378 prefixEnd_5111378 := by exact prefixLift 5111378
  have htrace : WordTrace (prefixWord ++ tailWord_5111378) baseStart_5111378 baseEnd_5111378 := by
    simpa [prefixWord, tailWord_5111378, baseEnd_5111378] using wordTrace_append hprefix tailTrace_5111378
  have hstable : (prefixWord ++ tailWord_5111378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111378).length < 2 ^ (prefixWord ++ tailWord_5111378).sum := by decide
  have hdescent : baseEnd_5111378 < baseStart_5111378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111421 : List Nat := [1, 4, 1, 1, 4, 1, 3, 2, 1, 3, 2]
def baseStart_5111421 : Nat := 118140960795 + 5111421 * 2 ^ 59
def prefixEnd_5111421 : Nat := 4983230072969 + 3 ^ 40 * 5111421 * 2
def baseEnd_5111421 : Nat := 2624615800485151275530509

theorem tailTrace_5111421 : CollatzResearch.WordTrace tailWord_5111421 prefixEnd_5111421 2624615800485151275530509 := by
  unfold tailWord_5111421
  simp only [CollatzResearch.WordTrace]
  refine ⟨186428839615202153051918117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124285893076801435367945411 186428839615202153051918117)
  ·
    refine ⟨34955407427850403697234647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186428839615202153051918117 34955407427850403697234647)
    ·
      refine ⟨52433111141775605545851971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34955407427850403697234647 52433111141775605545851971)
      ·
        refine ⟨78649666712663408318777957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52433111141775605545851971 78649666712663408318777957)
        ·
          refine ⟨14746812508624389059770867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78649666712663408318777957 14746812508624389059770867)
          ·
            refine ⟨22120218762936583589656301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14746812508624389059770867 22120218762936583589656301)
            ·
              refine ⟨8295082036101218846121113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22120218762936583589656301 8295082036101218846121113)
              ·
                refine ⟨6221311527075914134590835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8295082036101218846121113 6221311527075914134590835)
                ·
                  refine ⟨9331967290613871201886253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6221311527075914134590835 9331967290613871201886253)
                  ·
                    refine ⟨3499487733980201700707345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9331967290613871201886253 3499487733980201700707345)
                    ·
                      refine ⟨2624615800485151275530509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499487733980201700707345 2624615800485151275530509)
                      ·
                        rfl

theorem cell23_5111421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_5111421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111421 prefixEnd_5111421 := by exact prefixLift 5111421
  have htrace : WordTrace (prefixWord ++ tailWord_5111421) baseStart_5111421 baseEnd_5111421 := by
    simpa [prefixWord, tailWord_5111421, baseEnd_5111421] using wordTrace_append hprefix tailTrace_5111421
  have hstable : (prefixWord ++ tailWord_5111421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111421).length < 2 ^ (prefixWord ++ tailWord_5111421).sum := by decide
  have hdescent : baseEnd_5111421 < baseStart_5111421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111434 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 3, 4, 2]
def baseStart_5111434 : Nat := 118140960795 + 5111434 * 2 ^ 59
def prefixEnd_5111434 : Nat := 4983230072969 + 3 ^ 40 * 5111434 * 2
def baseEnd_5111434 : Nat := 2624622475733659724667949

theorem tailTrace_5111434 : CollatzResearch.WordTrace tailWord_5111434 prefixEnd_5111434 2624622475733659724667949 := by
  unfold tailWord_5111434
  simp only [CollatzResearch.WordTrace]
  refine ⟨46607328441038764068035339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124286209176103370848094237 46607328441038764068035339)
  ·
    refine ⟨69910992661558146102053009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46607328441038764068035339 69910992661558146102053009)
    ·
      refine ⟨52433244496168609576539757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69910992661558146102053009 52433244496168609576539757)
      ·
        refine ⟨19662466686063228591202409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52433244496168609576539757 19662466686063228591202409)
        ·
          refine ⟨14746850014547421443401807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19662466686063228591202409 14746850014547421443401807)
          ·
            refine ⟨22120275021821132165102711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14746850014547421443401807 22120275021821132165102711)
            ·
              refine ⟨33180412532731698247654067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22120275021821132165102711 33180412532731698247654067)
              ·
                refine ⟨49770618799097547371481101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33180412532731698247654067 49770618799097547371481101)
                ·
                  refine ⟨18663982049661580264305413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49770618799097547371481101 18663982049661580264305413)
                  ·
                    refine ⟨3499496634311546299557265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18663982049661580264305413 3499496634311546299557265)
                    ·
                      refine ⟨2624622475733659724667949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499496634311546299557265 2624622475733659724667949)
                      ·
                        rfl

theorem cell23_5111434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_5111434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111434 prefixEnd_5111434 := by exact prefixLift 5111434
  have htrace : WordTrace (prefixWord ++ tailWord_5111434) baseStart_5111434 baseEnd_5111434 := by
    simpa [prefixWord, tailWord_5111434, baseEnd_5111434] using wordTrace_append hprefix tailTrace_5111434
  have hstable : (prefixWord ++ tailWord_5111434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111434).length < 2 ^ (prefixWord ++ tailWord_5111434).sum := by decide
  have hdescent : baseEnd_5111434 < baseStart_5111434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111438 : List Nat := [4, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2]
def baseStart_5111438 : Nat := 118140960795 + 5111438 * 2 ^ 59
def prefixEnd_5111438 : Nat := 4983230072969 + 3 ^ 40 * 5111438 * 2
def baseEnd_5111438 : Nat := 2624624529656277709017931

theorem tailTrace_5111438 : CollatzResearch.WordTrace tailWord_5111438 prefixEnd_5111438 2624624529656277709017931 := by
  unfold tailWord_5111438
  simp only [CollatzResearch.WordTrace]
  refine ⟨23303682457017570619410871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124286306437427043303524645 23303682457017570619410871)
  ·
    refine ⟨34955523685526355929116307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23303682457017570619410871 34955523685526355929116307)
    ·
      refine ⟨52433285528289533893674461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34955523685526355929116307 52433285528289533893674461)
      ·
        refine ⟨19662482073108575210127923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52433285528289533893674461 19662482073108575210127923)
        ·
          refine ⟨29493723109662862815191885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19662482073108575210127923 29493723109662862815191885)
          ·
            refine ⟨11060146166123573555696957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29493723109662862815191885 11060146166123573555696957)
            ·
              refine ⟨4147554812296340083386359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11060146166123573555696957 4147554812296340083386359)
              ·
                refine ⟨6221332218444510125079539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4147554812296340083386359 6221332218444510125079539)
                ·
                  refine ⟨9331998327666765187619309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6221332218444510125079539 9331998327666765187619309)
                  ·
                    refine ⟨3499499372875036945357241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9331998327666765187619309 3499499372875036945357241)
                    ·
                      refine ⟨2624624529656277709017931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499499372875036945357241 2624624529656277709017931)
                      ·
                        rfl

theorem cell23_5111438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_5111438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111438 prefixEnd_5111438 := by exact prefixLift 5111438
  have htrace : WordTrace (prefixWord ++ tailWord_5111438) baseStart_5111438 baseEnd_5111438 := by
    simpa [prefixWord, tailWord_5111438, baseEnd_5111438] using wordTrace_append hprefix tailTrace_5111438
  have hstable : (prefixWord ++ tailWord_5111438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111438).length < 2 ^ (prefixWord ++ tailWord_5111438).sum := by decide
  have hdescent : baseEnd_5111438 < baseStart_5111438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111454 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_5111454 : Nat := 118140960795 + 5111454 * 2 ^ 59
def prefixEnd_5111454 : Nat := 4983230072969 + 3 ^ 40 * 5111454 * 2
def baseEnd_5111454 : Nat := 2624632745346749646417857

theorem tailTrace_5111454 : CollatzResearch.WordTrace tailWord_5111454 prefixEnd_5111454 2624632745346749646417857 := by
  unfold tailWord_5111454
  simp only [CollatzResearch.WordTrace]
  refine ⟨23303755403010324960983677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124286695482721733125246277 23303755403010324960983677)
  ·
    refine ⟨8738908276128871860368879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23303755403010324960983677 8738908276128871860368879)
    ·
      refine ⟨13108362414193307790553319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8738908276128871860368879 13108362414193307790553319)
      ·
        refine ⟨19662543621289961685829979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13108362414193307790553319 19662543621289961685829979)
        ·
          refine ⟨29493815431934942528744969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19662543621289961685829979 29493815431934942528744969)
          ·
            refine ⟨22120361573951206896558727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29493815431934942528744969 22120361573951206896558727)
            ·
              refine ⟨33180542360926810344838091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22120361573951206896558727 33180542360926810344838091)
              ·
                refine ⟨49770813541390215517257137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33180542360926810344838091 49770813541390215517257137)
                ·
                  refine ⟨37328110156042661637942853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49770813541390215517257137 37328110156042661637942853)
                  ·
                    refine ⟨6999020654257999057114285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37328110156042661637942853 6999020654257999057114285)
                    ·
                      refine ⟨2624632745346749646417857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6999020654257999057114285 2624632745346749646417857)
                      ·
                        rfl

theorem cell23_5111454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_5111454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111454 prefixEnd_5111454 := by exact prefixLift 5111454
  have htrace : WordTrace (prefixWord ++ tailWord_5111454) baseStart_5111454 baseEnd_5111454 := by
    simpa [prefixWord, tailWord_5111454, baseEnd_5111454] using wordTrace_append hprefix tailTrace_5111454
  have hstable : (prefixWord ++ tailWord_5111454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111454).length < 2 ^ (prefixWord ++ tailWord_5111454).sum := by decide
  have hdescent : baseEnd_5111454 < baseStart_5111454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111480 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_5111480 : Nat := 118140960795 + 5111480 * 2 ^ 59
def prefixEnd_5111480 : Nat := 4983230072969 + 3 ^ 40 * 5111480 * 2
def baseEnd_5111480 : Nat := 2624646095843766544692737

theorem tailTrace_5111480 : CollatzResearch.WordTrace tailWord_5111480 prefixEnd_5111480 2624646095843766544692737 := by
  unfold tailWord_5111480
  simp only [CollatzResearch.WordTrace]
  refine ⟨93215495760994203064157947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124287327681325604085543929 93215495760994203064157947)
  ·
    refine ⟨139823243641491304596236921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93215495760994203064157947 139823243641491304596236921)
    ·
      refine ⟨104867432731118478447177691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139823243641491304596236921 104867432731118478447177691)
      ·
        refine ⟨157301149096677717670766537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104867432731118478447177691 157301149096677717670766537)
        ·
          refine ⟨117975861822508288253074903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157301149096677717670766537 117975861822508288253074903)
          ·
            refine ⟨176963792733762432379612355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117975861822508288253074903 176963792733762432379612355)
            ·
              refine ⟨265445689100643648569418533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176963792733762432379612355 265445689100643648569418533)
              ·
                refine ⟨49771066706370684106765975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 265445689100643648569418533 49771066706370684106765975)
                ·
                  refine ⟨74656600059556026160148963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49771066706370684106765975 74656600059556026160148963)
                  ·
                    refine ⟨111984900089334039240223445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74656600059556026160148963 111984900089334039240223445)
                    ·
                      refine ⟨2624646095843766544692737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111984900089334039240223445 2624646095843766544692737)
                      ·
                        rfl

theorem cell23_5111480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_5111480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111480 prefixEnd_5111480 := by exact prefixLift 5111480
  have htrace : WordTrace (prefixWord ++ tailWord_5111480) baseStart_5111480 baseEnd_5111480 := by
    simpa [prefixWord, tailWord_5111480, baseEnd_5111480] using wordTrace_append hprefix tailTrace_5111480
  have hstable : (prefixWord ++ tailWord_5111480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111480).length < 2 ^ (prefixWord ++ tailWord_5111480).sum := by decide
  have hdescent : baseEnd_5111480 < baseStart_5111480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111501 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_5111501 : Nat := 118140960795 + 5111501 * 2 ^ 59
def prefixEnd_5111501 : Nat := 4983230072969 + 3 ^ 40 * 5111501 * 2
def baseEnd_5111501 : Nat := 2624656878937510962530141

theorem tailTrace_5111501 : CollatzResearch.WordTrace tailWord_5111501 prefixEnd_5111501 2624656878937510962530141 := by
  unfold tailWord_5111501
  simp only [CollatzResearch.WordTrace]
  refine ⟨186431757454912326714830357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124287838303274884476553571 186431757454912326714830357)
  ·
    refine ⟨8738988630699015314757673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 186431757454912326714830357 8738988630699015314757673)
    ·
      refine ⟨6554241473024261486068255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8738988630699015314757673 6554241473024261486068255)
      ·
        refine ⟨9831362209536392229102383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6554241473024261486068255 9831362209536392229102383)
        ·
          refine ⟨14747043314304588343653575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9831362209536392229102383 14747043314304588343653575)
          ·
            refine ⟨22120564971456882515480363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14747043314304588343653575 22120564971456882515480363)
            ·
              refine ⟨33180847457185323773220545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22120564971456882515480363 33180847457185323773220545)
              ·
                refine ⟨24885635592888992829915409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33180847457185323773220545 24885635592888992829915409)
                ·
                  refine ⟨18664226694666744622436557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24885635592888992829915409 18664226694666744622436557)
                  ·
                    refine ⟨6999085010500029233413709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18664226694666744622436557 6999085010500029233413709)
                    ·
                      refine ⟨2624656878937510962530141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6999085010500029233413709 2624656878937510962530141)
                      ·
                        rfl

theorem cell23_5111501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_5111501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111501 prefixEnd_5111501 := by exact prefixLift 5111501
  have htrace : WordTrace (prefixWord ++ tailWord_5111501) baseStart_5111501 baseEnd_5111501 := by
    simpa [prefixWord, tailWord_5111501, baseEnd_5111501] using wordTrace_append hprefix tailTrace_5111501
  have hstable : (prefixWord ++ tailWord_5111501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111501).length < 2 ^ (prefixWord ++ tailWord_5111501).sum := by decide
  have hdescent : baseEnd_5111501 < baseStart_5111501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111524 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 2, 4, 2]
def baseStart_5111524 : Nat := 118140960795 + 5111524 * 2 ^ 59
def prefixEnd_5111524 : Nat := 4983230072969 + 3 ^ 40 * 5111524 * 2
def baseEnd_5111524 : Nat := 2624668688992564372542535

theorem tailTrace_5111524 : CollatzResearch.WordTrace tailWord_5111524 prefixEnd_5111524 2624668688992564372542535 := by
  unfold tailWord_5111524
  simp only [CollatzResearch.WordTrace]
  refine ⟨93216298166914500821458813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124288397555886001095278417 93216298166914500821458813)
  ·
    refine ⟨34956111812592937808047055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93216298166914500821458813 34956111812592937808047055)
    ·
      refine ⟨52434167718889406712070583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34956111812592937808047055 52434167718889406712070583)
      ·
        refine ⟨78651251578334110068105875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52434167718889406712070583 78651251578334110068105875)
        ·
          refine ⟨117976877367501165102158813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78651251578334110068105875 117976877367501165102158813)
          ·
            refine ⟨44241329012812936913309555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117976877367501165102158813 44241329012812936913309555)
            ·
              refine ⟨66361993519219405369964333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44241329012812936913309555 66361993519219405369964333)
              ·
                refine ⟨24885747569707277013736625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66361993519219405369964333 24885747569707277013736625)
                ·
                  refine ⟨18664310677280457760302469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24885747569707277013736625 18664310677280457760302469)
                  ·
                    refine ⟨3499558251990085830056713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18664310677280457760302469 3499558251990085830056713)
                    ·
                      refine ⟨2624668688992564372542535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499558251990085830056713 2624668688992564372542535)
                      ·
                        rfl

theorem cell23_5111524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_5111524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111524 prefixEnd_5111524 := by exact prefixLift 5111524
  have htrace : WordTrace (prefixWord ++ tailWord_5111524) baseStart_5111524 baseEnd_5111524 := by
    simpa [prefixWord, tailWord_5111524, baseEnd_5111524] using wordTrace_append hprefix tailTrace_5111524
  have hstable : (prefixWord ++ tailWord_5111524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111524).length < 2 ^ (prefixWord ++ tailWord_5111524).sum := by decide
  have hdescent : baseEnd_5111524 < baseStart_5111524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111534 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_5111534 : Nat := 118140960795 + 5111534 * 2 ^ 59
def prefixEnd_5111534 : Nat := 4983230072969 + 3 ^ 40 * 5111534 * 2
def baseEnd_5111534 : Nat := 874891274599703111139163

theorem tailTrace_5111534 : CollatzResearch.WordTrace tailWord_5111534 prefixEnd_5111534 874891274599703111139163 := by
  unfold tailWord_5111534
  simp only [CollatzResearch.WordTrace]
  refine ⟨23304120132974096668847707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124288640709195182233854437 23304120132974096668847707)
  ·
    refine ⟨34956180199461145003271561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23304120132974096668847707 34956180199461145003271561)
    ·
      refine ⟨26217135149595858752453671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34956180199461145003271561 26217135149595858752453671)
      ·
        refine ⟨39325702724393788128680507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26217135149595858752453671 39325702724393788128680507)
        ·
          refine ⟨58988554086590682193020761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39325702724393788128680507 58988554086590682193020761)
          ·
            refine ⟨44241415564943011644765571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58988554086590682193020761 44241415564943011644765571)
            ·
              refine ⟨66362123347414517467148357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44241415564943011644765571 66362123347414517467148357)
              ·
                refine ⟨12442898127640222025090317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66362123347414517467148357 12442898127640222025090317)
                ·
                  refine ⟨4666086797865083259408869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12442898127640222025090317 4666086797865083259408869)
                  ·
                    refine ⟨874891274599703111139163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4666086797865083259408869 874891274599703111139163)
                    ·
                      rfl

theorem cell23_5111534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_5111534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111534 prefixEnd_5111534 := by exact prefixLift 5111534
  have htrace : WordTrace (prefixWord ++ tailWord_5111534) baseStart_5111534 baseEnd_5111534 := by
    simpa [prefixWord, tailWord_5111534, baseEnd_5111534] using wordTrace_append hprefix tailTrace_5111534
  have hstable : (prefixWord ++ tailWord_5111534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111534).length < 2 ^ (prefixWord ++ tailWord_5111534).sum := by decide
  have hdescent : baseEnd_5111534 < baseStart_5111534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111551 : List Nat := [1, 1, 2, 2, 1, 3, 5, 3, 1, 4]
def baseStart_5111551 : Nat := 118140960795 + 5111551 * 2 ^ 59
def prefixEnd_5111551 : Nat := 4983230072969 + 3 ^ 40 * 5111551 * 2
def baseEnd_5111551 : Nat := 874894184323411922301637

theorem tailTrace_5111551 : CollatzResearch.WordTrace tailWord_5111551 prefixEnd_5111551 874894184323411922301637 := by
  unfold tailWord_5111551
  simp only [CollatzResearch.WordTrace]
  refine ⟨186433581104731185254150507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124289054069820790169433671 186433581104731185254150507)
  ·
    refine ⟨279650371657096777881225761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186433581104731185254150507 279650371657096777881225761)
    ·
      refine ⟨209737778742822583410919321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279650371657096777881225761 209737778742822583410919321)
      ·
        refine ⟨157303334057116937558189491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209737778742822583410919321 157303334057116937558189491)
        ·
          refine ⟨235955001085675406337284237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157303334057116937558189491 235955001085675406337284237)
          ·
            refine ⟨88483125407128277376481589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235955001085675406337284237 88483125407128277376481589)
            ·
              refine ⟨8295293006918276004045149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88483125407128277376481589 8295293006918276004045149)
              ·
                refine ⟨3110734877594353501516931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8295293006918276004045149 3110734877594353501516931)
                ·
                  refine ⟨4666102316391530252275397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110734877594353501516931 4666102316391530252275397)
                  ·
                    refine ⟨874894184323411922301637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4666102316391530252275397 874894184323411922301637)
                    ·
                      rfl

theorem cell23_5111551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 1, 4].length) (baseStart_5111551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111551 prefixEnd_5111551 := by exact prefixLift 5111551
  have htrace : WordTrace (prefixWord ++ tailWord_5111551) baseStart_5111551 baseEnd_5111551 := by
    simpa [prefixWord, tailWord_5111551, baseEnd_5111551] using wordTrace_append hprefix tailTrace_5111551
  have hstable : (prefixWord ++ tailWord_5111551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111551).length < 2 ^ (prefixWord ++ tailWord_5111551).sum := by decide
  have hdescent : baseEnd_5111551 < baseStart_5111551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111565 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_5111565 : Nat := 118140960795 + 5111565 * 2 ^ 59
def prefixEnd_5111565 : Nat := 4983230072969 + 3 ^ 40 * 5111565 * 2
def baseEnd_5111565 : Nat := 2624689741699398712129847

theorem tailTrace_5111565 : CollatzResearch.WordTrace tailWord_5111565 prefixEnd_5111565 2624689741699398712129847 := by
  unfold tailWord_5111565
  simp only [CollatzResearch.WordTrace]
  refine ⟨186434091726680465645160149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124289394484453643763440099 186434091726680465645160149)
  ·
    refine ⟨4369549024844073413558441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 186434091726680465645160149 4369549024844073413558441)
    ·
      refine ⟨3277161768633055060168831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4369549024844073413558441 3277161768633055060168831)
      ·
        refine ⟨4915742652949582590253247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3277161768633055060168831 4915742652949582590253247)
        ·
          refine ⟨7373613979424373885379871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4915742652949582590253247 7373613979424373885379871)
          ·
            refine ⟨11060420969136560828069807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7373613979424373885379871 11060420969136560828069807)
            ·
              refine ⟨16590631453704841242104711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11060420969136560828069807 16590631453704841242104711)
              ·
                refine ⟨24885947180557261863157067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16590631453704841242104711 24885947180557261863157067)
                ·
                  refine ⟨37328920770835892794735601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24885947180557261863157067 37328920770835892794735601)
                  ·
                    refine ⟨27996690578126919596051701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37328920770835892794735601 27996690578126919596051701)
                    ·
                      refine ⟨2624689741699398712129847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27996690578126919596051701 2624689741699398712129847)
                      ·
                        rfl

theorem cell23_5111565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_5111565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111565 prefixEnd_5111565 := by exact prefixLift 5111565
  have htrace : WordTrace (prefixWord ++ tailWord_5111565) baseStart_5111565 baseEnd_5111565 := by
    simpa [prefixWord, tailWord_5111565, baseEnd_5111565] using wordTrace_append hprefix tailTrace_5111565
  have hstable : (prefixWord ++ tailWord_5111565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111565).length < 2 ^ (prefixWord ++ tailWord_5111565).sum := by decide
  have hdescent : baseEnd_5111565 < baseStart_5111565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111601 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 2, 3, 2]
def baseStart_5111601 : Nat := 118140960795 + 5111601 * 2 ^ 59
def prefixEnd_5111601 : Nat := 4983230072969 + 3 ^ 40 * 5111601 * 2
def baseEnd_5111601 : Nat := 2624708227002960571279681

theorem tailTrace_5111601 : CollatzResearch.WordTrace tailWord_5111601 prefixEnd_5111601 2624708227002960571279681 := by
  unfold tailWord_5111601
  simp only [CollatzResearch.WordTrace]
  refine ⟨186435404754550043793470657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124290269836366695862313771 186435404754550043793470657)
  ·
    refine ⟨139826553565912532845102993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186435404754550043793470657 139826553565912532845102993)
    ·
      refine ⟨104869915174434399633827245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139826553565912532845102993 104869915174434399633827245)
      ·
        refine ⟨39326218190412899862685217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104869915174434399633827245 39326218190412899862685217)
        ·
          refine ⟨29494663642809674897013913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39326218190412899862685217 29494663642809674897013913)
          ·
            refine ⟨22120997732107256172760435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29494663642809674897013913 22120997732107256172760435)
            ·
              refine ⟨33181496598160884259140653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22120997732107256172760435 33181496598160884259140653)
              ·
                refine ⟨12443061224310331597177745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33181496598160884259140653 12443061224310331597177745)
                ·
                  refine ⟨9332295918232748697883309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12443061224310331597177745 9332295918232748697883309)
                  ·
                    refine ⟨3499610969337280761706241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9332295918232748697883309 3499610969337280761706241)
                    ·
                      refine ⟨2624708227002960571279681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499610969337280761706241 2624708227002960571279681)
                      ·
                        rfl

theorem cell23_5111601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_5111601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111601 prefixEnd_5111601 := by exact prefixLift 5111601
  have htrace : WordTrace (prefixWord ++ tailWord_5111601) baseStart_5111601 baseEnd_5111601 := by
    simpa [prefixWord, tailWord_5111601, baseEnd_5111601] using wordTrace_append hprefix tailTrace_5111601
  have hstable : (prefixWord ++ tailWord_5111601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111601).length < 2 ^ (prefixWord ++ tailWord_5111601).sum := by decide
  have hdescent : baseEnd_5111601 < baseStart_5111601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111648 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 3, 2, 2]
def baseStart_5111648 : Nat := 118140960795 + 5111648 * 2 ^ 59
def prefixEnd_5111648 : Nat := 4983230072969 + 3 ^ 40 * 5111648 * 2
def baseEnd_5111648 : Nat := 2624732360593721887391965

theorem tailTrace_5111648 : CollatzResearch.WordTrace tailWord_5111648 prefixEnd_5111648 2624732360593721887391965 := by
  unfold tailWord_5111648
  simp only [CollatzResearch.WordTrace]
  refine ⟨93218559492689885410215799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124291412656919847213621065 93218559492689885410215799)
  ·
    refine ⟨139827839239034828115323699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93218559492689885410215799 139827839239034828115323699)
    ·
      refine ⟨209741758858552242172985549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139827839239034828115323699 209741758858552242172985549)
      ·
        refine ⟨78653159571957090814869581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209741758858552242172985549 78653159571957090814869581)
        ·
          refine ⟨29494934839483909055576093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78653159571957090814869581 29494934839483909055576093)
          ·
            refine ⟨11060600564806465895841035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29494934839483909055576093 11060600564806465895841035)
            ·
              refine ⟨16590900847209698843761553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11060600564806465895841035 16590900847209698843761553)
              ·
                refine ⟨12443175635407274132821165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16590900847209698843761553 12443175635407274132821165)
                ·
                  refine ⟨4666190863277727799807937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12443175635407274132821165 4666190863277727799807937)
                  ·
                    refine ⟨3499643147458295849855953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4666190863277727799807937 3499643147458295849855953)
                    ·
                      refine ⟨2624732360593721887391965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499643147458295849855953 2624732360593721887391965)
                      ·
                        rfl

theorem cell23_5111648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_5111648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111648 prefixEnd_5111648 := by exact prefixLift 5111648
  have htrace : WordTrace (prefixWord ++ tailWord_5111648) baseStart_5111648 baseEnd_5111648 := by
    simpa [prefixWord, tailWord_5111648, baseEnd_5111648] using wordTrace_append hprefix tailTrace_5111648
  have hstable : (prefixWord ++ tailWord_5111648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111648).length < 2 ^ (prefixWord ++ tailWord_5111648).sum := by decide
  have hdescent : baseEnd_5111648 < baseStart_5111648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111665 : List Nat := [1, 2, 2, 2, 1, 3, 4, 3, 1, 2, 2]
def baseStart_5111665 : Nat := 118140960795 + 5111665 * 2 ^ 59
def prefixEnd_5111665 : Nat := 4983230072969 + 3 ^ 40 * 5111665 * 2
def baseEnd_5111665 : Nat := 2624741089764848320879387

theorem tailTrace_5111665 : CollatzResearch.WordTrace tailWord_5111665 prefixEnd_5111665 2624741089764848320879387 := by
  unfold tailWord_5111665
  simp only [CollatzResearch.WordTrace]
  refine ⟨186437739026318182723800449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124291826017545455149200299 186437739026318182723800449)
  ·
    refine ⟨139828304269738637042850337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186437739026318182723800449 139828304269738637042850337)
    ·
      refine ⟨104871228202303977782137753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139828304269738637042850337 104871228202303977782137753)
      ·
        refine ⟨78653421151727983336603315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104871228202303977782137753 78653421151727983336603315)
        ·
          refine ⟨117980131727591975004904973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78653421151727983336603315 117980131727591975004904973)
          ·
            refine ⟨44242549397846990626839365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117980131727591975004904973 44242549397846990626839365)
            ·
              refine ⟨8295478012096310742532381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44242549397846990626839365 8295478012096310742532381)
              ·
                refine ⟨3110804254536116528449643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8295478012096310742532381 3110804254536116528449643)
                ·
                  refine ⟨4666206381804174792674465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110804254536116528449643 4666206381804174792674465)
                  ·
                    refine ⟨3499654786353131094505849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4666206381804174792674465 3499654786353131094505849)
                    ·
                      refine ⟨2624741089764848320879387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499654786353131094505849 2624741089764848320879387)
                      ·
                        rfl

theorem cell23_5111665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_5111665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111665 prefixEnd_5111665 := by exact prefixLift 5111665
  have htrace : WordTrace (prefixWord ++ tailWord_5111665) baseStart_5111665 baseEnd_5111665 := by
    simpa [prefixWord, tailWord_5111665, baseEnd_5111665] using wordTrace_append hprefix tailTrace_5111665
  have hstable : (prefixWord ++ tailWord_5111665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111665).length < 2 ^ (prefixWord ++ tailWord_5111665).sum := by decide
  have hdescent : baseEnd_5111665 < baseStart_5111665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111698 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_5111698 : Nat := 118140960795 + 5111698 * 2 ^ 59
def prefixEnd_5111698 : Nat := 4983230072969 + 3 ^ 40 * 5111698 * 2
def baseEnd_5111698 : Nat := 2624758034626446691766735

theorem tailTrace_5111698 : CollatzResearch.WordTrace tailWord_5111698 prefixEnd_5111698 2624758034626446691766735 := by
  unfold tailWord_5111698
  simp only [CollatzResearch.WordTrace]
  refine ⟨46609735658799657339937937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124292628423465752906501165 46609735658799657339937937)
  ·
    refine ⟨34957301744099743004953453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46609735658799657339937937 34957301744099743004953453)
    ·
      refine ⟨13108988154037403626857545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34957301744099743004953453 13108988154037403626857545)
      ·
        refine ⟨9831741115528052720143159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13108988154037403626857545 9831741115528052720143159)
        ·
          refine ⟨14747611673292079080214739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9831741115528052720143159 14747611673292079080214739)
          ·
            refine ⟨22121417509938118620322109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14747611673292079080214739 22121417509938118620322109)
            ·
              refine ⟨8295531566226794482620791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22121417509938118620322109 8295531566226794482620791)
              ·
                refine ⟨12443297349340191723931187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8295531566226794482620791 12443297349340191723931187)
                ·
                  refine ⟨18664946024010287585896781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12443297349340191723931187 18664946024010287585896781)
                  ·
                    refine ⟨6999354759003857844711293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18664946024010287585896781 6999354759003857844711293)
                    ·
                      refine ⟨2624758034626446691766735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6999354759003857844711293 2624758034626446691766735)
                      ·
                        rfl

theorem cell23_5111698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_5111698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111698 prefixEnd_5111698 := by exact prefixLift 5111698
  have htrace : WordTrace (prefixWord ++ tailWord_5111698) baseStart_5111698 baseEnd_5111698 := by
    simpa [prefixWord, tailWord_5111698, baseEnd_5111698] using wordTrace_append hprefix tailTrace_5111698
  have hstable : (prefixWord ++ tailWord_5111698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111698).length < 2 ^ (prefixWord ++ tailWord_5111698).sum := by decide
  have hdescent : baseEnd_5111698 < baseStart_5111698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111789 : List Nat := [1, 5, 1, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_5111789 : Nat := 118140960795 + 5111789 * 2 ^ 59
def prefixEnd_5111789 : Nat := 4983230072969 + 3 ^ 40 * 5111789 * 2
def baseEnd_5111789 : Nat := 2624804761366005835728817

theorem tailTrace_5111789 : CollatzResearch.WordTrace tailWord_5111789 prefixEnd_5111789 2624804761366005835728817 := by
  unfold tailWord_5111789
  simp only [CollatzResearch.WordTrace]
  refine ⟨186442261677868951901314421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124294841118579301267542947 186442261677868951901314421)
  ·
    refine ⟨17478962032300214240748227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186442261677868951901314421 17478962032300214240748227)
    ·
      refine ⟨26218443048450321361122341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17478962032300214240748227 26218443048450321361122341)
      ·
        refine ⟨4915958071584435255210439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26218443048450321361122341 4915958071584435255210439)
        ·
          refine ⟨7373937107376652882815659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4915958071584435255210439 7373937107376652882815659)
          ·
            refine ⟨11060905661064979324223489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7373937107376652882815659 11060905661064979324223489)
            ·
              refine ⟨8295679245798734493167617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11060905661064979324223489 8295679245798734493167617)
              ·
                refine ⟨6221759434349050869875713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8295679245798734493167617 6221759434349050869875713)
                ·
                  refine ⟨4666319575761788152406785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6221759434349050869875713 4666319575761788152406785)
                  ·
                    refine ⟨3499739681821341114305089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4666319575761788152406785 3499739681821341114305089)
                    ·
                      refine ⟨2624804761366005835728817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499739681821341114305089 2624804761366005835728817)
                      ·
                        rfl

theorem cell23_5111789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_5111789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111789 prefixEnd_5111789 := by exact prefixLift 5111789
  have htrace : WordTrace (prefixWord ++ tailWord_5111789) baseStart_5111789 baseEnd_5111789 := by
    simpa [prefixWord, tailWord_5111789, baseEnd_5111789] using wordTrace_append hprefix tailTrace_5111789
  have hstable : (prefixWord ++ tailWord_5111789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111789).length < 2 ^ (prefixWord ++ tailWord_5111789).sum := by decide
  have hdescent : baseEnd_5111789 < baseStart_5111789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111824 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 4]
def baseStart_5111824 : Nat := 118140960795 + 5111824 * 2 ^ 59
def prefixEnd_5111824 : Nat := 4983230072969 + 3 ^ 40 * 5111824 * 2
def baseEnd_5111824 : Nat := 2624822733188913198791155

theorem tailTrace_5111824 : CollatzResearch.WordTrace tailWord_5111824 prefixEnd_5111824 2624822733188913198791155 := by
  unfold tailWord_5111824
  simp only [CollatzResearch.WordTrace]
  refine ⟨93221769116371076439419263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124295692155161435252559017 93221769116371076439419263)
  ·
    refine ⟨139832653674556614659128895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93221769116371076439419263 139832653674556614659128895)
    ·
      refine ⟨209748980511834921988693343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139832653674556614659128895 209748980511834921988693343)
      ·
        refine ⟨314623470767752382983040015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209748980511834921988693343 314623470767752382983040015)
        ·
          refine ⟨471935206151628574474560023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314623470767752382983040015 471935206151628574474560023)
          ·
            refine ⟨707902809227442861711840035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471935206151628574474560023 707902809227442861711840035)
            ·
              refine ⟨1061854213841164292567760053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707902809227442861711840035 1061854213841164292567760053)
              ·
                refine ⟨99548832547609152428227505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1061854213841164292567760053 99548832547609152428227505)
                ·
                  refine ⟨74661624410706864321170629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99548832547609152428227505 74661624410706864321170629)
                  ·
                    refine ⟨13999054577007537060219493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74661624410706864321170629 13999054577007537060219493)
                    ·
                      refine ⟨2624822733188913198791155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13999054577007537060219493 2624822733188913198791155)
                      ·
                        rfl

theorem cell23_5111824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_5111824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111824 prefixEnd_5111824 := by exact prefixLift 5111824
  have htrace : WordTrace (prefixWord ++ tailWord_5111824) baseStart_5111824 baseEnd_5111824 := by
    simpa [prefixWord, tailWord_5111824, baseEnd_5111824] using wordTrace_append hprefix tailTrace_5111824
  have hstable : (prefixWord ++ tailWord_5111824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111824).length < 2 ^ (prefixWord ++ tailWord_5111824).sum := by decide
  have hdescent : baseEnd_5111824 < baseStart_5111824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111868 : List Nat := [2, 2, 2, 2, 2, 1, 5, 1, 6]
def baseStart_5111868 : Nat := 118140960795 + 5111868 * 2 ^ 59
def prefixEnd_5111868 : Nat := 4983230072969 + 3 ^ 40 * 5111868 * 2
def baseEnd_5111868 : Nat := 291649480704190114071217

theorem tailTrace_5111868 : CollatzResearch.WordTrace tailWord_5111868 prefixEnd_5111868 291649480704190114071217 := by
  unfold tailWord_5111868
  simp only [CollatzResearch.WordTrace]
  refine ⟨93222571522291374196720129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124296762029721832262293505 93222571522291374196720129)
  ·
    refine ⟨69916928641718530647540097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93222571522291374196720129 69916928641718530647540097)
    ·
      refine ⟨52437696481288897985655073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69916928641718530647540097 52437696481288897985655073)
      ·
        refine ⟨39328272360966673489241305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52437696481288897985655073 39328272360966673489241305)
        ·
          refine ⟨29496204270725005116930979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39328272360966673489241305 29496204270725005116930979)
          ·
            refine ⟨44244306406087507675396469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29496204270725005116930979 44244306406087507675396469)
            ·
              refine ⟨4147903725570703844568419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44244306406087507675396469 4147903725570703844568419)
              ·
                refine ⟨6221855588356055766852629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4147903725570703844568419 6221855588356055766852629)
                ·
                  refine ⟨291649480704190114071217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6221855588356055766852629 291649480704190114071217)
                  ·
                    rfl

theorem cell23_5111868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_5111868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111868 prefixEnd_5111868 := by exact prefixLift 5111868
  have htrace : WordTrace (prefixWord ++ tailWord_5111868) baseStart_5111868 baseEnd_5111868 := by
    simpa [prefixWord, tailWord_5111868, baseEnd_5111868] using wordTrace_append hprefix tailTrace_5111868
  have hstable : (prefixWord ++ tailWord_5111868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111868).length < 2 ^ (prefixWord ++ tailWord_5111868).sum := by decide
  have hdescent : baseEnd_5111868 < baseStart_5111868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111918 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_5111918 : Nat := 118140960795 + 5111918 * 2 ^ 59
def prefixEnd_5111918 : Nat := 4983230072969 + 3 ^ 40 * 5111918 * 2
def baseEnd_5111918 : Nat := 2624871000370435831015723

theorem tailTrace_5111918 : CollatzResearch.WordTrace tailWord_5111918 prefixEnd_5111918 2624871000370435831015723 := by
  unfold tailWord_5111918
  simp only [CollatzResearch.WordTrace]
  refine ⟨23305870836800200866595051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124297977796267737955173605 23305870836800200866595051)
  ·
    refine ⟨34958806255200301299892577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23305870836800200866595051 34958806255200301299892577)
    ·
      refine ⟨26219104691400225974919433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34958806255200301299892577 26219104691400225974919433)
      ·
        refine ⟨19664328518550169481189575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26219104691400225974919433 19664328518550169481189575)
        ·
          refine ⟨29496492777825254221784363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19664328518550169481189575 29496492777825254221784363)
          ·
            refine ⟨44244739166737881332676545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29496492777825254221784363 44244739166737881332676545)
            ·
              refine ⟨33183554375053410999507409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44244739166737881332676545 33183554375053410999507409)
              ·
                refine ⟨24887665781290058249630557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33183554375053410999507409 24887665781290058249630557)
                ·
                  refine ⟨9332874667983771843611459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24887665781290058249630557 9332874667983771843611459)
                  ·
                    refine ⟨13999312001975657765417189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9332874667983771843611459 13999312001975657765417189)
                    ·
                      refine ⟨2624871000370435831015723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13999312001975657765417189 2624871000370435831015723)
                      ·
                        rfl

theorem cell23_5111918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_5111918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111918 prefixEnd_5111918 := by exact prefixLift 5111918
  have htrace : WordTrace (prefixWord ++ tailWord_5111918) baseStart_5111918 baseEnd_5111918 := by
    simpa [prefixWord, tailWord_5111918, baseEnd_5111918] using wordTrace_append hprefix tailTrace_5111918
  have hstable : (prefixWord ++ tailWord_5111918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111918).length < 2 ^ (prefixWord ++ tailWord_5111918).sum := by decide
  have hdescent : baseEnd_5111918 < baseStart_5111918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111921 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_5111921 : Nat := 118140960795 + 5111921 * 2 ^ 59
def prefixEnd_5111921 : Nat := 4983230072969 + 3 ^ 40 * 5111921 * 2
def baseEnd_5111921 : Nat := 2624872540812399319278209

theorem tailTrace_5111921 : CollatzResearch.WordTrace tailWord_5111921 prefixEnd_5111921 2624872540812399319278209 := by
  unfold tailWord_5111921
  simp only [CollatzResearch.WordTrace]
  refine ⟨186447076113390738445119617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124298050742260492296746411 186447076113390738445119617)
  ·
    refine ⟨139835307085043053833839713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186447076113390738445119617 139835307085043053833839713)
    ·
      refine ⟨104876480313782290375379785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139835307085043053833839713 104876480313782290375379785)
      ·
        refine ⟨78657360235336717781534839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104876480313782290375379785 78657360235336717781534839)
        ·
          refine ⟨117986040353005076672302259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78657360235336717781534839 117986040353005076672302259)
          ·
            refine ⟨176979060529507615008453389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117986040353005076672302259 176979060529507615008453389)
            ·
              refine ⟨66367147698565355628170021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176979060529507615008453389 66367147698565355628170021)
              ·
                refine ⟨12443840193481004180281879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66367147698565355628170021 12443840193481004180281879)
                ·
                  refine ⟨18665760290221506270422819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12443840193481004180281879 18665760290221506270422819)
                  ·
                    refine ⟨27998640435332259405634229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18665760290221506270422819 27998640435332259405634229)
                    ·
                      refine ⟨2624872540812399319278209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27998640435332259405634229 2624872540812399319278209)
                      ·
                        rfl

theorem cell23_5111921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_5111921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111921 prefixEnd_5111921 := by exact prefixLift 5111921
  have htrace : WordTrace (prefixWord ++ tailWord_5111921) baseStart_5111921 baseEnd_5111921 := by
    simpa [prefixWord, tailWord_5111921, baseEnd_5111921] using wordTrace_append hprefix tailTrace_5111921
  have hstable : (prefixWord ++ tailWord_5111921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111921).length < 2 ^ (prefixWord ++ tailWord_5111921).sum := by decide
  have hdescent : baseEnd_5111921 < baseStart_5111921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111941 : List Nat := [1, 3, 1, 1, 5, 1, 2, 9]
def baseStart_5111941 : Nat := 118140960795 + 5111941 * 2 ^ 59
def prefixEnd_5111941 : Nat := 4983230072969 + 3 ^ 40 * 5111941 * 2
def baseEnd_5111941 : Nat := 97217881867610712630671

theorem tailTrace_5111941 : CollatzResearch.WordTrace tailWord_5111941 prefixEnd_5111941 97217881867610712630671 := by
  unfold tailWord_5111941
  simp only [CollatzResearch.WordTrace]
  refine ⟨186447805573318281860847677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124298537048878854573898451 186447805573318281860847677)
  ·
    refine ⟨69917927089994355697817879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186447805573318281860847677 69917927089994355697817879)
    ·
      refine ⟨104876890634991533546726819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69917927089994355697817879 104876890634991533546726819)
      ·
        refine ⟨157315335952487300320090229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104876890634991533546726819 157315335952487300320090229)
        ·
          refine ⟨14748312745545684405008459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157315335952487300320090229 14748312745545684405008459)
          ·
            refine ⟨22122469118318526607512689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14748312745545684405008459 22122469118318526607512689)
            ·
              refine ⟨16591851838738894955634517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22122469118318526607512689 16591851838738894955634517)
              ·
                refine ⟨97217881867610712630671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16591851838738894955634517 97217881867610712630671)
                ·
                  rfl

theorem cell23_5111941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 9].length) (baseStart_5111941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111941 prefixEnd_5111941 := by exact prefixLift 5111941
  have htrace : WordTrace (prefixWord ++ tailWord_5111941) baseStart_5111941 baseEnd_5111941 := by
    simpa [prefixWord, tailWord_5111941, baseEnd_5111941] using wordTrace_append hprefix tailTrace_5111941
  have hstable : (prefixWord ++ tailWord_5111941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111941).length < 2 ^ (prefixWord ++ tailWord_5111941).sum := by decide
  have hdescent : baseEnd_5111941 < baseStart_5111941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111952 : List Nat := [2, 1, 1, 1, 1, 1, 6, 5, 1, 2, 2]
def baseStart_5111952 : Nat := 118140960795 + 5111952 * 2 ^ 59
def prefixEnd_5111952 : Nat := 4983230072969 + 3 ^ 40 * 5111952 * 2
def baseEnd_5111952 : Nat := 2624888458712688697990567

theorem tailTrace_5111952 : CollatzResearch.WordTrace tailWord_5111952 prefixEnd_5111952 2624888458712688697990567 := by
  unfold tailWord_5111952
  simp only [CollatzResearch.WordTrace]
  refine ⟨93224103388139215369749055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124298804517518953826332073 93224103388139215369749055)
  ·
    refine ⟨139836155082208823054623583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93224103388139215369749055 139836155082208823054623583)
    ·
      refine ⟨209754232623313234581935375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139836155082208823054623583 209754232623313234581935375)
      ·
        refine ⟨314631348934969851872903063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209754232623313234581935375 314631348934969851872903063)
        ·
          refine ⟨471947023402454777809354595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314631348934969851872903063 471947023402454777809354595)
          ·
            refine ⟨707920535103682166714031893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471947023402454777809354595 707920535103682166714031893)
            ·
              refine ⟨33183775082985101564720245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 707920535103682166714031893 33183775082985101564720245)
              ·
                refine ⟨3110978914029853271692523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33183775082985101564720245 3110978914029853271692523)
                ·
                  refine ⟨4666468371044779907538785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110978914029853271692523 4666468371044779907538785)
                  ·
                    refine ⟨3499851278283584930654089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4666468371044779907538785 3499851278283584930654089)
                    ·
                      refine ⟨2624888458712688697990567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499851278283584930654089 2624888458712688697990567)
                      ·
                        rfl

theorem cell23_5111952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 1, 2, 2].length) (baseStart_5111952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111952 prefixEnd_5111952 := by exact prefixLift 5111952
  have htrace : WordTrace (prefixWord ++ tailWord_5111952) baseStart_5111952 baseEnd_5111952 := by
    simpa [prefixWord, tailWord_5111952, baseEnd_5111952] using wordTrace_append hprefix tailTrace_5111952
  have hstable : (prefixWord ++ tailWord_5111952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111952).length < 2 ^ (prefixWord ++ tailWord_5111952).sum := by decide
  have hdescent : baseEnd_5111952 < baseStart_5111952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111962 : List Nat := [3, 1, 1, 5, 2, 1, 2, 2, 2, 4]
def baseStart_5111962 : Nat := 118140960795 + 5111962 * 2 ^ 59
def prefixEnd_5111962 : Nat := 4983230072969 + 3 ^ 40 * 5111962 * 2
def baseEnd_5111962 : Nat := 874964531173077886288507

theorem tailTrace_5111962 : CollatzResearch.WordTrace tailWord_5111962 prefixEnd_5111962 874964531173077886288507 := by
  unfold tailWord_5111962
  simp only [CollatzResearch.WordTrace]
  refine ⟨46612142876560550611840535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124299047670828134964908093 46612142876560550611840535)
  ·
    refine ⟨69918214314840825917760803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46612142876560550611840535 69918214314840825917760803)
    ·
      refine ⟨104877321472261238876641205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69918214314840825917760803 104877321472261238876641205)
      ·
        refine ⟨9832248888024491144685113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104877321472261238876641205 9832248888024491144685113)
        ·
          refine ⟨7374186666018368358513835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9832248888024491144685113 7374186666018368358513835)
          ·
            refine ⟨11061279999027552537770753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7374186666018368358513835 11061279999027552537770753)
            ·
              refine ⟨8295959999270664403328065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11061279999027552537770753 8295959999270664403328065)
              ·
                refine ⟨6221969999452998302496049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8295959999270664403328065 6221969999452998302496049)
                ·
                  refine ⟨4666477499589748726872037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6221969999452998302496049 4666477499589748726872037)
                  ·
                    refine ⟨874964531173077886288507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4666477499589748726872037 874964531173077886288507)
                    ·
                      rfl

theorem cell23_5111962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_5111962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111962 prefixEnd_5111962 := by exact prefixLift 5111962
  have htrace : WordTrace (prefixWord ++ tailWord_5111962) baseStart_5111962 baseEnd_5111962 := by
    simpa [prefixWord, tailWord_5111962, baseEnd_5111962] using wordTrace_append hprefix tailTrace_5111962
  have hstable : (prefixWord ++ tailWord_5111962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111962).length < 2 ^ (prefixWord ++ tailWord_5111962).sum := by decide
  have hdescent : baseEnd_5111962 < baseStart_5111962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111969 : List Nat := [1, 2, 3, 3, 1, 3, 1, 4, 1, 2, 2]
def baseStart_5111969 : Nat := 118140960795 + 5111969 * 2 ^ 59
def prefixEnd_5111969 : Nat := 4983230072969 + 3 ^ 40 * 5111969 * 2
def baseEnd_5111969 : Nat := 2624897187883815131477989

theorem tailTrace_5111969 : CollatzResearch.WordTrace tailWord_5111969 prefixEnd_5111969 2624897187883815131477989 := by
  unfold tailWord_5111969
  simp only [CollatzResearch.WordTrace]
  refine ⟨186448826817216842642866961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124299217878144561761911307 186448826817216842642866961)
  ·
    refine ⟨139836620112912631982150221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186448826817216842642866961 139836620112912631982150221)
    ·
      refine ⟨52438732542342236993306333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139836620112912631982150221 52438732542342236993306333)
      ·
        refine ⟨19664524703378338872489875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52438732542342236993306333 19664524703378338872489875)
        ·
          refine ⟨29496787055067508308734813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19664524703378338872489875 29496787055067508308734813)
          ·
            refine ⟨11061295145650315615775555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29496787055067508308734813 11061295145650315615775555)
            ·
              refine ⟨16591942718475473423663333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11061295145650315615775555 16591942718475473423663333)
              ·
                refine ⟨3110989259714151266936875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16591942718475473423663333 3110989259714151266936875)
                ·
                  refine ⟨4666483889571226900405313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110989259714151266936875 4666483889571226900405313)
                  ·
                    refine ⟨3499862917178420175303985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4666483889571226900405313 3499862917178420175303985)
                    ·
                      refine ⟨2624897187883815131477989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499862917178420175303985 2624897187883815131477989)
                      ·
                        rfl

theorem cell23_5111969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_5111969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111969 prefixEnd_5111969 := by exact prefixLift 5111969
  have htrace : WordTrace (prefixWord ++ tailWord_5111969) baseStart_5111969 baseEnd_5111969 := by
    simpa [prefixWord, tailWord_5111969, baseEnd_5111969] using wordTrace_append hprefix tailTrace_5111969
  have hstable : (prefixWord ++ tailWord_5111969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111969).length < 2 ^ (prefixWord ++ tailWord_5111969).sum := by decide
  have hdescent : baseEnd_5111969 < baseStart_5111969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111975 : List Nat := [1, 1, 6, 2, 2, 2, 1, 8]
def baseStart_5111975 : Nat := 118140960795 + 5111975 * 2 ^ 59
def prefixEnd_5111975 : Nat := 4983230072969 + 3 ^ 40 * 5111975 * 2
def baseEnd_5111975 : Nat := 97218528472879337333443

theorem tailTrace_5111975 : CollatzResearch.WordTrace tailWord_5111975 prefixEnd_5111975 97218528472879337333443 := by
  unfold tailWord_5111975
  simp only [CollatzResearch.WordTrace]
  refine ⟨186449045655195105667585379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124299363770130070445056919 186449045655195105667585379)
  ·
    refine ⟨279673568482792658501378069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186449045655195105667585379 279673568482792658501378069)
    ·
      refine ⟨13109698522630905867252097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 279673568482792658501378069 13109698522630905867252097)
      ·
        refine ⟨9832273891973179400439073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13109698522630905867252097 9832273891973179400439073)
        ·
          refine ⟨7374205418979884550329305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9832273891973179400439073 7374205418979884550329305)
          ·
            refine ⟨5530654064234913412746979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7374205418979884550329305 5530654064234913412746979)
            ·
              refine ⟨8295981096352370119120469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5530654064234913412746979 8295981096352370119120469)
              ·
                refine ⟨97218528472879337333443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8295981096352370119120469 97218528472879337333443)
                ·
                  rfl

theorem cell23_5111975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 8].length) (baseStart_5111975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111975 prefixEnd_5111975 := by exact prefixLift 5111975
  have htrace : WordTrace (prefixWord ++ tailWord_5111975) baseStart_5111975 baseEnd_5111975 := by
    simpa [prefixWord, tailWord_5111975, baseEnd_5111975] using wordTrace_append hprefix tailTrace_5111975
  have hstable : (prefixWord ++ tailWord_5111975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111975).length < 2 ^ (prefixWord ++ tailWord_5111975).sum := by decide
  have hdescent : baseEnd_5111975 < baseStart_5111975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5111995 : List Nat := [1, 1, 1, 1, 1, 2, 6, 4, 1, 3, 2]
def baseStart_5111995 : Nat := 118140960795 + 5111995 * 2 ^ 59
def prefixEnd_5111995 : Nat := 4983230072969 + 3 ^ 40 * 5111995 * 2
def baseEnd_5111995 : Nat := 2624910538380832029752869

theorem tailTrace_5111995 : CollatzResearch.WordTrace tailWord_5111995 prefixEnd_5111995 2624910538380832029752869 := by
  unfold tailWord_5111995
  simp only [CollatzResearch.WordTrace]
  refine ⟨186449775115122649083313439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124299850076748432722208959 186449775115122649083313439)
  ·
    refine ⟨279674662672683973624970159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186449775115122649083313439 279674662672683973624970159)
    ·
      refine ⟨419511994009025960437455239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279674662672683973624970159 419511994009025960437455239)
      ·
        refine ⟨629267991013538940656182859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419511994009025960437455239 629267991013538940656182859)
        ·
          refine ⟨943901986520308410984274289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629267991013538940656182859 943901986520308410984274289)
          ·
            refine ⟨707926489890231308238205717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 943901986520308410984274289 707926489890231308238205717)
            ·
              refine ⟨33184054213604592573665893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 707926489890231308238205717 33184054213604592573665893)
              ·
                refine ⟨6222010165050861107562355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33184054213604592573665893 6222010165050861107562355)
                ·
                  refine ⟨9333015247576291661343533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6222010165050861107562355 9333015247576291661343533)
                  ·
                    refine ⟨3499880717841109373003825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9333015247576291661343533 3499880717841109373003825)
                    ·
                      refine ⟨2624910538380832029752869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499880717841109373003825 2624910538380832029752869)
                      ·
                        rfl

theorem cell23_5111995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 3, 2].length) (baseStart_5111995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5111995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5111995 prefixEnd_5111995 := by exact prefixLift 5111995
  have htrace : WordTrace (prefixWord ++ tailWord_5111995) baseStart_5111995 baseEnd_5111995 := by
    simpa [prefixWord, tailWord_5111995, baseEnd_5111995] using wordTrace_append hprefix tailTrace_5111995
  have hstable : (prefixWord ++ tailWord_5111995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5111995).length < 2 ^ (prefixWord ++ tailWord_5111995).sum := by decide
  have hdescent : baseEnd_5111995 < baseStart_5111995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5111995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112011 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 5]
def baseStart_5112011 : Nat := 118140960795 + 5112011 * 2 ^ 59
def prefixEnd_5112011 : Nat := 4983230072969 + 3 ^ 40 * 5112011 * 2
def baseEnd_5112011 : Nat := 2624918754071303967152795

theorem tailTrace_5112011 : CollatzResearch.WordTrace tailWord_5112011 prefixEnd_5112011 2624918754071303967152795 := by
  unfold tailWord_5112011
  simp only [CollatzResearch.WordTrace]
  refine ⟨186450358683064683815895887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124300239122043122543930591 186450358683064683815895887)
  ·
    refine ⟨279675538024597025723843831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186450358683064683815895887 279675538024597025723843831)
    ·
      refine ⟨419513307036895538585765747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279675538024597025723843831 419513307036895538585765747)
      ·
        refine ⟨629269960555343307878648621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419513307036895538585765747 629269960555343307878648621)
        ·
          refine ⟨235976235208253740454493233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 629269960555343307878648621 235976235208253740454493233)
          ·
            refine ⟨176982176406190305340869925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235976235208253740454493233 176982176406190305340869925)
            ·
              refine ⟨33184158076160682251413111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176982176406190305340869925 33184158076160682251413111)
              ·
                refine ⟨49776237114241023377119667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33184158076160682251413111 49776237114241023377119667)
                ·
                  refine ⟨74664355671361535065679501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49776237114241023377119667 74664355671361535065679501)
                  ·
                    refine ⟨27999133376760575649629813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74664355671361535065679501 27999133376760575649629813)
                    ·
                      refine ⟨2624918754071303967152795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27999133376760575649629813 2624918754071303967152795)
                      ·
                        rfl

theorem cell23_5112011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_5112011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112011 prefixEnd_5112011 := by exact prefixLift 5112011
  have htrace : WordTrace (prefixWord ++ tailWord_5112011) baseStart_5112011 baseEnd_5112011 := by
    simpa [prefixWord, tailWord_5112011, baseEnd_5112011] using wordTrace_append hprefix tailTrace_5112011
  have hstable : (prefixWord ++ tailWord_5112011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112011).length < 2 ^ (prefixWord ++ tailWord_5112011).sum := by decide
  have hdescent : baseEnd_5112011 < baseStart_5112011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112018 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_5112018 : Nat := 118140960795 + 5112018 * 2 ^ 59
def prefixEnd_5112018 : Nat := 4983230072969 + 3 ^ 40 * 5112018 * 2
def baseEnd_5112018 : Nat := 874974116145295146588421

theorem tailTrace_5112018 : CollatzResearch.WordTrace tailWord_5112018 prefixEnd_5112018 874974116145295146588421 := by
  unfold tailWord_5112018
  simp only [CollatzResearch.WordTrace]
  refine ⟨46612653498509831002850177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124300409329359549340933805 46612653498509831002850177)
  ·
    refine ⟨34959490123882373252137633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46612653498509831002850177 34959490123882373252137633)
    ·
      refine ⟨26219617592911779939103225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34959490123882373252137633 26219617592911779939103225)
      ·
        refine ⟨19664713194683834954327419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26219617592911779939103225 19664713194683834954327419)
        ·
          refine ⟨29497069792025752431491129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19664713194683834954327419 29497069792025752431491129)
          ·
            refine ⟨22122802344019314323618347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29497069792025752431491129 22122802344019314323618347)
            ·
              refine ⟨33184203516028971485427521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22122802344019314323618347 33184203516028971485427521)
              ·
                refine ⟨24888152637021728614070641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33184203516028971485427521 24888152637021728614070641)
                ·
                  refine ⟨18666114477766296460552981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24888152637021728614070641 18666114477766296460552981)
                  ·
                    refine ⟨874974116145295146588421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18666114477766296460552981 874974116145295146588421)
                    ·
                      rfl

theorem cell23_5112018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_5112018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112018 prefixEnd_5112018 := by exact prefixLift 5112018
  have htrace : WordTrace (prefixWord ++ tailWord_5112018) baseStart_5112018 baseEnd_5112018 := by
    simpa [prefixWord, tailWord_5112018, baseEnd_5112018] using wordTrace_append hprefix tailTrace_5112018
  have hstable : (prefixWord ++ tailWord_5112018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112018).length < 2 ^ (prefixWord ++ tailWord_5112018).sum := by decide
  have hdescent : baseEnd_5112018 < baseStart_5112018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112088 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_5112088 : Nat := 118140960795 + 5112088 * 2 ^ 59
def prefixEnd_5112088 : Nat := 4983230072969 + 3 ^ 40 * 5112088 * 2
def baseEnd_5112088 : Nat := 2624958292081700165889941

theorem tailTrace_5112088 : CollatzResearch.WordTrace tailWord_5112088 prefixEnd_5112088 2624958292081700165889941 := by
  unfold tailWord_5112088
  simp only [CollatzResearch.WordTrace]
  refine ⟨93226583551892862983224459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124302111402523817310965945 93226583551892862983224459)
  ·
    refine ⟨139839875327839294474836689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93226583551892862983224459 139839875327839294474836689)
    ·
      refine ⟨104879906495879470856127517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139839875327839294474836689 104879906495879470856127517)
      ·
        refine ⟨39329964935954801571047819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104879906495879470856127517 39329964935954801571047819)
        ·
          refine ⟨58994947403932202356571729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39329964935954801571047819 58994947403932202356571729)
          ·
            refine ⟨44246210552949151767428797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58994947403932202356571729 44246210552949151767428797)
            ·
              refine ⟨16592328957355931912785799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44246210552949151767428797 16592328957355931912785799)
              ·
                refine ⟨24888493436033897869178699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16592328957355931912785799 24888493436033897869178699)
                ·
                  refine ⟨37332740154050846803768049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24888493436033897869178699 37332740154050846803768049)
                  ·
                    refine ⟨27999555115538135102826037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37332740154050846803768049 27999555115538135102826037)
                    ·
                      refine ⟨2624958292081700165889941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27999555115538135102826037 2624958292081700165889941)
                      ·
                        rfl

theorem cell23_5112088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_5112088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112088 prefixEnd_5112088 := by exact prefixLift 5112088
  have htrace : WordTrace (prefixWord ++ tailWord_5112088) baseStart_5112088 baseEnd_5112088 := by
    simpa [prefixWord, tailWord_5112088, baseEnd_5112088] using wordTrace_append hprefix tailTrace_5112088
  have hstable : (prefixWord ++ tailWord_5112088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112088).length < 2 ^ (prefixWord ++ tailWord_5112088).sum := by decide
  have hdescent : baseEnd_5112088 < baseStart_5112088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112093 : List Nat := [1, 4, 2, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_5112093 : Nat := 118140960795 + 5112093 * 2 ^ 59
def prefixEnd_5112093 : Nat := 4983230072969 + 3 ^ 40 * 5112093 * 2
def baseEnd_5112093 : Nat := 2624960859484972646327419

theorem tailTrace_5112093 : CollatzResearch.WordTrace tailWord_5112093 prefixEnd_5112093 2624960859484972646327419 := by
  unfold tailWord_5112093
  simp only [CollatzResearch.WordTrace]
  refine ⟨186453349468767611820380933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124302232979178407880253955 186453349468767611820380933)
  ·
    refine ⟨34960003025393927216321425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186453349468767611820380933 34960003025393927216321425)
    ·
      refine ⟨26220002269045445412241069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34960003025393927216321425 26220002269045445412241069)
      ·
        refine ⟨9832500850892042029590401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26220002269045445412241069 9832500850892042029590401)
        ·
          refine ⟨7374375638169031522192801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9832500850892042029590401 7374375638169031522192801)
          ·
            refine ⟨5530781728626773641644601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7374375638169031522192801 5530781728626773641644601)
            ·
              refine ⟨4148086296470080231233451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5530781728626773641644601 4148086296470080231233451)
              ·
                refine ⟨6222129444705120346850177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148086296470080231233451 6222129444705120346850177)
                ·
                  refine ⟨4666597083528840260137633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6222129444705120346850177 4666597083528840260137633)
                  ·
                    refine ⟨3499947812646630195103225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4666597083528840260137633 3499947812646630195103225)
                    ·
                      refine ⟨2624960859484972646327419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3499947812646630195103225 2624960859484972646327419)
                      ·
                        rfl

theorem cell23_5112093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_5112093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112093 prefixEnd_5112093 := by exact prefixLift 5112093
  have htrace : WordTrace (prefixWord ++ tailWord_5112093) baseStart_5112093 baseEnd_5112093 := by
    simpa [prefixWord, tailWord_5112093, baseEnd_5112093] using wordTrace_append hprefix tailTrace_5112093
  have hstable : (prefixWord ++ tailWord_5112093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112093).length < 2 ^ (prefixWord ++ tailWord_5112093).sum := by decide
  have hdescent : baseEnd_5112093 < baseStart_5112093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112115 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 4]
def baseStart_5112115 : Nat := 118140960795 + 5112115 * 2 ^ 59
def prefixEnd_5112115 : Nat := 4983230072969 + 3 ^ 40 * 5112115 * 2
def baseEnd_5112115 : Nat := 2624972156059371560252317

theorem tailTrace_5112115 : CollatzResearch.WordTrace tailWord_5112115 prefixEnd_5112115 2624972156059371560252317 := by
  unfold tailWord_5112115
  simp only [CollatzResearch.WordTrace]
  refine ⟨186454151874687909577681799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124302767916458606385121199 186454151874687909577681799)
  ·
    refine ⟨279681227812031864366522699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186454151874687909577681799 279681227812031864366522699)
    ·
      refine ⟨419521841718047796549784049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279681227812031864366522699 419521841718047796549784049)
      ·
        refine ⟨314641381288535847412338037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419521841718047796549784049 314641381288535847412338037)
        ·
          refine ⟨29497629495800235694906691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 314641381288535847412338037 29497629495800235694906691)
          ·
            refine ⟨44246444243700353542360037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29497629495800235694906691 44246444243700353542360037)
            ·
              refine ⟨8296208295693816289192507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44246444243700353542360037 8296208295693816289192507)
              ·
                refine ⟨12444312443540724433788761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8296208295693816289192507 12444312443540724433788761)
                ·
                  refine ⟨9333234332655543325341571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12444312443540724433788761 9333234332655543325341571)
                  ·
                    refine ⟨13999851498983314988012357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9333234332655543325341571 13999851498983314988012357)
                    ·
                      refine ⟨2624972156059371560252317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13999851498983314988012357 2624972156059371560252317)
                      ·
                        rfl

theorem cell23_5112115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 4].length) (baseStart_5112115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112115 prefixEnd_5112115 := by exact prefixLift 5112115
  have htrace : WordTrace (prefixWord ++ tailWord_5112115) baseStart_5112115 baseEnd_5112115 := by
    simpa [prefixWord, tailWord_5112115, baseEnd_5112115] using wordTrace_append hprefix tailTrace_5112115
  have hstable : (prefixWord ++ tailWord_5112115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112115).length < 2 ^ (prefixWord ++ tailWord_5112115).sum := by decide
  have hdescent : baseEnd_5112115 < baseStart_5112115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112135 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_5112135 : Nat := 118140960795 + 5112135 * 2 ^ 59
def prefixEnd_5112135 : Nat := 4983230072969 + 3 ^ 40 * 5112135 * 2
def baseEnd_5112135 : Nat := 2624982425672461482002225

theorem tailTrace_5112135 : CollatzResearch.WordTrace tailWord_5112135 prefixEnd_5112135 2624982425672461482002225 := by
  unfold tailWord_5112135
  simp only [CollatzResearch.WordTrace]
  refine ⟨186454881334615452993409859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124303254223076968662273239 186454881334615452993409859)
  ·
    refine ⟨279682322001923179490114789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186454881334615452993409859 279682322001923179490114789)
    ·
      refine ⟨52440435375360596154396523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279682322001923179490114789 52440435375360596154396523)
      ·
        refine ⟨78660653063040894231594785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52440435375360596154396523 78660653063040894231594785)
        ·
          refine ⟨58995489797280670673696089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78660653063040894231594785 58995489797280670673696089)
          ·
            refine ⟨44246617347960503005272067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58995489797280670673696089 44246617347960503005272067)
            ·
              refine ⟨66369926021940754507908101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44246617347960503005272067 66369926021940754507908101)
              ·
                refine ⟨12444361129113891470232769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66369926021940754507908101 12444361129113891470232769)
                ·
                  refine ⟨9333270846835418602674577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12444361129113891470232769 9333270846835418602674577)
                  ·
                    refine ⟨6999953135126563952005933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9333270846835418602674577 6999953135126563952005933)
                    ·
                      refine ⟨2624982425672461482002225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6999953135126563952005933 2624982425672461482002225)
                      ·
                        rfl

theorem cell23_5112135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_5112135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112135 prefixEnd_5112135 := by exact prefixLift 5112135
  have htrace : WordTrace (prefixWord ++ tailWord_5112135) baseStart_5112135 baseEnd_5112135 := by
    simpa [prefixWord, tailWord_5112135, baseEnd_5112135] using wordTrace_append hprefix tailTrace_5112135
  have hstable : (prefixWord ++ tailWord_5112135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112135).length < 2 ^ (prefixWord ++ tailWord_5112135).sum := by decide
  have hdescent : baseEnd_5112135 < baseStart_5112135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112199 : List Nat := [1, 1, 4, 2, 2, 1, 1, 6, 1, 1, 3]
def baseStart_5112199 : Nat := 118140960795 + 5112199 * 2 ^ 59
def prefixEnd_5112199 : Nat := 4983230072969 + 3 ^ 40 * 5112199 * 2
def baseEnd_5112199 : Nat := 2625015288434349231601931

theorem tailTrace_5112199 : CollatzResearch.WordTrace tailWord_5112199 prefixEnd_5112199 2625015288434349231601931 := by
  unfold tailWord_5112199
  simp only [CollatzResearch.WordTrace]
  refine ⟨186457215606383591923739651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124304810404255727949159767 186457215606383591923739651)
  ·
    refine ⟨279685823409575387885609477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186457215606383591923739651 279685823409575387885609477)
    ·
      refine ⟨52441091889295385228551777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279685823409575387885609477 52441091889295385228551777)
      ·
        refine ⟨39330818916971538921413833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52441091889295385228551777 39330818916971538921413833)
        ·
          refine ⟨29498114187728654191060375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39330818916971538921413833 29498114187728654191060375)
          ·
            refine ⟨44247171281592981286590563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29498114187728654191060375 44247171281592981286590563)
            ·
              refine ⟨66370756922389471929885845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44247171281592981286590563 66370756922389471929885845)
              ·
                refine ⟨3111129230737006496713399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66370756922389471929885845 3111129230737006496713399)
                ·
                  refine ⟨4666693846105509745070099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3111129230737006496713399 4666693846105509745070099)
                  ·
                    refine ⟨7000040769158264617605149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4666693846105509745070099 7000040769158264617605149)
                    ·
                      refine ⟨2625015288434349231601931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7000040769158264617605149 2625015288434349231601931)
                      ·
                        rfl

theorem cell23_5112199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_5112199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112199 prefixEnd_5112199 := by exact prefixLift 5112199
  have htrace : WordTrace (prefixWord ++ tailWord_5112199) baseStart_5112199 baseEnd_5112199 := by
    simpa [prefixWord, tailWord_5112199, baseEnd_5112199] using wordTrace_append hprefix tailTrace_5112199
  have hstable : (prefixWord ++ tailWord_5112199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112199).length < 2 ^ (prefixWord ++ tailWord_5112199).sum := by decide
  have hdescent : baseEnd_5112199 < baseStart_5112199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112215 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 1, 6]
def baseStart_5112215 : Nat := 118140960795 + 5112215 * 2 ^ 59
def prefixEnd_5112215 : Nat := 4983230072969 + 3 ^ 40 * 5112215 * 2
def baseEnd_5112215 : Nat := 875007834708273723000619

theorem tailTrace_5112215 : CollatzResearch.WordTrace tailWord_5112215 prefixEnd_5112215 875007834708273723000619 := by
  unfold tailWord_5112215
  simp only [CollatzResearch.WordTrace]
  refine ⟨186457799174325626656322099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124305199449550417770881399 186457799174325626656322099)
  ·
    refine ⟨279686698761488439984483149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186457799174325626656322099 279686698761488439984483149)
    ·
      refine ⟨104882512035558164994181181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279686698761488439984483149 104882512035558164994181181)
      ·
        refine ⟨39330942013334311872817943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104882512035558164994181181 39330942013334311872817943)
        ·
          refine ⟨58996413020001467809226915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39330942013334311872817943 58996413020001467809226915)
          ·
            refine ⟨88494619530002201713840373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58996413020001467809226915 88494619530002201713840373)
            ·
              refine ⟨8296370580937706410672535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88494619530002201713840373 8296370580937706410672535)
              ·
                refine ⟨12444555871406559616008803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8296370580937706410672535 12444555871406559616008803)
                ·
                  refine ⟨18666833807109839424013205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12444555871406559616008803 18666833807109839424013205)
                  ·
                    refine ⟨875007834708273723000619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18666833807109839424013205 875007834708273723000619)
                    ·
                      rfl

theorem cell23_5112215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_5112215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112215 prefixEnd_5112215 := by exact prefixLift 5112215
  have htrace : WordTrace (prefixWord ++ tailWord_5112215) baseStart_5112215 baseEnd_5112215 := by
    simpa [prefixWord, tailWord_5112215, baseEnd_5112215] using wordTrace_append hprefix tailTrace_5112215
  have hstable : (prefixWord ++ tailWord_5112215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112215).length < 2 ^ (prefixWord ++ tailWord_5112215).sum := by decide
  have hdescent : baseEnd_5112215 < baseStart_5112215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112242 : List Nat := [3, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_5112242 : Nat := 118140960795 + 5112242 * 2 ^ 59
def prefixEnd_5112242 : Nat := 4983230072969 + 3 ^ 40 * 5112242 * 2
def baseEnd_5112242 : Nat := 2625037368102492563364233

theorem tailTrace_5112242 : CollatzResearch.WordTrace tailWord_5112242 prefixEnd_5112242 2625037368102492563364233 := by
  unfold tailWord_5112242
  simp only [CollatzResearch.WordTrace]
  refine ⟨46614695986306952566888745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124305855963485206845036653 46614695986306952566888745)
  ·
    refine ⟨34961021989730214425166559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46614695986306952566888745 34961021989730214425166559)
    ·
      refine ⟨52441532984595321637749839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34961021989730214425166559 52441532984595321637749839)
      ·
        refine ⟨78662299476892982456624759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52441532984595321637749839 78662299476892982456624759)
        ·
          refine ⟨117993449215339473684937139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78662299476892982456624759 117993449215339473684937139)
          ·
            refine ⟨176990173823009210527405709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117993449215339473684937139 176990173823009210527405709)
            ·
              refine ⟨66371315183628453947777141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176990173823009210527405709 66371315183628453947777141)
              ·
                refine ⟨6222310798465167557604107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66371315183628453947777141 6222310798465167557604107)
                ·
                  refine ⟨9333466197697751336406161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6222310798465167557604107 9333466197697751336406161)
                  ·
                    refine ⟨7000099648273313502304621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9333466197697751336406161 7000099648273313502304621)
                    ·
                      refine ⟨2625037368102492563364233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7000099648273313502304621 2625037368102492563364233)
                      ·
                        rfl

theorem cell23_5112242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_5112242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112242 prefixEnd_5112242 := by exact prefixLift 5112242
  have htrace : WordTrace (prefixWord ++ tailWord_5112242) baseStart_5112242 baseEnd_5112242 := by
    simpa [prefixWord, tailWord_5112242, baseEnd_5112242] using wordTrace_append hprefix tailTrace_5112242
  have hstable : (prefixWord ++ tailWord_5112242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112242).length < 2 ^ (prefixWord ++ tailWord_5112242).sum := by decide
  have hdescent : baseEnd_5112242 < baseStart_5112242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112276 : List Nat := [2, 4, 1, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_5112276 : Nat := 118140960795 + 5112276 * 2 ^ 59
def prefixEnd_5112276 : Nat := 4983230072969 + 3 ^ 40 * 5112276 * 2
def baseEnd_5112276 : Nat := 2625054826444745430339077

theorem tailTrace_5112276 : CollatzResearch.WordTrace tailWord_5112276 prefixEnd_5112276 2625054826444745430339077 := by
  unfold tailWord_5112276
  simp only [CollatzResearch.WordTrace]
  refine ⟨93230012013552317037146341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124306682684736422716195121 93230012013552317037146341)
  ·
    refine ⟨17480627252541059444464939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93230012013552317037146341 17480627252541059444464939)
    ·
      refine ⟨26220940878811589166697409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17480627252541059444464939 26220940878811589166697409)
      ·
        refine ⟨19665705659108691875023057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26220940878811589166697409 19665705659108691875023057)
        ·
          refine ⟨14749279244331518906267293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19665705659108691875023057 14749279244331518906267293)
          ·
            refine ⟨5530979716624319589850235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14749279244331518906267293 5530979716624319589850235)
            ·
              refine ⟨8296469574936479384775353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5530979716624319589850235 8296469574936479384775353)
              ·
                refine ⟨6222352181202359538581515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8296469574936479384775353 6222352181202359538581515)
                ·
                  refine ⟨9333528271803539307872273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6222352181202359538581515 9333528271803539307872273)
                  ·
                    refine ⟨7000146203852654480904205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9333528271803539307872273 7000146203852654480904205)
                    ·
                      refine ⟨2625054826444745430339077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7000146203852654480904205 2625054826444745430339077)
                      ·
                        rfl

theorem cell23_5112276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_5112276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112276 prefixEnd_5112276 := by exact prefixLift 5112276
  have htrace : WordTrace (prefixWord ++ tailWord_5112276) baseStart_5112276 baseEnd_5112276 := by
    simpa [prefixWord, tailWord_5112276, baseEnd_5112276] using wordTrace_append hprefix tailTrace_5112276
  have hstable : (prefixWord ++ tailWord_5112276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112276).length < 2 ^ (prefixWord ++ tailWord_5112276).sum := by decide
  have hdescent : baseEnd_5112276 < baseStart_5112276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112305 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 2, 6]
def baseStart_5112305 : Nat := 118140960795 + 5112305 * 2 ^ 59
def prefixEnd_5112305 : Nat := 4983230072969 + 3 ^ 40 * 5112305 * 2
def baseEnd_5112305 : Nat := 875023239127908605625481

theorem tailTrace_5112305 : CollatzResearch.WordTrace tailWord_5112305 prefixEnd_5112305 875023239127908605625481 := by
  unfold tailWord_5112305
  simp only [CollatzResearch.WordTrace]
  refine ⟨186461081743999572027098369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124307387829333048018065579 186461081743999572027098369)
  ·
    refine ⟨139845811307999679020323777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186461081743999572027098369 139845811307999679020323777)
    ·
      refine ⟨104884358480999759265242833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139845811307999679020323777 104884358480999759265242833)
      ·
        refine ⟨78663268860749819448932125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104884358480999759265242833 78663268860749819448932125)
        ·
          refine ⟨29498725822781182293349547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78663268860749819448932125 29498725822781182293349547)
          ·
            refine ⟨44248088734171773440024321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29498725822781182293349547 44248088734171773440024321)
            ·
              refine ⟨33186066550628830080018241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44248088734171773440024321 33186066550628830080018241)
              ·
                refine ⟨24889549912971622560013681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33186066550628830080018241 24889549912971622560013681)
                ·
                  refine ⟨18667162434728716920010261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24889549912971622560013681 18667162434728716920010261)
                  ·
                    refine ⟨875023239127908605625481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18667162434728716920010261 875023239127908605625481)
                    ·
                      rfl

theorem cell23_5112305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_5112305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112305 prefixEnd_5112305 := by exact prefixLift 5112305
  have htrace : WordTrace (prefixWord ++ tailWord_5112305) baseStart_5112305 baseEnd_5112305 := by
    simpa [prefixWord, tailWord_5112305, baseEnd_5112305] using wordTrace_append hprefix tailTrace_5112305
  have hstable : (prefixWord ++ tailWord_5112305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112305).length < 2 ^ (prefixWord ++ tailWord_5112305).sum := by decide
  have hdescent : baseEnd_5112305 < baseStart_5112305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112312 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 3, 4, 2]
def baseStart_5112312 : Nat := 118140960795 + 5112312 * 2 ^ 59
def prefixEnd_5112312 : Nat := 4983230072969 + 3 ^ 40 * 5112312 * 2
def baseEnd_5112312 : Nat := 2625073311748307289488911

theorem tailTrace_5112312 : CollatzResearch.WordTrace tailWord_5112312 prefixEnd_5112312 2625073311748307289488911 := by
  unfold tailWord_5112312
  simp only [CollatzResearch.WordTrace]
  refine ⟨93230668527487106111301595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124307558036649474815068793 93230668527487106111301595)
  ·
    refine ⟨139846002791230659166952393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93230668527487106111301595 139846002791230659166952393)
    ·
      refine ⟨104884502093422994375214295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139846002791230659166952393 104884502093422994375214295)
      ·
        refine ⟨157326753140134491562821443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104884502093422994375214295 157326753140134491562821443)
        ·
          refine ⟨235990129710201737344232165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157326753140134491562821443 235990129710201737344232165)
          ·
            refine ⟨44248149320662825752043531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235990129710201737344232165 44248149320662825752043531)
            ·
              refine ⟨66372223980994238628065297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44248149320662825752043531 66372223980994238628065297)
              ·
                refine ⟨49779167985745678971048973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66372223980994238628065297 49779167985745678971048973)
                ·
                  refine ⟨18667187994654629614143365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49779167985745678971048973 18667187994654629614143365)
                  ·
                    refine ⟨3500097748997743052651881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18667187994654629614143365 3500097748997743052651881)
                    ·
                      refine ⟨2625073311748307289488911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3500097748997743052651881 2625073311748307289488911)
                      ·
                        rfl

theorem cell23_5112312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 4, 2].length) (baseStart_5112312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112312 prefixEnd_5112312 := by exact prefixLift 5112312
  have htrace : WordTrace (prefixWord ++ tailWord_5112312) baseStart_5112312 baseEnd_5112312 := by
    simpa [prefixWord, tailWord_5112312, baseEnd_5112312] using wordTrace_append hprefix tailTrace_5112312
  have hstable : (prefixWord ++ tailWord_5112312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112312).length < 2 ^ (prefixWord ++ tailWord_5112312).sum := by decide
  have hdescent : baseEnd_5112312 < baseStart_5112312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112325 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_5112325 : Nat := 118140960795 + 5112325 * 2 ^ 59
def prefixEnd_5112325 : Nat := 4983230072969 + 3 ^ 40 * 5112325 * 2
def baseEnd_5112325 : Nat := 2625079986996815738626351

theorem tailTrace_5112325 : CollatzResearch.WordTrace tailWord_5112325 prefixEnd_5112325 2625079986996815738626351 := by
  unfold tailWord_5112325
  simp only [CollatzResearch.WordTrace]
  refine ⟨186461811203927115442826429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124307874135951410295217619 186461811203927115442826429)
  ·
    refine ⟨69923179201472668291059911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186461811203927115442826429 69923179201472668291059911)
    ·
      refine ⟨104884768802209002436589867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69923179201472668291059911 104884768802209002436589867)
      ·
        refine ⟨157327153203313503654884801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104884768802209002436589867 157327153203313503654884801)
        ·
          refine ⟨117995364902485127741163601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157327153203313503654884801 117995364902485127741163601)
          ·
            refine ⟨88496523676863845805872701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117995364902485127741163601 88496523676863845805872701)
            ·
              refine ⟨33186196378823942177202263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88496523676863845805872701 33186196378823942177202263)
              ·
                refine ⟨49779294568235913265803395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33186196378823942177202263 49779294568235913265803395)
                ·
                  refine ⟨74668941852353869898705093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49779294568235913265803395 74668941852353869898705093)
                  ·
                    refine ⟨14000426597316350606007205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74668941852353869898705093 14000426597316350606007205)
                    ·
                      refine ⟨2625079986996815738626351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14000426597316350606007205 2625079986996815738626351)
                      ·
                        rfl

theorem cell23_5112325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_5112325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112325 prefixEnd_5112325 := by exact prefixLift 5112325
  have htrace : WordTrace (prefixWord ++ tailWord_5112325) baseStart_5112325 baseEnd_5112325 := by
    simpa [prefixWord, tailWord_5112325, baseEnd_5112325] using wordTrace_append hprefix tailTrace_5112325
  have hstable : (prefixWord ++ tailWord_5112325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112325).length < 2 ^ (prefixWord ++ tailWord_5112325).sum := by decide
  have hdescent : baseEnd_5112325 < baseStart_5112325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112333 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_5112333 : Nat := 118140960795 + 5112333 * 2 ^ 59
def prefixEnd_5112333 : Nat := 4983230072969 + 3 ^ 40 * 5112333 * 2
def baseEnd_5112333 : Nat := 2625084094842051707326315

theorem tailTrace_5112333 : CollatzResearch.WordTrace tailWord_5112333 prefixEnd_5112333 2625084094842051707326315 := by
  unfold tailWord_5112333
  simp only [CollatzResearch.WordTrace]
  refine ⟨186462102987898132809117653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124308068658598755206078435 186462102987898132809117653)
  ·
    refine ⟨4370205538778862487713695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 186462102987898132809117653 4370205538778862487713695)
    ·
      refine ⟨6555308308168293731570543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4370205538778862487713695 6555308308168293731570543)
      ·
        refine ⟨9832962462252440597355815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6555308308168293731570543 9832962462252440597355815)
        ·
          refine ⟨14749443693378660896033723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9832962462252440597355815 14749443693378660896033723)
          ·
            refine ⟨22124165540067991344050585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14749443693378660896033723 22124165540067991344050585)
            ·
              refine ⟨16593124155050993508037939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22124165540067991344050585 16593124155050993508037939)
              ·
                refine ⟨24889686232576490262056909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16593124155050993508037939 24889686232576490262056909)
                ·
                  refine ⟨9333632337216183848271341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24889686232576490262056909 9333632337216183848271341)
                  ·
                    refine ⟨3500112126456068943101753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9333632337216183848271341 3500112126456068943101753)
                    ·
                      refine ⟨2625084094842051707326315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3500112126456068943101753 2625084094842051707326315)
                      ·
                        rfl

theorem cell23_5112333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_5112333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112333 prefixEnd_5112333 := by exact prefixLift 5112333
  have htrace : WordTrace (prefixWord ++ tailWord_5112333) baseStart_5112333 baseEnd_5112333 := by
    simpa [prefixWord, tailWord_5112333, baseEnd_5112333] using wordTrace_append hprefix tailTrace_5112333
  have hstable : (prefixWord ++ tailWord_5112333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112333).length < 2 ^ (prefixWord ++ tailWord_5112333).sum := by decide
  have hdescent : baseEnd_5112333 < baseStart_5112333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112375 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_5112375 : Nat := 118140960795 + 5112375 * 2 ^ 59
def prefixEnd_5112375 : Nat := 4983230072969 + 3 ^ 40 * 5112375 * 2
def baseEnd_5112375 : Nat := 2625105661029540543001121

theorem tailTrace_5112375 : CollatzResearch.WordTrace tailWord_5112375 prefixEnd_5112375 2625105661029540543001121 := by
  unfold tailWord_5112375
  simp only [CollatzResearch.WordTrace]
  refine ⟨186463634853745973982146579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124309089902497315988097719 186463634853745973982146579)
  ·
    refine ⟨279695452280618960973219869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186463634853745973982146579 279695452280618960973219869)
    ·
      refine ⟨104885794605232110364957451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279695452280618960973219869 104885794605232110364957451)
      ·
        refine ⟨157328691907848165547436177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104885794605232110364957451 157328691907848165547436177)
        ·
          refine ⟨117996518930886124160577133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157328691907848165547436177 117996518930886124160577133)
          ·
            refine ⟨44248694599082296560216425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117996518930886124160577133 44248694599082296560216425)
            ·
              refine ⟨33186520949311722420162319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44248694599082296560216425 33186520949311722420162319)
              ·
                refine ⟨49779781423967583630243479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33186520949311722420162319 49779781423967583630243479)
                ·
                  refine ⟨74669672135951375445365219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49779781423967583630243479 74669672135951375445365219)
                  ·
                    refine ⟨112004508203927063168047829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74669672135951375445365219 112004508203927063168047829)
                    ·
                      refine ⟨2625105661029540543001121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112004508203927063168047829 2625105661029540543001121)
                      ·
                        rfl

theorem cell23_5112375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_5112375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112375 prefixEnd_5112375 := by exact prefixLift 5112375
  have htrace : WordTrace (prefixWord ++ tailWord_5112375) baseStart_5112375 baseEnd_5112375 := by
    simpa [prefixWord, tailWord_5112375, baseEnd_5112375] using wordTrace_append hprefix tailTrace_5112375
  have hstable : (prefixWord ++ tailWord_5112375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112375).length < 2 ^ (prefixWord ++ tailWord_5112375).sum := by decide
  have hdescent : baseEnd_5112375 < baseStart_5112375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112402 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_5112402 : Nat := 118140960795 + 5112402 * 2 ^ 59
def prefixEnd_5112402 : Nat := 4983230072969 + 3 ^ 40 * 5112402 * 2
def baseEnd_5112402 : Nat := 2625119525007211937363497

theorem tailTrace_5112402 : CollatzResearch.WordTrace tailWord_5112402 prefixEnd_5112402 2625119525007211937363497 := by
  unfold tailWord_5112402
  simp only [CollatzResearch.WordTrace]
  refine ⟨46616154906162039398344865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124309746416432105062252973 46616154906162039398344865)
  ·
    refine ⟨34962116179621529548758649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46616154906162039398344865 34962116179621529548758649)
    ·
      refine ⟨26221587134716147161568987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34962116179621529548758649 26221587134716147161568987)
      ·
        refine ⟨39332380702074220742353481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26221587134716147161568987 39332380702074220742353481)
        ·
          refine ⟨29499285526555665556765111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39332380702074220742353481 29499285526555665556765111)
          ·
            refine ⟨44248928289833498335147667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29499285526555665556765111 44248928289833498335147667)
            ·
              refine ⟨66373392434750247502721501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44248928289833498335147667 66373392434750247502721501)
              ·
                refine ⟨24890022163031342813520563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66373392434750247502721501 24890022163031342813520563)
                ·
                  refine ⟨37335033244547014220280845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24890022163031342813520563 37335033244547014220280845)
                  ·
                    refine ⟨14000637466705130332605317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37335033244547014220280845 14000637466705130332605317)
                    ·
                      refine ⟨2625119525007211937363497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14000637466705130332605317 2625119525007211937363497)
                      ·
                        rfl

theorem cell23_5112402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_5112402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112402 prefixEnd_5112402 := by exact prefixLift 5112402
  have htrace : WordTrace (prefixWord ++ tailWord_5112402) baseStart_5112402 baseEnd_5112402 := by
    simpa [prefixWord, tailWord_5112402, baseEnd_5112402] using wordTrace_append hprefix tailTrace_5112402
  have hstable : (prefixWord ++ tailWord_5112402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112402).length < 2 ^ (prefixWord ++ tailWord_5112402).sum := by decide
  have hdescent : baseEnd_5112402 < baseStart_5112402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112415 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 6]
def baseStart_5112415 : Nat := 118140960795 + 5112415 * 2 ^ 59
def prefixEnd_5112415 : Nat := 4983230072969 + 3 ^ 40 * 5112415 * 2
def baseEnd_5112415 : Nat := 2625126200255720386500937

theorem tailTrace_5112415 : CollatzResearch.WordTrace tailWord_5112415 prefixEnd_5112415 2625126200255720386500937 := by
  unfold tailWord_5112415
  simp only [CollatzResearch.WordTrace]
  refine ⟨186465093773601060813602699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124310062515734040542401799 186465093773601060813602699)
  ·
    refine ⟨279697640660401591220404049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186465093773601060813602699 279697640660401591220404049)
    ·
      refine ⟨209773230495301193415303037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279697640660401591220404049 209773230495301193415303037)
      ·
        refine ⟨78664961435737947530738639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209773230495301193415303037 78664961435737947530738639)
        ·
          refine ⟨117997442153606921296107959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78664961435737947530738639 117997442153606921296107959)
          ·
            refine ⟨176996163230410381944161939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117997442153606921296107959 176996163230410381944161939)
            ·
              refine ⟨265494244845615572916242909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176996163230410381944161939 265494244845615572916242909)
              ·
                refine ⟨99560341817105839843591091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265494244845615572916242909 99560341817105839843591091)
                ·
                  refine ⟨149340512725658759765386637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99560341817105839843591091 149340512725658759765386637)
                  ·
                    refine ⟨56002692272122034912019989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149340512725658759765386637 56002692272122034912019989)
                    ·
                      refine ⟨2625126200255720386500937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56002692272122034912019989 2625126200255720386500937)
                      ·
                        rfl

theorem cell23_5112415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_5112415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112415 prefixEnd_5112415 := by exact prefixLift 5112415
  have htrace : WordTrace (prefixWord ++ tailWord_5112415) baseStart_5112415 baseEnd_5112415 := by
    simpa [prefixWord, tailWord_5112415, baseEnd_5112415] using wordTrace_append hprefix tailTrace_5112415
  have hstable : (prefixWord ++ tailWord_5112415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112415).length < 2 ^ (prefixWord ++ tailWord_5112415).sum := by decide
  have hdescent : baseEnd_5112415 < baseStart_5112415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112450 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5112450 : Nat := 118140960795 + 5112450 * 2 ^ 59
def prefixEnd_5112450 : Nat := 4983230072969 + 3 ^ 40 * 5112450 * 2
def baseEnd_5112450 : Nat := 875048057359542583187759

theorem tailTrace_5112450 : CollatzResearch.WordTrace tailWord_5112450 prefixEnd_5112450 875048057359542583187759 := by
  unfold tailWord_5112450
  simp only [CollatzResearch.WordTrace]
  refine ⟨46616592582118565447781701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124310913552316174527417869 46616592582118565447781701)
  ·
    refine ⟨8740611109147231021459069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46616592582118565447781701 8740611109147231021459069)
    ·
      refine ⟨3277729165930211633047151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8740611109147231021459069 3277729165930211633047151)
      ·
        refine ⟨4916593748895317449570727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3277729165930211633047151 4916593748895317449570727)
        ·
          refine ⟨7374890623342976174356091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4916593748895317449570727 7374890623342976174356091)
          ·
            refine ⟨11062335935014464261534137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7374890623342976174356091 11062335935014464261534137)
            ·
              refine ⟨8296751951260848196150603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11062335935014464261534137 8296751951260848196150603)
              ·
                refine ⟨12445127926891272294225905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8296751951260848196150603 12445127926891272294225905)
                ·
                  refine ⟨9333845945168454220669429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12445127926891272294225905 9333845945168454220669429)
                  ·
                    refine ⟨875048057359542583187759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9333845945168454220669429 875048057359542583187759)
                    ·
                      rfl

theorem cell23_5112450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5112450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112450 prefixEnd_5112450 := by exact prefixLift 5112450
  have htrace : WordTrace (prefixWord ++ tailWord_5112450) baseStart_5112450 baseEnd_5112450 := by
    simpa [prefixWord, tailWord_5112450, baseEnd_5112450] using wordTrace_append hprefix tailTrace_5112450
  have hstable : (prefixWord ++ tailWord_5112450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112450).length < 2 ^ (prefixWord ++ tailWord_5112450).sum := by decide
  have hdescent : baseEnd_5112450 < baseStart_5112450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112480 : List Nat := [2, 1, 1, 4, 4, 2, 2, 2, 1, 4]
def baseStart_5112480 : Nat := 118140960795 + 5112480 * 2 ^ 59
def prefixEnd_5112480 : Nat := 4983230072969 + 3 ^ 40 * 5112480 * 2
def baseEnd_5112480 : Nat := 875053192166087544062713

theorem tailTrace_5112480 : CollatzResearch.WordTrace tailWord_5112480 prefixEnd_5112480 875053192166087544062713 := by
  unfold tailWord_5112480
  simp only [CollatzResearch.WordTrace]
  refine ⟨93233732259182788457359447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124311643012243717943145929 93233732259182788457359447)
  ·
    refine ⟨139850598388774182686039171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93233732259182788457359447 139850598388774182686039171)
    ·
      refine ⟨209775897583161274029058757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139850598388774182686039171 209775897583161274029058757)
      ·
        refine ⟨39332980796842738880448517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209775897583161274029058757 39332980796842738880448517)
        ·
          refine ⟨7374933899408013540084097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39332980796842738880448517 7374933899408013540084097)
          ·
            refine ⟨5531200424556010155063073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7374933899408013540084097 5531200424556010155063073)
            ·
              refine ⟨4148400318417007616297305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5531200424556010155063073 4148400318417007616297305)
              ·
                refine ⟨3111300238812755712222979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4148400318417007616297305 3111300238812755712222979)
                ·
                  refine ⟨4666950358219133568334469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3111300238812755712222979 4666950358219133568334469)
                  ·
                    refine ⟨875053192166087544062713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4666950358219133568334469 875053192166087544062713)
                    ·
                      rfl

theorem cell23_5112480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 1, 4].length) (baseStart_5112480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112480 prefixEnd_5112480 := by exact prefixLift 5112480
  have htrace : WordTrace (prefixWord ++ tailWord_5112480) baseStart_5112480 baseEnd_5112480 := by
    simpa [prefixWord, tailWord_5112480, baseEnd_5112480] using wordTrace_append hprefix tailTrace_5112480
  have hstable : (prefixWord ++ tailWord_5112480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112480).length < 2 ^ (prefixWord ++ tailWord_5112480).sum := by decide
  have hdescent : baseEnd_5112480 < baseStart_5112480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112509 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_5112509 : Nat := 118140960795 + 5112509 * 2 ^ 59
def prefixEnd_5112509 : Nat := 4983230072969 + 3 ^ 40 * 5112509 * 2
def baseEnd_5112509 : Nat := 2625174467437243018725505

theorem tailTrace_5112509 : CollatzResearch.WordTrace tailWord_5112509 prefixEnd_5112509 2625174467437243018725505 := by
  unfold tailWord_5112509
  simp only [CollatzResearch.WordTrace]
  refine ⟨186468522235260514867524581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124312348156840343245016387 186468522235260514867524581)
  ·
    refine ⟨34962847919111346537660859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186468522235260514867524581 34962847919111346537660859)
    ·
      refine ⟨52444271878667019806491289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34962847919111346537660859 52444271878667019806491289)
      ·
        refine ⟨39333203909000264854868467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52444271878667019806491289 39333203909000264854868467)
        ·
          refine ⟨58999805863500397282302701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39333203909000264854868467 58999805863500397282302701)
          ·
            refine ⟨22124927198812648980863513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58999805863500397282302701 22124927198812648980863513)
            ·
              refine ⟨16593695399109486735647635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22124927198812648980863513 16593695399109486735647635)
              ·
                refine ⟨24890543098664230103471453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16593695399109486735647635 24890543098664230103471453)
                ·
                  refine ⟨9333953661999086288801795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24890543098664230103471453 9333953661999086288801795)
                  ·
                    refine ⟨14000930492998629433202693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9333953661999086288801795 14000930492998629433202693)
                    ·
                      refine ⟨2625174467437243018725505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14000930492998629433202693 2625174467437243018725505)
                      ·
                        rfl

theorem cell23_5112509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_5112509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112509 prefixEnd_5112509 := by exact prefixLift 5112509
  have htrace : WordTrace (prefixWord ++ tailWord_5112509) baseStart_5112509 baseEnd_5112509 := by
    simpa [prefixWord, tailWord_5112509, baseEnd_5112509] using wordTrace_append hprefix tailTrace_5112509
  have hstable : (prefixWord ++ tailWord_5112509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112509).length < 2 ^ (prefixWord ++ tailWord_5112509).sum := by decide
  have hdescent : baseEnd_5112509 < baseStart_5112509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112526 : List Nat := [4, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_5112526 : Nat := 118140960795 + 5112526 * 2 ^ 59
def prefixEnd_5112526 : Nat := 4983230072969 + 3 ^ 40 * 5112526 * 2
def baseEnd_5112526 : Nat := 2625183196608369452212927

theorem tailTrace_5112526 : CollatzResearch.WordTrace tailWord_5112526 prefixEnd_5112526 2625183196608369452212927 := by
  unfold tailWord_5112526
  simp only [CollatzResearch.WordTrace]
  refine ⟨23308642784524865846361679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124312761517465951180595621 23308642784524865846361679)
  ·
    refine ⟨34962964176787298769542519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23308642784524865846361679 34962964176787298769542519)
    ·
      refine ⟨52444446265180948154313779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34962964176787298769542519 52444446265180948154313779)
      ·
        refine ⟨78666669397771422231470669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52444446265180948154313779 78666669397771422231470669)
        ·
          refine ⟨29500001024164283336801501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78666669397771422231470669 29500001024164283336801501)
          ·
            refine ⟨11062500384061606251300563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29500001024164283336801501 11062500384061606251300563)
            ·
              refine ⟨16593750576092409376950845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11062500384061606251300563 16593750576092409376950845)
              ·
                refine ⟨6222656466034653516356567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16593750576092409376950845 6222656466034653516356567)
                ·
                  refine ⟨9333984699051980274534851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6222656466034653516356567 9333984699051980274534851)
                  ·
                    refine ⟨14000977048577970411802277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9333984699051980274534851 14000977048577970411802277)
                    ·
                      refine ⟨2625183196608369452212927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14000977048577970411802277 2625183196608369452212927)
                      ·
                        rfl

theorem cell23_5112526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_5112526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112526 prefixEnd_5112526 := by exact prefixLift 5112526
  have htrace : WordTrace (prefixWord ++ tailWord_5112526) baseStart_5112526 baseEnd_5112526 := by
    simpa [prefixWord, tailWord_5112526, baseEnd_5112526] using wordTrace_append hprefix tailTrace_5112526
  have hstable : (prefixWord ++ tailWord_5112526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112526).length < 2 ^ (prefixWord ++ tailWord_5112526).sum := by decide
  have hdescent : baseEnd_5112526 < baseStart_5112526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112536 : List Nat := [2, 1, 2, 2, 3, 2, 3, 2, 2, 4]
def baseStart_5112536 : Nat := 118140960795 + 5112536 * 2 ^ 59
def prefixEnd_5112536 : Nat := 4983230072969 + 3 ^ 40 * 5112536 * 2
def baseEnd_5112536 : Nat := 875062777138304804362627

theorem tailTrace_5112536 : CollatzResearch.WordTrace tailWord_5112536 prefixEnd_5112536 875062777138304804362627 := by
  unfold tailWord_5112536
  simp only [CollatzResearch.WordTrace]
  refine ⟨93234753503081349239378731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124313004670775132319171641 93234753503081349239378731)
  ·
    refine ⟨139852130254622023859068097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93234753503081349239378731 139852130254622023859068097)
    ·
      refine ⟨104889097690966517894301073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139852130254622023859068097 104889097690966517894301073)
      ·
        refine ⟨78666823268224888420725805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104889097690966517894301073 78666823268224888420725805)
        ·
          refine ⟨29500058725584333157772177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78666823268224888420725805 29500058725584333157772177)
          ·
            refine ⟨22125044044188249868329133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29500058725584333157772177 22125044044188249868329133)
            ·
              refine ⟨8296891516570593700623425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22125044044188249868329133 8296891516570593700623425)
              ·
                refine ⟨6222668637427945275467569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8296891516570593700623425 6222668637427945275467569)
                ·
                  refine ⟨4667001478070958956600677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6222668637427945275467569 4667001478070958956600677)
                  ·
                    refine ⟨875062777138304804362627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4667001478070958956600677 875062777138304804362627)
                    ·
                      rfl

theorem cell23_5112536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_5112536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112536 prefixEnd_5112536 := by exact prefixLift 5112536
  have htrace : WordTrace (prefixWord ++ tailWord_5112536) baseStart_5112536 baseEnd_5112536 := by
    simpa [prefixWord, tailWord_5112536, baseEnd_5112536] using wordTrace_append hprefix tailTrace_5112536
  have hstable : (prefixWord ++ tailWord_5112536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112536).length < 2 ^ (prefixWord ++ tailWord_5112536).sum := by decide
  have hdescent : baseEnd_5112536 < baseStart_5112536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112543 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 3, 2, 2]
def baseStart_5112543 : Nat := 118140960795 + 5112543 * 2 ^ 59
def prefixEnd_5112543 : Nat := 4983230072969 + 3 ^ 40 * 5112543 * 2
def baseEnd_5112543 : Nat := 2625191925779495885700349

theorem tailTrace_5112543 : CollatzResearch.WordTrace tailWord_5112543 prefixEnd_5112543 2625191925779495885700349 := by
  unfold tailWord_5112543
  simp only [CollatzResearch.WordTrace]
  refine ⟨186469762317137338674262283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124313174878091559116174855 186469762317137338674262283)
  ·
    refine ⟨279704643475706008011393425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186469762317137338674262283 279704643475706008011393425)
    ·
      refine ⟨209778482606779506008545069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279704643475706008011393425 209778482606779506008545069)
      ·
        refine ⟨78666930977542314753204401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209778482606779506008545069 78666930977542314753204401)
        ·
          refine ⟨59000198233156736064903301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78666930977542314753204401 59000198233156736064903301)
          ·
            refine ⟨11062537168716888012169369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59000198233156736064903301 11062537168716888012169369)
            ·
              refine ⟨8296902876537666009127027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11062537168716888012169369 8296902876537666009127027)
              ·
                refine ⟨12445354314806499013690541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8296902876537666009127027 12445354314806499013690541)
                ·
                  refine ⟨4667007868052437130133953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12445354314806499013690541 4667007868052437130133953)
                  ·
                    refine ⟨3500255901039327847600465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4667007868052437130133953 3500255901039327847600465)
                    ·
                      refine ⟨2625191925779495885700349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3500255901039327847600465 2625191925779495885700349)
                      ·
                        rfl

theorem cell23_5112543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_5112543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112543 prefixEnd_5112543 := by exact prefixLift 5112543
  have htrace : WordTrace (prefixWord ++ tailWord_5112543) baseStart_5112543 baseEnd_5112543 := by
    simpa [prefixWord, tailWord_5112543, baseEnd_5112543] using wordTrace_append hprefix tailTrace_5112543
  have hstable : (prefixWord ++ tailWord_5112543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112543).length < 2 ^ (prefixWord ++ tailWord_5112543).sum := by decide
  have hdescent : baseEnd_5112543 < baseStart_5112543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112569 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 2, 7, 2]
def baseStart_5112569 : Nat := 118140960795 + 5112569 * 2 ^ 59
def prefixEnd_5112569 : Nat := 4983230072969 + 3 ^ 40 * 5112569 * 2
def baseEnd_5112569 : Nat := 2625205276276512783975229

theorem tailTrace_5112569 : CollatzResearch.WordTrace tailWord_5112569 prefixEnd_5112569 2625205276276512783975229 := by
  unfold tailWord_5112569
  simp only [CollatzResearch.WordTrace]
  refine ⟨186470710615043145114708761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124313807076695430076472507 186470710615043145114708761)
  ·
    refine ⟨139853032961282358836031571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186470710615043145114708761 139853032961282358836031571)
    ·
      refine ⟨209779549441923538254047357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139853032961282358836031571 209779549441923538254047357)
      ·
        refine ⟨78667331040721326845267759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209779549441923538254047357 78667331040721326845267759)
        ·
          refine ⟨118000996561081990267901639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78667331040721326845267759 118000996561081990267901639)
          ·
            refine ⟨177001494841622985401852459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118000996561081990267901639 177001494841622985401852459)
            ·
              refine ⟨265502242262434478102778689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177001494841622985401852459 265502242262434478102778689)
              ·
                refine ⟨199126681696825858577084017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265502242262434478102778689 199126681696825858577084017)
                ·
                  refine ⟨149345011272619393932813013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199126681696825858577084017 149345011272619393932813013)
                  ·
                    refine ⟨3500273701702017045300305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 149345011272619393932813013 3500273701702017045300305)
                    ·
                      refine ⟨2625205276276512783975229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3500273701702017045300305 2625205276276512783975229)
                      ·
                        rfl

theorem cell23_5112569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_5112569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112569 prefixEnd_5112569 := by exact prefixLift 5112569
  have htrace : WordTrace (prefixWord ++ tailWord_5112569) baseStart_5112569 baseEnd_5112569 := by
    simpa [prefixWord, tailWord_5112569, baseEnd_5112569] using wordTrace_append hprefix tailTrace_5112569
  have hstable : (prefixWord ++ tailWord_5112569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112569).length < 2 ^ (prefixWord ++ tailWord_5112569).sum := by decide
  have hdescent : baseEnd_5112569 < baseStart_5112569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112594 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_5112594 : Nat := 118140960795 + 5112594 * 2 ^ 59
def prefixEnd_5112594 : Nat := 4983230072969 + 3 ^ 40 * 5112594 * 2
def baseEnd_5112594 : Nat := 2625218113292875186162615

theorem tailTrace_5112594 : CollatzResearch.WordTrace tailWord_5112594 prefixEnd_5112594 2625218113292875186162615 := by
  unfold tailWord_5112594
  simp only [CollatzResearch.WordTrace]
  refine ⟨46617905609988143596092209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124314414959968382922912557 46617905609988143596092209)
  ·
    refine ⟨34963429207491107697069157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46617905609988143596092209 34963429207491107697069157)
    ·
      refine ⟨6555642976404582693200467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34963429207491107697069157 6555642976404582693200467)
      ·
        refine ⟨9833464464606874039800701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6555642976404582693200467 9833464464606874039800701)
        ·
          refine ⟨3687549174227577764925263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9833464464606874039800701 3687549174227577764925263)
          ·
            refine ⟨5531323761341366647387895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687549174227577764925263 5531323761341366647387895)
            ·
              refine ⟨8296985642012049971081843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5531323761341366647387895 8296985642012049971081843)
              ·
                refine ⟨12445478463018074956622765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8296985642012049971081843 12445478463018074956622765)
                ·
                  refine ⟨4667054423631778108733537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12445478463018074956622765 4667054423631778108733537)
                  ·
                    refine ⟨3500290817723833581550153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4667054423631778108733537 3500290817723833581550153)
                    ·
                      refine ⟨2625218113292875186162615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3500290817723833581550153 2625218113292875186162615)
                      ·
                        rfl

theorem cell23_5112594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_5112594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112594 prefixEnd_5112594 := by exact prefixLift 5112594
  have htrace : WordTrace (prefixWord ++ tailWord_5112594) baseStart_5112594 baseEnd_5112594 := by
    simpa [prefixWord, tailWord_5112594, baseEnd_5112594] using wordTrace_append hprefix tailTrace_5112594
  have hstable : (prefixWord ++ tailWord_5112594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112594).length < 2 ^ (prefixWord ++ tailWord_5112594).sum := by decide
  have hdescent : baseEnd_5112594 < baseStart_5112594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112610 : List Nat := [3, 3, 1, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_5112610 : Nat := 118140960795 + 5112610 * 2 ^ 59
def prefixEnd_5112610 : Nat := 4983230072969 + 3 ^ 40 * 5112610 * 2
def baseEnd_5112610 : Nat := 2625226328983347123562541

theorem tailTrace_5112610 : CollatzResearch.WordTrace tailWord_5112610 prefixEnd_5112610 2625226328983347123562541 := by
  unfold tailWord_5112610
  simp only [CollatzResearch.WordTrace]
  refine ⟨46618051501973652279237821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124314804005263072744634189 46618051501973652279237821)
  ·
    refine ⟨17481769313240119604714183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46618051501973652279237821 17481769313240119604714183)
    ·
      refine ⟨26222653969860179407071275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17481769313240119604714183 26222653969860179407071275)
      ·
        refine ⟨39333980954790269110606913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26222653969860179407071275 39333980954790269110606913)
        ·
          refine ⟨29500485716092701832955185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39333980954790269110606913 29500485716092701832955185)
          ·
            refine ⟨22125364287069526374716389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29500485716092701832955185 22125364287069526374716389)
            ·
              refine ⟨4148505803825536195259323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22125364287069526374716389 4148505803825536195259323)
              ·
                refine ⟨6222758705738304292888985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148505803825536195259323 6222758705738304292888985)
                ·
                  refine ⟨4667069029303728219666739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6222758705738304292888985 4667069029303728219666739)
                  ·
                    refine ⟨7000603543955592329500109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4667069029303728219666739 7000603543955592329500109)
                    ·
                      refine ⟨2625226328983347123562541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7000603543955592329500109 2625226328983347123562541)
                      ·
                        rfl

theorem cell23_5112610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_5112610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112610 prefixEnd_5112610 := by exact prefixLift 5112610
  have htrace : WordTrace (prefixWord ++ tailWord_5112610) baseStart_5112610 baseEnd_5112610 := by
    simpa [prefixWord, tailWord_5112610, baseEnd_5112610] using wordTrace_append hprefix tailTrace_5112610
  have hstable : (prefixWord ++ tailWord_5112610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112610).length < 2 ^ (prefixWord ++ tailWord_5112610).sum := by decide
  have hdescent : baseEnd_5112610 < baseStart_5112610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112637 : List Nat := [1, 4, 1, 4, 2, 1, 3, 1, 1, 3, 2]
def baseStart_5112637 : Nat := 118140960795 + 5112637 * 2 ^ 59
def prefixEnd_5112637 : Nat := 4983230072969 + 3 ^ 40 * 5112637 * 2
def baseEnd_5112637 : Nat := 2625240192961018517924917

theorem tailTrace_5112637 : CollatzResearch.WordTrace tailWord_5112637 prefixEnd_5112637 2625240192961018517924917 := by
  unfold tailWord_5112637
  simp only [CollatzResearch.WordTrace]
  refine ⟨186473190778796792728184165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124315460519197861818789443 186473190778796792728184165)
  ·
    refine ⟨34963723271024398636534531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186473190778796792728184165 34963723271024398636534531)
    ·
      refine ⟨52445584906536597954801797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34963723271024398636534531 52445584906536597954801797)
      ·
        refine ⟨9833547169975612116525337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52445584906536597954801797 9833547169975612116525337)
        ·
          refine ⟨7375160377481709087394003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9833547169975612116525337 7375160377481709087394003)
          ·
            refine ⟨11062740566222563631091005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7375160377481709087394003 11062740566222563631091005)
            ·
              refine ⟨4148527712333461361659127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11062740566222563631091005 4148527712333461361659127)
              ·
                refine ⟨6222791568500192042488691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148527712333461361659127 6222791568500192042488691)
                ·
                  refine ⟨9334187352750288063733037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6222791568500192042488691 9334187352750288063733037)
                  ·
                    refine ⟨3500320257281358023899889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9334187352750288063733037 3500320257281358023899889)
                    ·
                      refine ⟨2625240192961018517924917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3500320257281358023899889 2625240192961018517924917)
                      ·
                        rfl

theorem cell23_5112637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_5112637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112637 prefixEnd_5112637 := by exact prefixLift 5112637
  have htrace : WordTrace (prefixWord ++ tailWord_5112637) baseStart_5112637 baseEnd_5112637 := by
    simpa [prefixWord, tailWord_5112637, baseEnd_5112637] using wordTrace_append hprefix tailTrace_5112637
  have hstable : (prefixWord ++ tailWord_5112637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112637).length < 2 ^ (prefixWord ++ tailWord_5112637).sum := by decide
  have hdescent : baseEnd_5112637 < baseStart_5112637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112666 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3]
def baseStart_5112666 : Nat := 118140960795 + 5112666 * 2 ^ 59
def prefixEnd_5112666 : Nat := 4983230072969 + 3 ^ 40 * 5112666 * 2
def baseEnd_5112666 : Nat := 2625255083899998904462283

theorem tailTrace_5112666 : CollatzResearch.WordTrace tailWord_5112666 prefixEnd_5112666 2625255083899998904462283 := by
  unfold tailWord_5112666
  simp only [CollatzResearch.WordTrace]
  refine ⟨46618562123922932670247463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124316165663794487120659901 46618562123922932670247463)
  ·
    refine ⟨69927843185884399005371195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46618562123922932670247463 69927843185884399005371195)
    ·
      refine ⟨104891764778826598508056793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69927843185884399005371195 104891764778826598508056793)
      ·
        refine ⟨78668823584119948881042595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104891764778826598508056793 78668823584119948881042595)
        ·
          refine ⟨118003235376179923321563893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78668823584119948881042595 118003235376179923321563893)
          ·
            refine ⟨11062803316516867811396615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118003235376179923321563893 11062803316516867811396615)
            ·
              refine ⟨16594204974775301717094923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11062803316516867811396615 16594204974775301717094923)
              ·
                refine ⟨24891307462162952575642385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16594204974775301717094923 24891307462162952575642385)
                ·
                  refine ⟨18668480596622214431731789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24891307462162952575642385 18668480596622214431731789)
                  ·
                    refine ⟨7000680223733330411899421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18668480596622214431731789 7000680223733330411899421)
                    ·
                      refine ⟨2625255083899998904462283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7000680223733330411899421 2625255083899998904462283)
                      ·
                        rfl

theorem cell23_5112666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_5112666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112666 prefixEnd_5112666 := by exact prefixLift 5112666
  have htrace : WordTrace (prefixWord ++ tailWord_5112666) baseStart_5112666 baseEnd_5112666 := by
    simpa [prefixWord, tailWord_5112666, baseEnd_5112666] using wordTrace_append hprefix tailTrace_5112666
  have hstable : (prefixWord ++ tailWord_5112666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112666).length < 2 ^ (prefixWord ++ tailWord_5112666).sum := by decide
  have hdescent : baseEnd_5112666 < baseStart_5112666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112716 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 3, 4]
def baseStart_5112716 : Nat := 118140960795 + 5112716 * 2 ^ 59
def prefixEnd_5112716 : Nat := 4983230072969 + 3 ^ 40 * 5112716 * 2
def baseEnd_5112716 : Nat := 875093585977574569612351

theorem tailTrace_5112716 : CollatzResearch.WordTrace tailWord_5112716 prefixEnd_5112716 875093585977574569612351 := by
  unfold tailWord_5112716
  simp only [CollatzResearch.WordTrace]
  refine ⟨93238036072755294610155001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124317381430340392813540001 93238036072755294610155001)
  ·
    refine ⟨69928527054566470957616251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93238036072755294610155001 69928527054566470957616251)
    ·
      refine ⟨104892790581849706436424377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69928527054566470957616251 104892790581849706436424377)
      ·
        refine ⟨78669592936387279827318283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104892790581849706436424377 78669592936387279827318283)
        ·
          refine ⟨118004389404580919740977425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78669592936387279827318283 118004389404580919740977425)
          ·
            refine ⟨88503292053435689805733069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118004389404580919740977425 88503292053435689805733069)
            ·
              refine ⟨33188734520038383677149901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88503292053435689805733069 33188734520038383677149901)
              ·
                refine ⟨12445775445014393878931213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33188734520038383677149901 12445775445014393878931213)
                ·
                  refine ⟨4667165791880397704599205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12445775445014393878931213 4667165791880397704599205)
                  ·
                    refine ⟨875093585977574569612351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4667165791880397704599205 875093585977574569612351)
                    ·
                      rfl

theorem cell23_5112716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_5112716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112716 prefixEnd_5112716 := by exact prefixLift 5112716
  have htrace : WordTrace (prefixWord ++ tailWord_5112716) baseStart_5112716 baseEnd_5112716 := by
    simpa [prefixWord, tailWord_5112716, baseEnd_5112716] using wordTrace_append hprefix tailTrace_5112716
  have hstable : (prefixWord ++ tailWord_5112716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112716).length < 2 ^ (prefixWord ++ tailWord_5112716).sum := by decide
  have hdescent : baseEnd_5112716 < baseStart_5112716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112793 : List Nat := [1, 2, 1, 2, 5, 1, 3, 2, 1, 5]
def baseStart_5112793 : Nat := 118140960795 + 5112793 * 2 ^ 59
def prefixEnd_5112793 : Nat := 4983230072969 + 3 ^ 40 * 5112793 * 2
def baseEnd_5112793 : Nat := 875106765314373302524733

theorem tailTrace_5112793 : CollatzResearch.WordTrace tailWord_5112793 prefixEnd_5112793 875106765314373302524733 := by
  unfold tailWord_5112793
  simp only [CollatzResearch.WordTrace]
  refine ⟨186478880566231631370863033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124319253710821087580575355 186478880566231631370863033)
  ·
    refine ⟨139859160424673723528147275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186478880566231631370863033 139859160424673723528147275)
    ·
      refine ⟨209788740637010585292220913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139859160424673723528147275 209788740637010585292220913)
      ·
        refine ⟨157341555477757938969165685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209788740637010585292220913 157341555477757938969165685)
        ·
          refine ⟨14750770826039806778359283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157341555477757938969165685 14750770826039806778359283)
          ·
            refine ⟨22126156239059710167538925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14750770826039806778359283 22126156239059710167538925)
            ·
              refine ⟨8297308589647391312827097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22126156239059710167538925 8297308589647391312827097)
              ·
                refine ⟨6222981442235543484620323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8297308589647391312827097 6222981442235543484620323)
                ·
                  refine ⟨9334472163353315226930485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6222981442235543484620323 9334472163353315226930485)
                  ·
                    refine ⟨875106765314373302524733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9334472163353315226930485 875106765314373302524733)
                    ·
                      rfl

theorem cell23_5112793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 5].length) (baseStart_5112793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112793 prefixEnd_5112793 := by exact prefixLift 5112793
  have htrace : WordTrace (prefixWord ++ tailWord_5112793) baseStart_5112793 baseEnd_5112793 := by
    simpa [prefixWord, tailWord_5112793, baseEnd_5112793] using wordTrace_append hprefix tailTrace_5112793
  have hstable : (prefixWord ++ tailWord_5112793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112793).length < 2 ^ (prefixWord ++ tailWord_5112793).sum := by decide
  have hdescent : baseEnd_5112793 < baseStart_5112793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112809 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 6]
def baseStart_5112809 : Nat := 118140960795 + 5112809 * 2 ^ 59
def prefixEnd_5112809 : Nat := 4983230072969 + 3 ^ 40 * 5112809 * 2
def baseEnd_5112809 : Nat := 2625328511633591844974125

theorem tailTrace_5112809 : CollatzResearch.WordTrace tailWord_5112809 prefixEnd_5112809 2625328511633591844974125 := by
  unfold tailWord_5112809
  simp only [CollatzResearch.WordTrace]
  refine ⟨186479464134173666103445481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124319642756115777402296987 186479464134173666103445481)
  ·
    refine ⟨139859598100630249577584111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186479464134173666103445481 139859598100630249577584111)
    ·
      refine ⟨209789397150945374366376167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139859598100630249577584111 209789397150945374366376167)
      ·
        refine ⟨314684095726418061549564251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209789397150945374366376167 314684095726418061549564251)
        ·
          refine ⟨472026143589627092324346377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314684095726418061549564251 472026143589627092324346377)
          ·
            refine ⟨354019607692220319243259783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 472026143589627092324346377 354019607692220319243259783)
            ·
              refine ⟨531029411538330478864889675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354019607692220319243259783 531029411538330478864889675)
              ·
                refine ⟨796544117307495718297334513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531029411538330478864889675 796544117307495718297334513)
                ·
                  refine ⟨597408087980621788723000885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 796544117307495718297334513 597408087980621788723000885)
                  ·
                    refine ⟨56007008248183292692781333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 597408087980621788723000885 56007008248183292692781333)
                    ·
                      refine ⟨2625328511633591844974125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56007008248183292692781333 2625328511633591844974125)
                      ·
                        rfl

theorem cell23_5112809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_5112809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112809 prefixEnd_5112809 := by exact prefixLift 5112809
  have htrace : WordTrace (prefixWord ++ tailWord_5112809) baseStart_5112809 baseEnd_5112809 := by
    simpa [prefixWord, tailWord_5112809, baseEnd_5112809] using wordTrace_append hprefix tailTrace_5112809
  have hstable : (prefixWord ++ tailWord_5112809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112809).length < 2 ^ (prefixWord ++ tailWord_5112809).sum := by decide
  have hdescent : baseEnd_5112809 < baseStart_5112809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112810 : List Nat := [3, 1, 3, 1, 2, 3, 3, 1, 1, 5]
def baseStart_5112810 : Nat := 118140960795 + 5112810 * 2 ^ 59
def prefixEnd_5112810 : Nat := 4983230072969 + 3 ^ 40 * 5112810 * 2
def baseEnd_5112810 : Nat := 875109675038082113687207

theorem tailTrace_5112810 : CollatzResearch.WordTrace tailWord_5112810 prefixEnd_5112810 875109675038082113687207 := by
  unfold tailWord_5112810
  simp only [CollatzResearch.WordTrace]
  refine ⟨46619875151792510818557971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124319667071446695516154589 46619875151792510818557971)
  ·
    refine ⟨69929812727688766227836957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46619875151792510818557971 69929812727688766227836957)
    ·
      refine ⟨26223679772883287335438859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69929812727688766227836957 26223679772883287335438859)
      ·
        refine ⟨39335519659324931003158289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26223679772883287335438859 39335519659324931003158289)
        ·
          refine ⟨29501639744493698252368717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39335519659324931003158289 29501639744493698252368717)
          ·
            refine ⟨11063114904185136844638269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29501639744493698252368717 11063114904185136844638269)
            ·
              refine ⟨4148668089069426316739351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11063114904185136844638269 4148668089069426316739351)
              ·
                refine ⟨6223002133604139475109027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148668089069426316739351 6223002133604139475109027)
                ·
                  refine ⟨9334503200406209212663541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6223002133604139475109027 9334503200406209212663541)
                  ·
                    refine ⟨875109675038082113687207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9334503200406209212663541 875109675038082113687207)
                    ·
                      rfl

theorem cell23_5112810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_5112810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112810 prefixEnd_5112810 := by exact prefixLift 5112810
  have htrace : WordTrace (prefixWord ++ tailWord_5112810) baseStart_5112810 baseEnd_5112810 := by
    simpa [prefixWord, tailWord_5112810, baseEnd_5112810] using wordTrace_append hprefix tailTrace_5112810
  have hstable : (prefixWord ++ tailWord_5112810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112810).length < 2 ^ (prefixWord ++ tailWord_5112810).sum := by decide
  have hdescent : baseEnd_5112810 < baseStart_5112810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112833 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_5112833 : Nat := 118140960795 + 5112833 * 2 ^ 59
def prefixEnd_5112833 : Nat := 4983230072969 + 3 ^ 40 * 5112833 * 2
def baseEnd_5112833 : Nat := 2625340835169299751074015

theorem tailTrace_5112833 : CollatzResearch.WordTrace tailWord_5112833 prefixEnd_5112833 2625340835169299751074015 := by
  unfold tailWord_5112833
  simp only [CollatzResearch.WordTrace]
  refine ⟨186480339486086718202319153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124320226324057812134879435 186480339486086718202319153)
  ·
    refine ⟨139860254614565038651739365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186480339486086718202319153 139860254614565038651739365)
    ·
      refine ⟨26223797740230944747201131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139860254614565038651739365 26223797740230944747201131)
      ·
        refine ⟨39335696610346417120801697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26223797740230944747201131 39335696610346417120801697)
        ·
          refine ⟨29501772457759812840601273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39335696610346417120801697 29501772457759812840601273)
          ·
            refine ⟨22126329343319859630450955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29501772457759812840601273 22126329343319859630450955)
            ·
              refine ⟨33189494014979789445676433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22126329343319859630450955 33189494014979789445676433)
              ·
                refine ⟨24892120511234842084257325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33189494014979789445676433 24892120511234842084257325)
                ·
                  refine ⟨9334545191713065781596497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24892120511234842084257325 9334545191713065781596497)
                  ·
                    refine ⟨7000908893784799336197373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9334545191713065781596497 7000908893784799336197373)
                    ·
                      refine ⟨2625340835169299751074015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7000908893784799336197373 2625340835169299751074015)
                      ·
                        rfl

theorem cell23_5112833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_5112833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112833 prefixEnd_5112833 := by exact prefixLift 5112833
  have htrace : WordTrace (prefixWord ++ tailWord_5112833) baseStart_5112833 baseEnd_5112833 := by
    simpa [prefixWord, tailWord_5112833, baseEnd_5112833] using wordTrace_append hprefix tailTrace_5112833
  have hstable : (prefixWord ++ tailWord_5112833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112833).length < 2 ^ (prefixWord ++ tailWord_5112833).sum := by decide
  have hdescent : baseEnd_5112833 < baseStart_5112833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112843 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 4]
def baseStart_5112843 : Nat := 118140960795 + 5112843 * 2 ^ 59
def prefixEnd_5112843 : Nat := 4983230072969 + 3 ^ 40 * 5112843 * 2
def baseEnd_5112843 : Nat := 2625345969975844711948969

theorem tailTrace_5112843 : CollatzResearch.WordTrace tailWord_5112843 prefixEnd_5112843 2625345969975844711948969 := by
  unfold tailWord_5112843
  simp only [CollatzResearch.WordTrace]
  refine ⟨186480704216050489910183183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124320469477366993273455455 186480704216050489910183183)
  ·
    refine ⟨279721056324075734865274775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186480704216050489910183183 279721056324075734865274775)
    ·
      refine ⟨419581584486113602297912163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279721056324075734865274775 419581584486113602297912163)
      ·
        refine ⟨629372376729170403446868245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419581584486113602297912163 629372376729170403446868245)
        ·
          refine ⟨29501830159179862661571949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 629372376729170403446868245 29501830159179862661571949)
          ·
            refine ⟨11063186309692448498089481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29501830159179862661571949 11063186309692448498089481)
            ·
              refine ⟨8297389732269336373567111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11063186309692448498089481 8297389732269336373567111)
              ·
                refine ⟨12446084598404004560350667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8297389732269336373567111 12446084598404004560350667)
                ·
                  refine ⟨18669126897606006840526001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12446084598404004560350667 18669126897606006840526001)
                  ·
                    refine ⟨14001845173204505130394501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18669126897606006840526001 14001845173204505130394501)
                    ·
                      refine ⟨2625345969975844711948969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14001845173204505130394501 2625345969975844711948969)
                      ·
                        rfl

theorem cell23_5112843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 4].length) (baseStart_5112843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112843 prefixEnd_5112843 := by exact prefixLift 5112843
  have htrace : WordTrace (prefixWord ++ tailWord_5112843) baseStart_5112843 baseEnd_5112843 := by
    simpa [prefixWord, tailWord_5112843, baseEnd_5112843] using wordTrace_append hprefix tailTrace_5112843
  have hstable : (prefixWord ++ tailWord_5112843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112843).length < 2 ^ (prefixWord ++ tailWord_5112843).sum := by decide
  have hdescent : baseEnd_5112843 < baseStart_5112843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112853 : List Nat := [1, 3, 2, 1, 4, 2, 3, 7]
def baseStart_5112853 : Nat := 118140960795 + 5112853 * 2 ^ 59
def prefixEnd_5112853 : Nat := 4983230072969 + 3 ^ 40 * 5112853 * 2
def baseEnd_5112853 : Nat := 97235226103051469363849

theorem tailTrace_5112853 : CollatzResearch.WordTrace tailWord_5112853 prefixEnd_5112853 97235226103051469363849 := by
  unfold tailWord_5112853
  simp only [CollatzResearch.WordTrace]
  refine ⟨186481068946014261618047213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124320712630676174412031475 186481068946014261618047213)
  ·
    refine ⟨69930400854755348106767705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186481068946014261618047213 69930400854755348106767705)
    ·
      refine ⟨52447800641066511080075779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69930400854755348106767705 52447800641066511080075779)
      ·
        refine ⟨78671700961599766620113669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52447800641066511080075779 78671700961599766620113669)
        ·
          refine ⟨14750943930299956241271313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78671700961599766620113669 14750943930299956241271313)
          ·
            refine ⟨11063207947724967180953485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14750943930299956241271313 11063207947724967180953485)
            ·
              refine ⟨4148702980396862692857557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11063207947724967180953485 4148702980396862692857557)
              ·
                refine ⟨97235226103051469363849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4148702980396862692857557 97235226103051469363849)
                ·
                  rfl

theorem cell23_5112853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 7].length) (baseStart_5112853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112853 prefixEnd_5112853 := by exact prefixLift 5112853
  have htrace : WordTrace (prefixWord ++ tailWord_5112853) baseStart_5112853 baseEnd_5112853 := by
    simpa [prefixWord, tailWord_5112853, baseEnd_5112853] using wordTrace_append hprefix tailTrace_5112853
  have hstable : (prefixWord ++ tailWord_5112853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112853).length < 2 ^ (prefixWord ++ tailWord_5112853).sum := by decide
  have hdescent : baseEnd_5112853 < baseStart_5112853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112863 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 3]
def baseStart_5112863 : Nat := 118140960795 + 5112863 * 2 ^ 59
def prefixEnd_5112863 : Nat := 4983230072969 + 3 ^ 40 * 5112863 * 2
def baseEnd_5112863 : Nat := 2625356239588934633698877

theorem tailTrace_5112863 : CollatzResearch.WordTrace tailWord_5112863 prefixEnd_5112863 2625356239588934633698877 := by
  unfold tailWord_5112863
  simp only [CollatzResearch.WordTrace]
  refine ⟨186481433675978033325911243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124320955783985355550607495 186481433675978033325911243)
  ·
    refine ⟨279722150513967049988866865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186481433675978033325911243 279722150513967049988866865)
    ·
      refine ⟨209791612885475287491650149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279722150513967049988866865 209791612885475287491650149)
      ·
        refine ⟨39335927416026616404684403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209791612885475287491650149 39335927416026616404684403)
        ·
          refine ⟨59003891124039924607026605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39335927416026616404684403 59003891124039924607026605)
          ·
            refine ⟨22126459171514971727634977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59003891124039924607026605 22126459171514971727634977)
            ·
              refine ⟨16594844378636228795726233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22126459171514971727634977 16594844378636228795726233)
              ·
                refine ⟨12446133283977171596794675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16594844378636228795726233 12446133283977171596794675)
                ·
                  refine ⟨18669199925965757395192013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12446133283977171596794675 18669199925965757395192013)
                  ·
                    refine ⟨7000949972237159023197005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18669199925965757395192013 7000949972237159023197005)
                    ·
                      refine ⟨2625356239588934633698877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7000949972237159023197005 2625356239588934633698877)
                      ·
                        rfl

theorem cell23_5112863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_5112863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112863 prefixEnd_5112863 := by exact prefixLift 5112863
  have htrace : WordTrace (prefixWord ++ tailWord_5112863) baseStart_5112863 baseEnd_5112863 := by
    simpa [prefixWord, tailWord_5112863, baseEnd_5112863] using wordTrace_append hprefix tailTrace_5112863
  have hstable : (prefixWord ++ tailWord_5112863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112863).length < 2 ^ (prefixWord ++ tailWord_5112863).sum := by decide
  have hdescent : baseEnd_5112863 < baseStart_5112863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112864 : List Nat := [2, 1, 1, 7, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5112864 : Nat := 118140960795 + 5112864 * 2 ^ 59
def prefixEnd_5112864 : Nat := 4983230072969 + 3 ^ 40 * 5112864 * 2
def baseEnd_5112864 : Nat := 2625356753069589129786373

theorem tailTrace_5112864 : CollatzResearch.WordTrace tailWord_5112864 prefixEnd_5112864 2625356753069589129786373 := by
  unfold tailWord_5112864
  simp only [CollatzResearch.WordTrace]
  refine ⟨93240735074487205248348823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124320980099316273664465097 93240735074487205248348823)
  ·
    refine ⟨139861102611730807872523235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93240735074487205248348823 139861102611730807872523235)
    ·
      refine ⟨209791653917596211808784853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139861102611730807872523235 209791653917596211808784853)
      ·
        refine ⟨4916991888693661214268395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 209791653917596211808784853 4916991888693661214268395)
        ·
          refine ⟨7375487833040491821402593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4916991888693661214268395 7375487833040491821402593)
          ·
            refine ⟨5531615874780368866051945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7375487833040491821402593 5531615874780368866051945)
            ·
              refine ⟨4148711906085276649538959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5531615874780368866051945 4148711906085276649538959)
              ·
                refine ⟨6223067859127914974308439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148711906085276649538959 6223067859127914974308439)
                ·
                  refine ⟨9334601788691872461462659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6223067859127914974308439 9334601788691872461462659)
                  ·
                    refine ⟨14001902683037808692193989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9334601788691872461462659 14001902683037808692193989)
                    ·
                      refine ⟨2625356753069589129786373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14001902683037808692193989 2625356753069589129786373)
                      ·
                        rfl

theorem cell23_5112864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5112864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112864 prefixEnd_5112864 := by exact prefixLift 5112864
  have htrace : WordTrace (prefixWord ++ tailWord_5112864) baseStart_5112864 baseEnd_5112864 := by
    simpa [prefixWord, tailWord_5112864, baseEnd_5112864] using wordTrace_append hprefix tailTrace_5112864
  have hstable : (prefixWord ++ tailWord_5112864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112864).length < 2 ^ (prefixWord ++ tailWord_5112864).sum := by decide
  have hdescent : baseEnd_5112864 < baseStart_5112864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112867 : List Nat := [1, 1, 1, 4, 3, 4, 2, 1, 1, 2, 3]
def baseStart_5112867 : Nat := 118140960795 + 5112867 * 2 ^ 59
def prefixEnd_5112867 : Nat := 4983230072969 + 3 ^ 40 * 5112867 * 2
def baseEnd_5112867 : Nat := 2625358293511552618048859

theorem tailTrace_5112867 : CollatzResearch.WordTrace tailWord_5112867 prefixEnd_5112867 2625358293511552618048859 := by
  unfold tailWord_5112867
  simp only [CollatzResearch.WordTrace]
  refine ⟨186481579567963542009056855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124321053045309028006037903 186481579567963542009056855)
  ·
    refine ⟨279722369351945313013585283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186481579567963542009056855 279722369351945313013585283)
    ·
      refine ⟨419583554027917969520377925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279722369351945313013585283 419583554027917969520377925)
      ·
        refine ⟨78671916380234619285070861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 419583554027917969520377925 78671916380234619285070861)
        ·
          refine ⟨29501968642587982231901573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78671916380234619285070861 29501968642587982231901573)
          ·
            refine ⟨5531619120485246668481545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29501968642587982231901573 5531619120485246668481545)
            ·
              refine ⟨4148714340363935001361159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5531619120485246668481545 4148714340363935001361159)
              ·
                refine ⟨6223071510545902502041739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148714340363935001361159 6223071510545902502041739)
                ·
                  refine ⟨9334607265818853753062609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6223071510545902502041739 9334607265818853753062609)
                  ·
                    refine ⟨7000955449364140314796957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9334607265818853753062609 7000955449364140314796957)
                    ·
                      refine ⟨2625358293511552618048859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7000955449364140314796957 2625358293511552618048859)
                      ·
                        rfl

theorem cell23_5112867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_5112867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112867 prefixEnd_5112867 := by exact prefixLift 5112867
  have htrace : WordTrace (prefixWord ++ tailWord_5112867) baseStart_5112867 baseEnd_5112867 := by
    simpa [prefixWord, tailWord_5112867, baseEnd_5112867] using wordTrace_append hprefix tailTrace_5112867
  have hstable : (prefixWord ++ tailWord_5112867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112867).length < 2 ^ (prefixWord ++ tailWord_5112867).sum := by decide
  have hdescent : baseEnd_5112867 < baseStart_5112867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112874 : List Nat := [3, 1, 4, 1, 4, 1, 1, 2, 2, 4]
def baseStart_5112874 : Nat := 118140960795 + 5112874 * 2 ^ 59
def prefixEnd_5112874 : Nat := 4983230072969 + 3 ^ 40 * 5112874 * 2
def baseEnd_5112874 : Nat := 875120629292044696887109

theorem tailTrace_5112874 : CollatzResearch.WordTrace tailWord_5112874 prefixEnd_5112874 875120629292044696887109 := by
  unfold tailWord_5112874
  simp only [CollatzResearch.WordTrace]
  refine ⟨46620458719734545551140419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124321223252625454803041117 46620458719734545551140419)
  ·
    refine ⟨69930688079601818326710629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46620458719734545551140419 69930688079601818326710629)
    ·
      refine ⟨13112004014925340936258243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69930688079601818326710629 13112004014925340936258243)
      ·
        refine ⟨19668006022388011404387365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13112004014925340936258243 19668006022388011404387365)
        ·
          refine ⟨3687751129197752138322631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19668006022388011404387365 3687751129197752138322631)
          ·
            refine ⟨5531626693796628207483947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687751129197752138322631 5531626693796628207483947)
            ·
              refine ⟨8297440040694942311225921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5531626693796628207483947 8297440040694942311225921)
              ·
                refine ⟨6223080030521206733419441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8297440040694942311225921 6223080030521206733419441)
                ·
                  refine ⟨4667310022890905050064581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6223080030521206733419441 4667310022890905050064581)
                  ·
                    refine ⟨875120629292044696887109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4667310022890905050064581 875120629292044696887109)
                    ·
                      rfl

theorem cell23_5112874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_5112874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112874 prefixEnd_5112874 := by exact prefixLift 5112874
  have htrace : WordTrace (prefixWord ++ tailWord_5112874) baseStart_5112874 baseEnd_5112874 := by
    simpa [prefixWord, tailWord_5112874, baseEnd_5112874] using wordTrace_append hprefix tailTrace_5112874
  have hstable : (prefixWord ++ tailWord_5112874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112874).length < 2 ^ (prefixWord ++ tailWord_5112874).sum := by decide
  have hdescent : baseEnd_5112874 < baseStart_5112874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112896 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 2, 6]
def baseStart_5112896 : Nat := 118140960795 + 5112896 * 2 ^ 59
def prefixEnd_5112896 : Nat := 4983230072969 + 3 ^ 40 * 5112896 * 2
def baseEnd_5112896 : Nat := 875124394816844334862075

theorem tailTrace_5112896 : CollatzResearch.WordTrace tailWord_5112896 prefixEnd_5112896 875124394816844334862075 := by
  unfold tailWord_5112896
  simp only [CollatzResearch.WordTrace]
  refine ⟨93241318642429239980931271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124321758189905653307908361 93241318642429239980931271)
  ·
    refine ⟨139861977963643859971396907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93241318642429239980931271 139861977963643859971396907)
    ·
      refine ⟨209792966945465789957095361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139861977963643859971396907 209792966945465789957095361)
      ·
        refine ⟨157344725209099342467821521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209792966945465789957095361 157344725209099342467821521)
        ·
          refine ⟨118008543906824506850866141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157344725209099342467821521 118008543906824506850866141)
          ·
            refine ⟨44253203965059190069074803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118008543906824506850866141 44253203965059190069074803)
            ·
              refine ⟨66379805947588785103612205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44253203965059190069074803 66379805947588785103612205)
              ·
                refine ⟨24892427230345794413854577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66379805947588785103612205 24892427230345794413854577)
                ·
                  refine ⟨18669320422759345810390933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24892427230345794413854577 18669320422759345810390933)
                  ·
                    refine ⟨875124394816844334862075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18669320422759345810390933 875124394816844334862075)
                    ·
                      rfl

theorem cell23_5112896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_5112896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112896 prefixEnd_5112896 := by exact prefixLift 5112896
  have htrace : WordTrace (prefixWord ++ tailWord_5112896) baseStart_5112896 baseEnd_5112896 := by
    simpa [prefixWord, tailWord_5112896, baseEnd_5112896] using wordTrace_append hprefix tailTrace_5112896
  have hstable : (prefixWord ++ tailWord_5112896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112896).length < 2 ^ (prefixWord ++ tailWord_5112896).sum := by decide
  have hdescent : baseEnd_5112896 < baseStart_5112896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112897 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_5112897 : Nat := 118140960795 + 5112897 * 2 ^ 59
def prefixEnd_5112897 : Nat := 4983230072969 + 3 ^ 40 * 5112897 * 2
def baseEnd_5112897 : Nat := 2625373697931187500673721

theorem tailTrace_5112897 : CollatzResearch.WordTrace tailWord_5112897 prefixEnd_5112897 2625373697931187500673721 := by
  unfold tailWord_5112897
  simp only [CollatzResearch.WordTrace]
  refine ⟨186482673757854857132648945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124321782505236571421765963 186482673757854857132648945)
  ·
    refine ⟨139862005318391142849486709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186482673757854857132648945 139862005318391142849486709)
    ·
      refine ⟨13112062998599169642139379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139862005318391142849486709 13112062998599169642139379)
      ·
        refine ⟨19668094497898754463209069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13112062998599169642139379 19668094497898754463209069)
        ·
          refine ⟨7375535436712032923703401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19668094497898754463209069 7375535436712032923703401)
          ·
            refine ⟨5531651577534024692777551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7375535436712032923703401 5531651577534024692777551)
            ·
              refine ⟨8297477366301037039166327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5531651577534024692777551 8297477366301037039166327)
              ·
                refine ⟨12446216049451555558749491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8297477366301037039166327 12446216049451555558749491)
                ·
                  refine ⟨18669324074177333338124237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12446216049451555558749491 18669324074177333338124237)
                  ·
                    refine ⟨7000996527816500001796589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18669324074177333338124237 7000996527816500001796589)
                    ·
                      refine ⟨2625373697931187500673721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7000996527816500001796589 2625373697931187500673721)
                      ·
                        rfl

theorem cell23_5112897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_5112897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112897 prefixEnd_5112897 := by exact prefixLift 5112897
  have htrace : WordTrace (prefixWord ++ tailWord_5112897) baseStart_5112897 baseEnd_5112897 := by
    simpa [prefixWord, tailWord_5112897, baseEnd_5112897] using wordTrace_append hprefix tailTrace_5112897
  have hstable : (prefixWord ++ tailWord_5112897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112897).length < 2 ^ (prefixWord ++ tailWord_5112897).sum := by decide
  have hdescent : baseEnd_5112897 < baseStart_5112897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112920 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 6, 2, 2]
def baseStart_5112920 : Nat := 118140960795 + 5112920 * 2 ^ 59
def prefixEnd_5112920 : Nat := 4983230072969 + 3 ^ 40 * 5112920 * 2
def baseEnd_5112920 : Nat := 2625385507986240910686115

theorem tailTrace_5112920 : CollatzResearch.WordTrace tailWord_5112920 prefixEnd_5112920 2625385507986240910686115 := by
  unfold tailWord_5112920
  simp only [CollatzResearch.WordTrace]
  refine ⟨93241756318385766030368107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124322341757847688040490809 93241756318385766030368107)
  ·
    refine ⟨139862634477578649045552161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93241756318385766030368107 139862634477578649045552161)
    ·
      refine ⟨104896975858183986784164121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139862634477578649045552161 104896975858183986784164121)
      ·
        refine ⟨78672731893637990088123091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104896975858183986784164121 78672731893637990088123091)
        ·
          refine ⟨118009097840456985132184637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78672731893637990088123091 118009097840456985132184637)
          ·
            refine ⟨44253411690171369424569239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118009097840456985132184637 44253411690171369424569239)
            ·
              refine ⟨66380117535257054136853859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44253411690171369424569239 66380117535257054136853859)
              ·
                refine ⟨99570176302885581205280789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66380117535257054136853859 99570176302885581205280789)
                ·
                  refine ⟨4667352014197761618997537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99570176302885581205280789 4667352014197761618997537)
                  ·
                    refine ⟨3500514010648321214248153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4667352014197761618997537 3500514010648321214248153)
                    ·
                      refine ⟨2625385507986240910686115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3500514010648321214248153 2625385507986240910686115)
                      ·
                        rfl

theorem cell23_5112920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_5112920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112920 prefixEnd_5112920 := by exact prefixLift 5112920
  have htrace : WordTrace (prefixWord ++ tailWord_5112920) baseStart_5112920 baseEnd_5112920 := by
    simpa [prefixWord, tailWord_5112920, baseEnd_5112920] using wordTrace_append hprefix tailTrace_5112920
  have hstable : (prefixWord ++ tailWord_5112920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112920).length < 2 ^ (prefixWord ++ tailWord_5112920).sum := by decide
  have hdescent : baseEnd_5112920 < baseStart_5112920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5112983 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_5112983 : Nat := 118140960795 + 5112983 * 2 ^ 59
def prefixEnd_5112983 : Nat := 4983230072969 + 3 ^ 40 * 5112983 * 2
def baseEnd_5112983 : Nat := 2625417857267474164198325

theorem tailTrace_5112983 : CollatzResearch.WordTrace tailWord_5112983 prefixEnd_5112983 2625417857267474164198325 := by
  unfold tailWord_5112983
  simp only [CollatzResearch.WordTrace]
  refine ⟨186485810435543293820279603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124323873623695529213519735 186485810435543293820279603)
  ·
    refine ⟨279728715653314940730419405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186485810435543293820279603 279728715653314940730419405)
    ·
      refine ⟨104898268369993102773907277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279728715653314940730419405 104898268369993102773907277)
      ·
        refine ⟨39336850638747413540215229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104898268369993102773907277 39336850638747413540215229)
        ·
          refine ⟨14751318989530280077580711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39336850638747413540215229 14751318989530280077580711)
          ·
            refine ⟨22126978484295420116371067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14751318989530280077580711 22126978484295420116371067)
            ·
              refine ⟨33190467726443130174556601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22126978484295420116371067 33190467726443130174556601)
              ·
                refine ⟨24892850794832347630917451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33190467726443130174556601 24892850794832347630917451)
                ·
                  refine ⟨37339276192248521446376177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24892850794832347630917451 37339276192248521446376177)
                  ·
                    refine ⟨28004457144186391084782133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37339276192248521446376177 28004457144186391084782133)
                    ·
                      refine ⟨2625417857267474164198325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28004457144186391084782133 2625417857267474164198325)
                      ·
                        rfl

theorem cell23_5112983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_5112983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5112983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5112983 prefixEnd_5112983 := by exact prefixLift 5112983
  have htrace : WordTrace (prefixWord ++ tailWord_5112983) baseStart_5112983 baseEnd_5112983 := by
    simpa [prefixWord, tailWord_5112983, baseEnd_5112983] using wordTrace_append hprefix tailTrace_5112983
  have hstable : (prefixWord ++ tailWord_5112983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5112983).length < 2 ^ (prefixWord ++ tailWord_5112983).sum := by decide
  have hdescent : baseEnd_5112983 < baseStart_5112983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5112983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113010 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2]
def baseStart_5113010 : Nat := 118140960795 + 5113010 * 2 ^ 59
def prefixEnd_5113010 : Nat := 4983230072969 + 3 ^ 40 * 5113010 * 2
def baseEnd_5113010 : Nat := 2625431721245145558560701

theorem tailTrace_5113010 : CollatzResearch.WordTrace tailWord_5113010 prefixEnd_5113010 2625431721245145558560701 := by
  unfold tailWord_5113010
  simp only [CollatzResearch.WordTrace]
  refine ⟨46621698801611369357878121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124324530137630318287674989 46621698801611369357878121)
  ·
    refine ⟨34966274101208527018408591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46621698801611369357878121 34966274101208527018408591)
    ·
      refine ⟨52449411151812790527612887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34966274101208527018408591 52449411151812790527612887)
      ·
        refine ⟨78674116727719185791419331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52449411151812790527612887 78674116727719185791419331)
        ·
          refine ⟨118011175091578778687128997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78674116727719185791419331 118011175091578778687128997)
          ·
            refine ⟨22127095329671021003836687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118011175091578778687128997 22127095329671021003836687)
            ·
              refine ⟨33190642994506531505755031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22127095329671021003836687 33190642994506531505755031)
              ·
                refine ⟨49785964491759797258632547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33190642994506531505755031 49785964491759797258632547)
                ·
                  refine ⟨74678946737639695887948821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49785964491759797258632547 74678946737639695887948821)
                  ·
                    refine ⟨3500575628326860744747601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74678946737639695887948821 3500575628326860744747601)
                    ·
                      refine ⟨2625431721245145558560701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3500575628326860744747601 2625431721245145558560701)
                      ·
                        rfl

theorem cell23_5113010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_5113010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113010 prefixEnd_5113010 := by exact prefixLift 5113010
  have htrace : WordTrace (prefixWord ++ tailWord_5113010) baseStart_5113010 baseEnd_5113010 := by
    simpa [prefixWord, tailWord_5113010, baseEnd_5113010] using wordTrace_append hprefix tailTrace_5113010
  have hstable : (prefixWord ++ tailWord_5113010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113010).length < 2 ^ (prefixWord ++ tailWord_5113010).sum := by decide
  have hdescent : baseEnd_5113010 < baseStart_5113010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113020 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 5, 4]
def baseStart_5113020 : Nat := 118140960795 + 5113020 * 2 ^ 59
def prefixEnd_5113020 : Nat := 4983230072969 + 3 ^ 40 * 5113020 * 2
def baseEnd_5113020 : Nat := 875145618683896839811885

theorem tailTrace_5113020 : CollatzResearch.WordTrace tailWord_5113020 prefixEnd_5113020 875145618683896839811885 := by
  unfold tailWord_5113020
  simp only [CollatzResearch.WordTrace]
  refine ⟨93243579968204624569688257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124324773290939499426251009 93243579968204624569688257)
  ·
    refine ⟨69932684976153468427266193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93243579968204624569688257 69932684976153468427266193)
    ·
      refine ⟨52449513732115101320449645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69932684976153468427266193 52449513732115101320449645)
      ·
        refine ⟨19668567649543162995168617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52449513732115101320449645 19668567649543162995168617)
        ·
          refine ⟨14751425737157372246376463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19668567649543162995168617 14751425737157372246376463)
          ·
            refine ⟨22127138605736058369564695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14751425737157372246376463 22127138605736058369564695)
            ·
              refine ⟨33190707908604087554347043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22127138605736058369564695 33190707908604087554347043)
              ·
                refine ⟨49786061862906131331520565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33190707908604087554347043 49786061862906131331520565)
                ·
                  refine ⟨4667443299647449812330053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49786061862906131331520565 4667443299647449812330053)
                  ·
                    refine ⟨875145618683896839811885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4667443299647449812330053 875145618683896839811885)
                    ·
                      rfl

theorem cell23_5113020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_5113020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113020 prefixEnd_5113020 := by exact prefixLift 5113020
  have htrace : WordTrace (prefixWord ++ tailWord_5113020) baseStart_5113020 baseEnd_5113020 := by
    simpa [prefixWord, tailWord_5113020, baseEnd_5113020] using wordTrace_append hprefix tailTrace_5113020
  have hstable : (prefixWord ++ tailWord_5113020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113020).length < 2 ^ (prefixWord ++ tailWord_5113020).sum := by decide
  have hdescent : baseEnd_5113020 < baseStart_5113020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113093 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 3, 6]
def baseStart_5113093 : Nat := 118140960795 + 5113093 * 2 ^ 59
def prefixEnd_5113093 : Nat := 4983230072969 + 3 ^ 40 * 5113093 * 2
def baseEnd_5113093 : Nat := 875158113379822911274273

theorem tailTrace_5113093 : CollatzResearch.WordTrace tailWord_5113093 prefixEnd_5113093 875158113379822911274273 := by
  unfold tailWord_5113093
  simp only [CollatzResearch.WordTrace]
  refine ⟨186489822465144782606783933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124326548310096521737855955 186489822465144782606783933)
  ·
    refine ⟨69933683424429293477543975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186489822465144782606783933 69933683424429293477543975)
    ·
      refine ⟨104900525136643940216315963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69933683424429293477543975 104900525136643940216315963)
      ·
        refine ⟨157350787704965910324473945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104900525136643940216315963 157350787704965910324473945)
        ·
          refine ⟨118013090778724432743355459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157350787704965910324473945 118013090778724432743355459)
          ·
            refine ⟨177019636168086649115033189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118013090778724432743355459 177019636168086649115033189)
            ·
              refine ⟨33191181781516246709068723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177019636168086649115033189 33191181781516246709068723)
              ·
                refine ⟨49786772672274370063603085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33191181781516246709068723 49786772672274370063603085)
                ·
                  refine ⟨18670039752102888773851157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49786772672274370063603085 18670039752102888773851157)
                  ·
                    refine ⟨875158113379822911274273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18670039752102888773851157 875158113379822911274273)
                    ·
                      rfl

theorem cell23_5113093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_5113093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113093 prefixEnd_5113093 := by exact prefixLift 5113093
  have htrace : WordTrace (prefixWord ++ tailWord_5113093) baseStart_5113093 baseEnd_5113093 := by
    simpa [prefixWord, tailWord_5113093, baseEnd_5113093] using wordTrace_append hprefix tailTrace_5113093
  have hstable : (prefixWord ++ tailWord_5113093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113093).length < 2 ^ (prefixWord ++ tailWord_5113093).sum := by decide
  have hdescent : baseEnd_5113093 < baseStart_5113093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113111 : List Nat := [1, 1, 3, 4, 1, 1, 5, 2, 1, 1, 3]
def baseStart_5113111 : Nat := 118140960795 + 5113111 * 2 ^ 59
def prefixEnd_5113111 : Nat := 4983230072969 + 3 ^ 40 * 5113111 * 2
def baseEnd_5113111 : Nat := 2625483582791249663397737

theorem tailTrace_5113111 : CollatzResearch.WordTrace tailWord_5113111 prefixEnd_5113111 2625483582791249663397737 := by
  unfold tailWord_5113111
  simp only [CollatzResearch.WordTrace]
  refine ⟨186490478979079571680939187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124326985986053047787292791 186490478979079571680939187)
  ·
    refine ⟨279735718468619357521408781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186490478979079571680939187 279735718468619357521408781)
    ·
      refine ⟨104900894425732259070528293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279735718468619357521408781 104900894425732259070528293)
      ·
        refine ⟨19668917704824798575724055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104900894425732259070528293 19668917704824798575724055)
        ·
          refine ⟨29503376557237197863586083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19668917704824798575724055 29503376557237197863586083)
          ·
            refine ⟨44255064835855796795379125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29503376557237197863586083 44255064835855796795379125)
            ·
              refine ⟨4148912328361480949566793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44255064835855796795379125 4148912328361480949566793)
              ·
                refine ⟨3111684246271110712175095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4148912328361480949566793 3111684246271110712175095)
                ·
                  refine ⟨4667526369406666068262643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3111684246271110712175095 4667526369406666068262643)
                  ·
                    refine ⟨7001289554109999102393965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4667526369406666068262643 7001289554109999102393965)
                    ·
                      refine ⟨2625483582791249663397737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7001289554109999102393965 2625483582791249663397737)
                      ·
                        rfl

theorem cell23_5113111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_5113111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113111 prefixEnd_5113111 := by exact prefixLift 5113111
  have htrace : WordTrace (prefixWord ++ tailWord_5113111) baseStart_5113111 baseEnd_5113111 := by
    simpa [prefixWord, tailWord_5113111, baseEnd_5113111] using wordTrace_append hprefix tailTrace_5113111
  have hstable : (prefixWord ++ tailWord_5113111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113111).length < 2 ^ (prefixWord ++ tailWord_5113111).sum := by decide
  have hdescent : baseEnd_5113111 < baseStart_5113111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113118 : List Nat := [4, 3, 2, 1, 3, 1, 2, 1, 6]
def baseStart_5113118 : Nat := 118140960795 + 5113118 * 2 ^ 59
def prefixEnd_5113118 : Nat := 4983230072969 + 3 ^ 40 * 5113118 * 2
def baseEnd_5113118 : Nat := 291720797461759015112245

theorem tailTrace_5113118 : CollatzResearch.WordTrace tailWord_5113118 prefixEnd_5113118 291720797461759015112245 := by
  unfold tailWord_5113118
  simp only [CollatzResearch.WordTrace]
  refine ⟨23311341786256776484555501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124327156193369474584296005 23311341786256776484555501)
  ·
    refine ⟨8741753169846291181708313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23311341786256776484555501 8741753169846291181708313)
    ·
      refine ⟨6556314877384718386281235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8741753169846291181708313 6556314877384718386281235)
      ·
        refine ⟨9834472316077077579421853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6556314877384718386281235 9834472316077077579421853)
        ·
          refine ⟨3687927118528904092283195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9834472316077077579421853 3687927118528904092283195)
          ·
            refine ⟨5531890677793356138424793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687927118528904092283195 5531890677793356138424793)
            ·
              refine ⟨4148918008345017103818595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5531890677793356138424793 4148918008345017103818595)
              ·
                refine ⟨6223377012517525655727893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148918008345017103818595 6223377012517525655727893)
                ·
                  refine ⟨291720797461759015112245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6223377012517525655727893 291720797461759015112245)
                  ·
                    rfl

theorem cell23_5113118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_5113118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113118 prefixEnd_5113118 := by exact prefixLift 5113118
  have htrace : WordTrace (prefixWord ++ tailWord_5113118) baseStart_5113118 baseEnd_5113118 := by
    simpa [prefixWord, tailWord_5113118, baseEnd_5113118] using wordTrace_append hprefix tailTrace_5113118
  have hstable : (prefixWord ++ tailWord_5113118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113118).length < 2 ^ (prefixWord ++ tailWord_5113118).sum := by decide
  have hdescent : baseEnd_5113118 < baseStart_5113118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113123 : List Nat := [1, 1, 1, 4, 2, 3, 1, 10]
def baseStart_5113123 : Nat := 118140960795 + 5113123 * 2 ^ 59
def prefixEnd_5113123 : Nat := 4983230072969 + 3 ^ 40 * 5113123 * 2
def baseEnd_5113123 : Nat := 97240360909596430238803

theorem tailTrace_5113123 : CollatzResearch.WordTrace tailWord_5113123 prefixEnd_5113123 97240360909596430238803 := by
  unfold tailWord_5113123
  simp only [CollatzResearch.WordTrace]
  refine ⟨186490916655036097730376023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124327277770024065153584015 186490916655036097730376023)
  ·
    refine ⟨279736374982554146595564035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186490916655036097730376023 279736374982554146595564035)
    ·
      refine ⟨419604562473831219893346053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279736374982554146595564035 419604562473831219893346053)
      ·
        refine ⟨78675855463843353730002385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 419604562473831219893346053 78675855463843353730002385)
        ·
          refine ⟨59006891597882515297501789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78675855463843353730002385 59006891597882515297501789)
          ·
            refine ⟨22127584349205943236563171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59006891597882515297501789 22127584349205943236563171)
            ·
              refine ⟨33191376523808914854844757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22127584349205943236563171 33191376523808914854844757)
              ·
                refine ⟨97240360909596430238803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33191376523808914854844757 97240360909596430238803)
                ·
                  rfl

theorem cell23_5113123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 10].length) (baseStart_5113123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113123 prefixEnd_5113123 := by exact prefixLift 5113123
  have htrace : WordTrace (prefixWord ++ tailWord_5113123) baseStart_5113123 baseEnd_5113123 := by
    simpa [prefixWord, tailWord_5113123, baseEnd_5113123] using wordTrace_append hprefix tailTrace_5113123
  have hstable : (prefixWord ++ tailWord_5113123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113123).length < 2 ^ (prefixWord ++ tailWord_5113123).sum := by decide
  have hdescent : baseEnd_5113123 < baseStart_5113123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113137 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 3, 2, 3]
def baseStart_5113137 : Nat := 118140960795 + 5113137 * 2 ^ 59
def prefixEnd_5113137 : Nat := 4983230072969 + 3 ^ 40 * 5113137 * 2
def baseEnd_5113137 : Nat := 2625496933288266561672617

theorem tailTrace_5113137 : CollatzResearch.WordTrace tailWord_5113137 prefixEnd_5113137 2625496933288266561672617 := by
  unfold tailWord_5113137
  simp only [CollatzResearch.WordTrace]
  refine ⟨186491427276985378121385665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124327618184656918747590443 186491427276985378121385665)
  ·
    refine ⟨139868570457739033591039249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186491427276985378121385665 139868570457739033591039249)
    ·
      refine ⟨104901427843304275193279437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139868570457739033591039249 104901427843304275193279437)
      ·
        refine ⟨39338035441239103197479789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104901427843304275193279437 39338035441239103197479789)
        ·
          refine ⟨14751763290464663699054921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39338035441239103197479789 14751763290464663699054921)
          ·
            refine ⟨11063822467848497774291191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14751763290464663699054921 11063822467848497774291191)
            ·
              refine ⟨16595733701772746661436787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11063822467848497774291191 16595733701772746661436787)
              ·
                refine ⟨24893600552659119992155181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16595733701772746661436787 24893600552659119992155181)
                ·
                  refine ⟨9335100207247169997058193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24893600552659119992155181 9335100207247169997058193)
                  ·
                    refine ⟨7001325155435377497793645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9335100207247169997058193 7001325155435377497793645)
                    ·
                      refine ⟨2625496933288266561672617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7001325155435377497793645 2625496933288266561672617)
                      ·
                        rfl

theorem cell23_5113137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_5113137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113137 prefixEnd_5113137 := by exact prefixLift 5113137
  have htrace : WordTrace (prefixWord ++ tailWord_5113137) baseStart_5113137 baseEnd_5113137 := by
    simpa [prefixWord, tailWord_5113137, baseEnd_5113137] using wordTrace_append hprefix tailTrace_5113137
  have hstable : (prefixWord ++ tailWord_5113137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113137).length < 2 ^ (prefixWord ++ tailWord_5113137).sum := by decide
  have hdescent : baseEnd_5113137 < baseStart_5113137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113140 : List Nat := [2, 5, 1, 1, 1, 1, 1, 11]
def baseStart_5113140 : Nat := 118140960795 + 5113140 * 2 ^ 59
def prefixEnd_5113140 : Nat := 4983230072969 + 3 ^ 40 * 5113140 * 2
def baseEnd_5113140 : Nat := 97240684212230742590189

theorem tailTrace_5113140 : CollatzResearch.WordTrace tailWord_5113140 prefixEnd_5113140 97240684212230742590189 := by
  unfold tailWord_5113140
  simp only [CollatzResearch.WordTrace]
  refine ⟨93245768347987254816872437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124327691130649673089163249 93245768347987254816872437)
  ·
    refine ⟨8741790782623805139081791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93245768347987254816872437 8741790782623805139081791)
    ·
      refine ⟨13112686173935707708622687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8741790782623805139081791 13112686173935707708622687)
      ·
        refine ⟨19669029260903561562934031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13112686173935707708622687 19669029260903561562934031)
        ·
          refine ⟨29503543891355342344401047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19669029260903561562934031 29503543891355342344401047)
          ·
            refine ⟨44255315837033013516601571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29503543891355342344401047 44255315837033013516601571)
            ·
              refine ⟨66382973755549520274902357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44255315837033013516601571 66382973755549520274902357)
              ·
                refine ⟨97240684212230742590189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 66382973755549520274902357 97240684212230742590189)
                ·
                  rfl

theorem cell23_5113140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 11].length) (baseStart_5113140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113140 prefixEnd_5113140 := by exact prefixLift 5113140
  have htrace : WordTrace (prefixWord ++ tailWord_5113140) baseStart_5113140 baseEnd_5113140 := by
    simpa [prefixWord, tailWord_5113140, baseEnd_5113140] using wordTrace_append hprefix tailTrace_5113140
  have hstable : (prefixWord ++ tailWord_5113140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113140).length < 2 ^ (prefixWord ++ tailWord_5113140).sum := by decide
  have hdescent : baseEnd_5113140 < baseStart_5113140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113163 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 5]
def baseStart_5113163 : Nat := 118140960795 + 5113163 * 2 ^ 59
def prefixEnd_5113163 : Nat := 4983230072969 + 3 ^ 40 * 5113163 * 2
def baseEnd_5113163 : Nat := 2625510283785283459947497

theorem tailTrace_5113163 : CollatzResearch.WordTrace tailWord_5113163 prefixEnd_5113163 2625510283785283459947497 := by
  unfold tailWord_5113163
  simp only [CollatzResearch.WordTrace]
  refine ⟨186492375574891184561832143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124328250383260789707888095 186492375574891184561832143)
  ·
    refine ⟨279738563362336776842748215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186492375574891184561832143 279738563362336776842748215)
    ·
      refine ⟨419607845043505165264122323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279738563362336776842748215 419607845043505165264122323)
      ·
        refine ⟨629411767565257747896183485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419607845043505165264122323 629411767565257747896183485)
        ·
          refine ⟨236029412836971655461068807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 629411767565257747896183485 236029412836971655461068807)
          ·
            refine ⟨354044119255457483191603211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236029412836971655461068807 354044119255457483191603211)
            ·
              refine ⟨531066178883186224787404817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354044119255457483191603211 531066178883186224787404817)
              ·
                refine ⟨398299634162389668590553613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531066178883186224787404817 398299634162389668590553613)
                ·
                  refine ⟨149362362810896125721457605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398299634162389668590553613 149362362810896125721457605)
                  ·
                    refine ⟨28005443027043023572773301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149362362810896125721457605 28005443027043023572773301)
                    ·
                      refine ⟨2625510283785283459947497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28005443027043023572773301 2625510283785283459947497)
                      ·
                        rfl

theorem cell23_5113163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_5113163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113163 prefixEnd_5113163 := by exact prefixLift 5113163
  have htrace : WordTrace (prefixWord ++ tailWord_5113163) baseStart_5113163 baseEnd_5113163 := by
    simpa [prefixWord, tailWord_5113163, baseEnd_5113163] using wordTrace_append hprefix tailTrace_5113163
  have hstable : (prefixWord ++ tailWord_5113163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113163).length < 2 ^ (prefixWord ++ tailWord_5113163).sum := by decide
  have hdescent : baseEnd_5113163 < baseStart_5113163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113177 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 3, 3, 2]
def baseStart_5113177 : Nat := 118140960795 + 5113177 * 2 ^ 59
def prefixEnd_5113177 : Nat := 4983230072969 + 3 ^ 40 * 5113177 * 2
def baseEnd_5113177 : Nat := 2625517472514446405172433

theorem tailTrace_5113177 : CollatzResearch.WordTrace tailWord_5113177 prefixEnd_5113177 2625517472514446405172433 := by
  unfold tailWord_5113177
  simp only [CollatzResearch.WordTrace]
  refine ⟨186492886196840464952841785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124328590797893643301894523 186492886196840464952841785)
  ·
    refine ⟨139869664647630348714631339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186492886196840464952841785 139869664647630348714631339)
    ·
      refine ⟨209804496971445523071947009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139869664647630348714631339 209804496971445523071947009)
      ·
        refine ⟨157353372728584142303960257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209804496971445523071947009 157353372728584142303960257)
        ·
          refine ⟨118015029546438106727970193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157353372728584142303960257 118015029546438106727970193)
          ·
            refine ⟨88511272159828580045977645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118015029546438106727970193 88511272159828580045977645)
            ·
              refine ⟨33191727059935717517241617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88511272159828580045977645 33191727059935717517241617)
              ·
                refine ⟨24893795294951788137931213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33191727059935717517241617 24893795294951788137931213)
                ·
                  refine ⟨9335173235606920551724205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24893795294951788137931213 9335173235606920551724205)
                  ·
                    refine ⟨3500689963352595206896577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9335173235606920551724205 3500689963352595206896577)
                    ·
                      refine ⟨2625517472514446405172433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3500689963352595206896577 2625517472514446405172433)
                      ·
                        rfl

theorem cell23_5113177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 3, 2].length) (baseStart_5113177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113177 prefixEnd_5113177 := by exact prefixLift 5113177
  have htrace : WordTrace (prefixWord ++ tailWord_5113177) baseStart_5113177 baseEnd_5113177 := by
    simpa [prefixWord, tailWord_5113177, baseEnd_5113177] using wordTrace_append hprefix tailTrace_5113177
  have hstable : (prefixWord ++ tailWord_5113177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113177).length < 2 ^ (prefixWord ++ tailWord_5113177).sum := by decide
  have hdescent : baseEnd_5113177 < baseStart_5113177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113184 : List Nat := [2, 1, 1, 3, 4, 1, 2, 3, 2, 1, 3]
def baseStart_5113184 : Nat := 118140960795 + 5113184 * 2 ^ 59
def prefixEnd_5113184 : Nat := 4983230072969 + 3 ^ 40 * 5113184 * 2
def baseEnd_5113184 : Nat := 2625521066879027877784901

theorem tailTrace_5113184 : CollatzResearch.WordTrace tailWord_5113184 prefixEnd_5113184 2625521066879027877784901 := by
  unfold tailWord_5113184
  simp only [CollatzResearch.WordTrace]
  refine ⟨93246570753907552574173303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124328761005210070098897737 93246570753907552574173303)
  ·
    refine ⟨139869856130861328861259955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93246570753907552574173303 139869856130861328861259955)
    ·
      refine ⟨209804784196291993291889933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139869856130861328861259955 209804784196291993291889933)
      ·
        refine ⟨78676794073609497484458725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209804784196291993291889933 78676794073609497484458725)
        ·
          refine ⟨14751898888801780778336011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78676794073609497484458725 14751898888801780778336011)
          ·
            refine ⟨22127848333202671167504017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14751898888801780778336011 22127848333202671167504017)
            ·
              refine ⟨16595886249902003375628013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22127848333202671167504017 16595886249902003375628013)
              ·
                refine ⟨6223457343713251265860505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16595886249902003375628013 6223457343713251265860505)
                ·
                  refine ⟨4667593007784938449395379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6223457343713251265860505 4667593007784938449395379)
                  ·
                    refine ⟨7001389511677407674093069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4667593007784938449395379 7001389511677407674093069)
                    ·
                      refine ⟨2625521066879027877784901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7001389511677407674093069 2625521066879027877784901)
                      ·
                        rfl

theorem cell23_5113184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_5113184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113184 prefixEnd_5113184 := by exact prefixLift 5113184
  have htrace : WordTrace (prefixWord ++ tailWord_5113184) baseStart_5113184 baseEnd_5113184 := by
    simpa [prefixWord, tailWord_5113184, baseEnd_5113184] using wordTrace_append hprefix tailTrace_5113184
  have hstable : (prefixWord ++ tailWord_5113184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113184).length < 2 ^ (prefixWord ++ tailWord_5113184).sum := by decide
  have hdescent : baseEnd_5113184 < baseStart_5113184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113207 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 1, 4, 2]
def baseStart_5113207 : Nat := 118140960795 + 5113207 * 2 ^ 59
def prefixEnd_5113207 : Nat := 4983230072969 + 3 ^ 40 * 5113207 * 2
def baseEnd_5113207 : Nat := 2625532876934081287797295

theorem tailTrace_5113207 : CollatzResearch.WordTrace tailWord_5113207 prefixEnd_5113207 2625532876934081287797295 := by
  unfold tailWord_5113207
  simp only [CollatzResearch.WordTrace]
  refine ⟨186493980386731780076433875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124329320257821186717622583 186493980386731780076433875)
  ·
    refine ⟨279740970580097670114650813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186493980386731780076433875 279740970580097670114650813)
    ·
      refine ⟨104902863967536626292994055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279740970580097670114650813 104902863967536626292994055)
      ·
        refine ⟨157354295951304939439491083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104902863967536626292994055 157354295951304939439491083)
        ·
          refine ⟨236031443926957409159236625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157354295951304939439491083 236031443926957409159236625)
          ·
            refine ⟨177023582945218056869427469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236031443926957409159236625 177023582945218056869427469)
            ·
              refine ⟨66383843604456771326035301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177023582945218056869427469 66383843604456771326035301)
              ·
                refine ⟨12446970675835644623631619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66383843604456771326035301 12446970675835644623631619)
                ·
                  refine ⟨18670456013753466935447429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12446970675835644623631619 18670456013753466935447429)
                  ·
                    refine ⟨3500710502578775050396393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18670456013753466935447429 3500710502578775050396393)
                    ·
                      refine ⟨2625532876934081287797295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3500710502578775050396393 2625532876934081287797295)
                      ·
                        rfl

theorem cell23_5113207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 4, 2].length) (baseStart_5113207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113207 prefixEnd_5113207 := by exact prefixLift 5113207
  have htrace : WordTrace (prefixWord ++ tailWord_5113207) baseStart_5113207 baseEnd_5113207 := by
    simpa [prefixWord, tailWord_5113207, baseEnd_5113207] using wordTrace_append hprefix tailTrace_5113207
  have hstable : (prefixWord ++ tailWord_5113207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113207).length < 2 ^ (prefixWord ++ tailWord_5113207).sum := by decide
  have hdescent : baseEnd_5113207 < baseStart_5113207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113210 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3]
def baseStart_5113210 : Nat := 118140960795 + 5113210 * 2 ^ 59
def prefixEnd_5113210 : Nat := 4983230072969 + 3 ^ 40 * 5113210 * 2
def baseEnd_5113210 : Nat := 2625534417376044776059781

theorem tailTrace_5113210 : CollatzResearch.WordTrace tailWord_5113210 prefixEnd_5113210 2625534417376044776059781 := by
  unfold tailWord_5113210
  simp only [CollatzResearch.WordTrace]
  refine ⟨46623522451430227897198271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124329393203813941059195389 46623522451430227897198271)
  ·
    refine ⟨69935283677145341845797407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46623522451430227897198271 69935283677145341845797407)
    ·
      refine ⟨104902925515718012768696111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69935283677145341845797407 104902925515718012768696111)
      ·
        refine ⟨157354388273577019153044167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104902925515718012768696111 157354388273577019153044167)
        ·
          refine ⟨236031582410365528729566251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157354388273577019153044167 236031582410365528729566251)
          ·
            refine ⟨354047373615548293094349377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236031582410365528729566251 354047373615548293094349377)
            ·
              refine ⟨265535530211661219820762033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354047373615548293094349377 265535530211661219820762033)
              ·
                refine ⟨199151647658745914865571525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265535530211661219820762033 199151647658745914865571525)
                ·
                  refine ⟨37340933936014859037294661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199151647658745914865571525 37340933936014859037294661)
                  ·
                    refine ⟨7001425113002786069492749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37340933936014859037294661 7001425113002786069492749)
                    ·
                      refine ⟨2625534417376044776059781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7001425113002786069492749 2625534417376044776059781)
                      ·
                        rfl

theorem cell23_5113210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_5113210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113210 prefixEnd_5113210 := by exact prefixLift 5113210
  have htrace : WordTrace (prefixWord ++ tailWord_5113210) baseStart_5113210 baseEnd_5113210 := by
    simpa [prefixWord, tailWord_5113210, baseEnd_5113210] using wordTrace_append hprefix tailTrace_5113210
  have hstable : (prefixWord ++ tailWord_5113210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113210).length < 2 ^ (prefixWord ++ tailWord_5113210).sum := by decide
  have hdescent : baseEnd_5113210 < baseStart_5113210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
